/*
 * KATER -- Automating Weak Memory Model Metatheory
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-3.0.html.
 */

#include "GenMCPrinter.hpp"

#include "Config.hpp"
#include "KatModule.hpp"
#include "NFAUtils.hpp"
#include "RegExpUtils.hpp"
#include "Utils.hpp"

#include <fstream>

using namespace std::literals;

std::unordered_map<Relation::ID, const LetStatement *> GenMCPrinter::mutRecRelToLetMap;
std::unordered_map<const LetStatement *, unsigned> GenMCPrinter::letToIdxMap;

const static char *genmcCopyright =
	R"(/*
 * GenMC -- Generic Model Checking.
 *
 * This project is dual-licensed under the Apache License 2.0 and the MIT License.
 * You may choose to use, distribute, or modify this software under either license.
 *
 * Apache License 2.0:
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * MIT License:
 *     https://opensource.org/licenses/MIT
 */
)";

const static char *katerNotice =
	R"(/*******************************************************************************
 * CAUTION: This file is generated automatically by Kater -- DO NOT EDIT.
 *******************************************************************************/
)";

const static char *coherenceFuns =
	R"(
static auto isWriteRfBefore(const WriteLabel *wLab, const EventLabel *lab) -> bool
{
	auto &before = lab->view(#HB#);
	return before.contains(wLab->getPos()) ||
	       std::ranges::any_of(wLab->readers(),
				   [&](auto &rLab) { return before.contains(rLab.getPos()); });
}

static auto isHbOptRfBefore(const EventLabel *lab, const WriteLabel *wLab) -> bool
{
	return wLab->view(#HB#).contains(lab->getPos()) ||
	       std::ranges::any_of(wLab->readers(), [&](auto &rLab) {
		       return rLab.view(#HB#).contains(lab->getPos());
	       });
}

static auto splitLocMOBefore(SAddr addr, EventLabel *lab) -> ExecutionGraph::co_iterator
{
	auto &g = *lab->getParent();
	auto rit = std::find_if(g.co_rbegin(addr), g.co_rend(addr),
				[&](auto &oLab) { return isWriteRfBefore(&oLab, lab); });
	/* Convert to forward iterator, but be _really_ careful */
	return (rit == g.co_rend(addr)) ? g.co_begin(addr) : ++ExecutionGraph::co_iterator(*rit);
}

static auto splitLocMOAfterHb(ReadLabel *rLab) -> ExecutionGraph::co_iterator
{
	auto &g = *rLab->getParent();
	if (std::any_of(g.init_rf_begin(rLab->getAddr()), g.init_rf_end(rLab->getAddr()),
			[rLab](auto &rfLab) { return rfLab.view(#HB#).contains(rLab->getPos()); }))
		return g.co_begin(rLab->getAddr());

	auto it = std::find_if(g.co_begin(rLab->getAddr()), g.co_end(rLab->getAddr()),
			       [&](auto &wLab) { return isHbOptRfBefore(rLab, &wLab); });
	if (it == g.co_end(rLab->getAddr()) || it->view(#HB#).contains(rLab->getPos()))
		return it;
	return ++it;
}

static auto splitLocMOAfter(WriteLabel *wLab) -> ExecutionGraph::co_iterator
{
	auto &g = *wLab->getParent();
	return std::find_if(g.co_begin(wLab->getAddr()), g.co_end(wLab->getAddr()),
			    [&](auto &sLab) { return isHbOptRfBefore(wLab, &sLab); });
}

auto #CLASS#::getCoherentStores(ReadLabel *rLab) -> std::vector<EventLabel *>
{
	auto &g = *rLab->getParent();
	std::vector<EventLabel *> stores;

	/* Fastpath: co_max(G) is po-before R */
	auto *comaxLab = g.co_max(rLab->getAddr());
	if (comaxLab->getThread() == rLab->getThread() && comaxLab->getIndex() < rLab->getIndex())
		return {comaxLab};

	/*
	 * If there are no stores (rf?;hb)-before the current event
	 * then we can read read from all concurrent stores and the
	 * initializer store. Otherwise, we can read from all concurrent
	 * stores and the mo-latest of the (rf?;hb)-before stores.
	 */
	auto begIt = splitLocMOBefore(rLab->getAddr(), rLab);
	if (begIt == g.co_begin(rLab->getAddr()))
		stores.push_back(g.getInitLabel());
	else {
		stores.push_back(&*(--begIt));
		++begIt;
	}

	/*
	 * If the model supports out-of-order execution we have to also
	 * account for the possibility the read is hb-before some other
	 * store, or some read that reads from a store.
	 */
	auto endIt = (isDepTracking()) ? splitLocMOAfterHb(rLab) : g.co_end(rLab->getAddr());
	std::transform(begIt, endIt, std::back_inserter(stores), [&](auto &lab){
		return &lab;
	});
	return stores;
}

static auto getMOOptRfAfter(WriteLabel *sLab) -> std::vector<EventLabel *>
{
	auto &g = *sLab->getParent();
	std::vector<EventLabel *> after;
	std::vector<ReadLabel *> rfAfter;

	std::for_each(g.co_succ_begin(sLab), g.co_succ_end(sLab), [&](auto &wLab) {
		after.push_back(&wLab);
		std::transform(wLab.readers_begin(), wLab.readers_end(),
			       std::back_inserter(rfAfter), [&](auto &rLab) { return &rLab; });
	});
	std::transform(rfAfter.begin(), rfAfter.end(), std::back_inserter(after),
		       [](auto *rLab) { return rLab; });
	return after;
}

static auto getMOInvOptRfAfter(WriteLabel *sLab) -> std::vector<EventLabel *>
{
	auto &g = *sLab->getParent();
	std::vector<EventLabel *> after;
	std::vector<ReadLabel *> rfAfter;

	/* First, add (mo;rf?)-before */
	std::for_each(g.co_pred_begin(sLab), g.co_pred_end(sLab), [&](auto &wLab) {
		after.push_back(&wLab);
		std::transform(wLab.readers_begin(), wLab.readers_end(),
			       std::back_inserter(rfAfter), [&](auto &rLab) { return &rLab; });
	});
	std::transform(rfAfter.begin(), rfAfter.end(), std::back_inserter(after),
		       [](auto *rLab) { return rLab; });

	/* Then, we add the reader list for the initializer */
	std::for_each(g.init_rf_begin(sLab->getAddr()), g.init_rf_end(sLab->getAddr()),
		      [&](auto &rLab) { after.insert(after.end(), &rLab); });
	return after;
}

static auto getRevisitableFrom(WriteLabel *sLab, const VectorClock &pporf, WriteLabel *coPred)
	-> std::vector<ReadLabel *>
{
	auto &g = *sLab->getParent();
	const auto *confLab = findPendingRMW(sLab);
	std::vector<ReadLabel *> loads;

	for (auto &rLab : coPred->readers()) {
		if (!pporf.contains(rLab.getPos()) && rLab.getAddr() == sLab->getAddr() &&
		    rLab.isRevisitable() && rLab.wasAddedMax())
			loads.push_back(&rLab);
	}
	if (confLab)
		loads.erase(std::remove_if(loads.begin(), loads.end(),
					   [&](auto &eLab) {
						   return eLab->getStamp() > confLab->getStamp();
					   }),
			    loads.end());
	return loads;
}

void #CLASS#::filterCoherentRevisits(WriteLabel *sLab, std::vector<ReadLabel *> &ls)
{
	/* If this store is po- and mo-maximal then we are done */
	auto &g = *sLab->getParent();
	if (!isDepTracking() && sLab == g.co_max(sLab->getAddr()))
		return;

	/* First, we have to exclude (mo;rf?;hb?;sb)-after reads */
	auto optRfs = getMOOptRfAfter(sLab);
	ls.erase(std::remove_if(ls.begin(), ls.end(),
				[&](auto &eLab) {
					auto &before = g.po_imm_pred(eLab)->view(#HB#); // hb;sb
					return std::any_of(
						optRfs.begin(), optRfs.end(), [&](auto &evLab) {
							return before.contains(evLab->getPos());
						});
				}),
		 ls.end());

	/* If out-of-order event addition is not supported, then we are done
	 * due to po-maximality */
	if (!isDepTracking())
		return;

	/* Otherwise, we also have to exclude hb-before loads */
	ls.erase(std::remove_if(ls.begin(), ls.end(),
				[&](auto &eLab) { return sLab->view(#HB#).contains(eLab->getPos()); }),
		 ls.end());

	/* ...and also exclude (mo^-1; rf?; (hb^-1)?; sb^-1)-after reads in the *resulting* graph */
	auto &before = sLab->getPrefixView();
	auto moInvOptRfs = getMOInvOptRfAfter(sLab);
	ls.erase(std::remove_if(
			 ls.begin(), ls.end(),
			 [&](auto &eLab) {
				 auto v = g.getViewFromStamp(eLab->getStamp());
				 v->update(before);
				 return std::any_of(
					 moInvOptRfs.begin(), moInvOptRfs.end(), [&](auto &evLab) {
						 return v->contains(evLab->getPos()) && // stays in graph?
							g.po_imm_pred(evLab)->view(#HB#).contains(eLab->getPos()); // po-pred to check evLab != rLab
					 });
			 }),
		 ls.end());
}

auto #CLASS#::getCoherentPlacings(WriteLabel *wLab)
	-> std::vector<EventLabel *>
{
	auto &g = *wLab->getParent();
	std::vector<EventLabel *> result;

	/* If it is an RMW store, there is only one possible position in MO */
	if (wLab->isRMW()) {
		auto *rLab = genmc::dyn_cast<ReadLabel>(g.po_imm_pred(wLab));
		BUG_ON(!rLab);
		auto *rfLab = rLab->getRf();
		BUG_ON(!rfLab);
		result.push_back(rfLab);
		return result;
	}

	/* Otherwise, we calculate the full range and add the store */
	auto rangeBegin = splitLocMOBefore(wLab->getAddr(), wLab);
	auto rangeEnd = (isDepTracking()) ? splitLocMOAfter(wLab) : g.co_end(wLab->getAddr());
	auto cos = std::ranges::subrange(rangeBegin, rangeEnd) |
		   std::views::filter([&](auto &sLab) { return !sLab.isRMW(); }) |
		   std::views::transform([&](auto &sLab) {
			   auto *pLab = g.co_imm_pred(&sLab);
			   return pLab ? (EventLabel *)pLab : (EventLabel *)g.getInitLabel();
		   });
	std::ranges::copy(cos, std::back_inserter(result));
	result.push_back(rangeEnd == g.co_end(wLab->getAddr())
				 ? g.co_max(wLab->getAddr())
				 : (!g.co_imm_pred(&*rangeEnd)
					    ? (EventLabel *)g.getInitLabel()
					    : (EventLabel *)g.co_imm_pred(&*rangeEnd)));
	return result;
})";

struct DFSParameters {
	using State = NFA::State;
	using PrinterT = std::function<std::string(const std::string &)>;

	std::string name;				     // name of printed routine
	std::string status;				     // name of status arrays
	std::string params;				     // parameters of routine
	std::string savedParam;				     // saved param of label printing
	PrinterT createParams;				     // params of recursive calls
	PrinterT atBegin{[&](auto &s) { return ""; }};	     // at node discovery
	PrinterT atTreeE{[&](auto &s) { return ""; }};	     // at forward edge discovery
	PrinterT atCyclE{[&](auto &s) { return ""; }};	     // at cyclic edge discovery
	PrinterT atBackE{[&](auto &s) { return ""; }};	     // at backward edge discovery
	PrinterT atForwE{[&](auto &s) { return ""; }};	     // at forward edge discovery
	PrinterT atEnd{[&](auto &s) { return ""; }};	     // at node exit
	PrinterT atFinal{[&](auto &s) { return ""; }};	     // at final node discovery
	PrinterT atReturnFalse{[&](auto &s) { return ""; }}; // when a rec call returns false

	std::unordered_map<State *, unsigned> ids{}; // state->id map
	std::unordered_map<State *, bool> visit{};   // state->"has visit array"
};

GenMCPrinter::GenMCPrinter(const KatModule &module, const Config &config) : Printer(module, config)
{
	className = getPrefix() + "Checker";
	guardName = std::string("GENMC_") + getPrefix() + "_CHECKER_HPP";

	/* Open required streams, if the user requested file printing */
	if (!getPrefix().empty()) {
		foutHpp = openFileForWriting(getConf().dir + "/" + className + ".hpp");
		outHpp = &foutHpp;
		foutCpp = openFileForWriting(getConf().dir + "/" + className + ".cpp");
		outCpp = &foutCpp;
	}
}

auto GenMCPrinter::shouldPrintSuccAcycChecks() const -> bool
{
	return !getModule().isDepTracking();
}

auto GenMCPrinter::usesRfInvInAcycChecks() const -> bool
{
	auto result = false;
	for (auto &stmt : getModule().exports()) {
		auto *acyc = dynamic_cast<AcyclicConstraint *>(stmt->getConstraint());
		if (!acyc)
			continue;

		auto rfInv = Relation::createBuiltin(Relation::BuiltinID::rf).invert();
		visitRE(acyc->getRERef(), [&](auto &r) {
			auto *charRE = dynamic_cast<const CharRE *>(&*r);
			if (charRE && charRE->getLabel().getRelation().has_value() &&
			    *charRE->getLabel().getRelation() == rfInv)
				result = true;
		});
	}
	return result;
}

void GenMCPrinter::outputDFSCode(const NFA &nfa, const DFSParameters &params)
{
	assert(!params.name.empty() && !params.ids.empty() && !params.hasVisitArray.empty());
	auto getStateFunName = [&](auto *s) {
		return params.name + "_" + std::to_string(params.ids.at(s));
	};
	auto getStateArrName = [&](auto *s) {
		return params.status + "_" + std::to_string(params.ids.at(s));
	};

	/* Declare all variables and methods */
	for (auto &sUP : nfa.states()) {
		hpp() << "\tmutable std::vector<NodeStatus> " << getStateArrName(&*sUP) << ";\n";
	}
	hpp() << "\n";
	for (auto &sUP : nfa.states()) {
		hpp() << "\tbool " << getStateFunName(&*sUP) << "(" << params.params << ") "
		      << "const;\n";
	}
	hpp() << "\n";

	/* Print the DFS routines */
	for (auto &sUP : nfa.states()) {
		cpp() << "bool " << className << "::" << getStateFunName(&*sUP) << "("
		      << params.params << ") const \n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\n";

		if (params.visit.at(&*sUP)) {
			cpp() << "\tif (" << getStateArrName(&*sUP)
			      << "[lab->getStamp().get()] != NodeStatus::unseen)\n"
			      << "\t\treturn true;\n"
			      << "\t" << getStateArrName(&*sUP)
			      << "[lab->getStamp().get()] = NodeStatus::entered;\n";
		}

		cpp() << params.atBegin("lab") << "\n";
		if (sUP->isStarting()) {
			cpp() << params.atFinal("lab") << "\n";
		}

		for (auto &t : sUP->ins()) {
			cpp() << "\t";
			printTransLabel(cpp(), t, "pLab", "lab", params.savedParam);
			cpp() << " {\n";
			if (params.visit.at(t.dest)) {
				cpp() << "\t\tauto status = " << getStateArrName(t.dest)
				      << "[pLab->getStamp().get()];\n"
				      << "\t\tif (status == NodeStatus::unseen) {\n";
			}
			cpp() << "\t\t\tif (!" << getStateFunName(t.dest) << "("
			      << params.createParams("pLab") << ")){\n"
			      << params.atReturnFalse("lab") << "\n"
			      << "\t\t}\n"
			      << "\t\t" << params.atTreeE("lab") << "\n";
			if (params.visit.at(t.dest)) {
				cpp() << "\t\t} else if (status == NodeStatus::entered) {\n"
				      << params.atCyclE("pLab") << "\n"
				      << "\t\t} else if (status == NodeStatus::left) {\n"
				      << params.atForwE("pLab") << "\n"
				      << "\t\t}\n";
			}
			cpp() << "\t}\n";
		}

		cpp() << params.atEnd("lab") << "\n";
		if (params.visit.at(&*sUP)) {
			cpp() << "\t" << getStateArrName(&*sUP)
			      << "[lab->getStamp().get()] = NodeStatus::left;\n";
		}
		cpp() << "\treturn true;\n"
		      << "}\n"
		      << "\n";
	}
}

void GenMCPrinter::outputSCCCode(const NFA &nfa, const DFSParameters &params)
{
	assert(!params.name.empty() && !params.ids.empty() && !params.hasVisitArray.empty());
	auto getStateFunName = [&](auto *s) {
		return params.name + "_" + std::to_string(params.ids.at(s));
	};
	auto getStateArrName = [&](auto *s) {
		return params.status + "_" + std::to_string(params.ids.at(s));
	};
	auto acceptingCountName = params.status + "Accepting";

	/* Declare all variables and methods */
	for (auto &sUP : nfa.states()) {
		hpp() << "\tmutable std::vector<NodeVisitStatus> " << getStateArrName(&*sUP)
		      << ";\n";
	}
	hpp() << "\tmutable uint32_t " << acceptingCountName << ";\n"
	      << "\n";
	for (auto &sUP : nfa.states()) {
		hpp() << "\tbool " << getStateFunName(&*sUP) << "(" << params.params << ") "
		      << "const;\n";
	}
	hpp() << "\n";

	/* Output SCC code */
	for (auto &sUP : nfa.states()) {
		cpp() << "bool " << className << "::" << getStateFunName(&*sUP) << "("
		      << params.params << ") const \n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\n"
		      << (sUP->isStarting() ? "\t++"s + acceptingCountName + ";\n"s : ""s);
		if (params.visit.at(&*sUP)) {
			cpp() << "\t" << getStateArrName(&*sUP) << "[lab->getStamp().get()] = { "
			      << acceptingCountName << ", NodeStatus::entered };\n";
		}

		cpp() << params.atBegin("lab") << "\n";
		if (sUP->isStarting()) {
			cpp() << params.atFinal("lab") << "\n";
		}

		for (auto &t : sUP->ins()) {
			cpp() << "\t";
			printTransLabel(cpp(), t, "pLab", "lab", params.savedParam);
			cpp() << " {\n";
			if (params.visit.at(t.dest)) {
				cpp() << "\t\tauto &node = " << getStateArrName(t.dest)
				      << "[pLab->getStamp().get()];\n"
				      << "\t\tif (node.status == NodeStatus::unseen) {\n";
			}
			cpp() << "\t\t\tif (!" << getStateFunName(t.dest) << "("
			      << params.createParams("pLab") << ")){\n"
			      << params.atReturnFalse("lab") << "\n"
			      << "\t\t}\n"
			      << "\t\t" << params.atTreeE("lab") << "\n";
			if (params.visit.at(t.dest)) {
				cpp() << "\t\t} else if (node.status == NodeStatus::entered && ("
				      << acceptingCountName << " > node.count || "
				      << std::to_string(t.dest->isAccepting()) << ")) {\n"
				      << params.atCyclE("pLab") << "\n"
				      << "\t\t\treturn false;\n"
				      << "\t\t} else if (node.status == NodeStatus::left) {\n"
				      << params.atForwE("pLab") << "\n"
				      << "\t\t}\n";
			}
			cpp() << "\t}\n";
		}

		cpp() << (sUP->isStarting() ? "\t--"s + acceptingCountName + ";\n"s : ""s);
		if (params.visit.at(&*sUP)) {
			cpp() << "\t" << getStateArrName(&*sUP) << "[lab->getStamp().get()] = "
			      << "{ " << acceptingCountName << ", NodeStatus::left };\n";
		}
		cpp() << params.atEnd("lab") << "\n";
		cpp() << "\treturn true;\n"
		      << "}\n"
		      << "\n";
	}
}

auto replaceAll(std::string &inout, const std::string &what, const std::string &with) -> std::size_t
{
	std::size_t count{};
	for (std::string::size_type pos{};
	     std::string::npos != (pos = inout.find(what.data(), pos, what.length()));
	     pos += with.length(), ++count) {
		inout.replace(pos, what.length(), with.data(), with.length());
	}
	return count;
}

void GenMCPrinter::printPredSet(std::ostream &ostr, const std::string &arg,
				const PredicateSet &preds)
{
	if (preds.begin() == preds.end())
		return;

	ostr << "if (true";
	for (const auto &p : preds.preds()) {
		ostr << " && ";

		auto s = getModule().getTheory().getInfo(p).genmc;
		replaceAll(s, "#", arg);
		ostr << s;
	}
	ostr << ")";
}

void GenMCPrinter::printRelation(std::ostream &ostr, const std::string &res, const std::string &arg,
				 const std::optional<Relation> &r)
{
	if (!r.has_value()) {
		ostr << "if (auto " << res << " = " << arg << "; true)";
		return;
	}

	if (r->isBuiltin()) {
		const auto &rInfo = getModule().getTheory().getInfo(*r);
		const auto &outs = getModule().getTheory().getInfo(*r).genmc;
		const auto &s = r->isInverse() ? outs.pred : outs.succ;
		// FIXME: Make iterators for ctrl/data/dep respect the current API
		if (r->toBuiltin() == Relation::BuiltinID::data ||
		    r->toBuiltin() == Relation::BuiltinID::ctrl ||
		    r->toBuiltin() == Relation::BuiltinID::addr) {
			ostr << "for (auto &p : " << s << "(g, " << arg << ")) if (auto *" << res
			     << " = g.getEventLabel(p); true)";
		} else if (rInfo.arity == RelArity::OneOne ||
			   (rInfo.arity == RelArity::OneMany && r->isInverse()) ||
			   (rInfo.arity == RelArity::ManyOne && !r->isInverse())) {
			ostr << "if (auto " << res << " = " << s << "(g, " << arg << "); " << res
			     << ")";
		} else {
			ostr << "for (auto &tmp : " << s << "(g, " << arg << ")) if (auto *" << res
			     << " = &tmp; true)";
		}
		return;
	}

	// No view indexes should appear when printing nfas.
	// if they do appear, it's from rec views => these are left rec
	// => just yield the same event (next state is guaranteed to be starting)
	if (isMutRecRelation(r->getID())) {
		ostr << "if (auto " << res << " = " << arg << "; true)";
		return;
	}

	// FIXME: assumes preds + immediate
	assert(getModule().getTheory().hasInfo(*r));
	const auto &outs = getModule().getTheory().getInfo(*r).genmc;
	const auto &s = r->isInverse() ? outs.pred : outs.succ;
	ostr << "if (auto " << res << " = " << s << "(g, " << arg << "); " << res << ")";
	return;
}

void GenMCPrinter::printTransLabel(std::ostream &ostr, const NFA::Transition &t,
				   const std::string &res, const std::string &arg,
				   const std::string &saveRes)
{
	printPredSet(ostr, arg, t.label.getPreChecks());
	printRelation(ostr, res, arg, t.label.getRelation());
	printPredSet(ostr, res, t.label.getPostChecks());

	/* If the destination is starting, update the saved result */
	if (!t.dest->isStarting() || saveRes.empty())
		return;

	if (isMutRecRelation(t.label.getRelation()->getID())) {
		ostr << "if (" << saveRes << ".update(" << res << "->view("
		     << getPrintedIdx(getMutRecRelationDeclaration(t.label.getRelation()->getID()))
		     << ")); true)";
	} else {
		ostr << "if (" << saveRes << ".updateIdx(" << res << "->getPos()); true)";
	}
}

void GenMCPrinter::printHeader()
{
	/* Print a copyright notice in both HPP and CPP */
	hpp() << genmcCopyright << "\n" << katerNotice << "\n";
	cpp() << genmcCopyright << "\n" << katerNotice << "\n";

	/* Print all declarations in the HPP file */
	hpp() << "#ifndef " << guardName << "\n"
	      << "#define " << guardName << "\n"
	      << "\n"
	      << "#include \"ExecutionGraph/Consistency/ConsistencyChecker.hpp\"\n"
	      << "#include \"ExecutionGraph/EventLabel.hpp\"\n"
	      << "#include <cstdint>\n"
	      << "#include <vector>\n"
	      << "\n"
	      << "class " << className << " : public ConsistencyChecker {\n"
	      << "\n"
	      << "private:\n"
	      << "\tenum class NodeStatus : unsigned char { unseen, entered, "
		 "left };\n"
	      << "\n"
	      << "\tstruct NodeVisitStatus {\n"
	      << "\t\tNodeVisitStatus() = default;\n"
	      << "\t\tNodeVisitStatus(uint32_t c, NodeStatus s) : "
		 "count(c), "
		 "status(s) {}\n"
	      << "\t\tuint32_t count{};\n"
	      << "\t\tNodeStatus status{};\n"
	      << "\t};\n"
	      << "\n"
	      << "public:\n"
	      << "\t" << className << "(const Config *conf) : ConsistencyChecker(conf) {};\n"
	      << "\n"
	      << "private:\n"
	      << "\tbool isConsistent(const EventLabel *lab) const override;\n"
	      << "\tbool isConsistent(const ExecutionGraph &g) const override;\n"
	      << "\tbool isCoherentRelinche(const ExecutionGraph &g) const override;\n"
	      << "\tstd::optional<VerificationError> checkErrors(const EventLabel *lab, const "
		 "EventLabel *&race) const;\n"
	      << "\tstd::vector<VerificationError> checkWarnings(const EventLabel *lab, const "
		 "VSet<VerificationError> &reported, std::vector<const EventLabel *> &races) "
		 "const override;\n"
	      << "\tstd::vector<EventLabel *> getCoherentStores(ReadLabel *rLab) override;\n"
	      << "\tvoid filterCoherentRevisits(WriteLabel *sLab, std::vector<ReadLabel *> &ls) "
		 "override;\n"
	      << "\tstd::vector<EventLabel *> getCoherentPlacings(WriteLabel *sLab) override;\n"
	      << "\tvoid updateMMViews(EventLabel *lab) override;\n"
	      << "\tstd::unique_ptr<VectorClock> calculatePrefixView(const EventLabel *lab) const "
		 "override;\n"
	      << "\tbool isDepTracking() const;\n"
	      << "\tvoid calculateSaved(EventLabel *lab);\n"
	      << "\tvoid calculateViews(EventLabel *lab);\n"
	      << "\tmutable const EventLabel *cexLab{};\n"
	      << "\n";

	/* Print all includes in the CPP file */
	cpp() << "#include \"" << className << ".hpp\"\n"
	      << "#include \"ADT/VSet.hpp\"\n"
	      << "#include "
	      << (getModule().isDepTracking() ? "\"ADT/DepView.hpp\"\n"s : "\"ADT/View.hpp\"\n"s)
	      << "#include \"ExecutionGraph/ExecutionGraph.hpp\"\n"
	      << "#include \"ExecutionGraph/GraphIterators.hpp\"\n"
	      << "#include \"ExecutionGraph/GraphUtils.hpp\"\n"
	      << "#include \"Verification/Config.hpp\"\n"
	      << "#include \"Verification/VerificationError.hpp\"\n"
	      << "\n";
}

void GenMCPrinter::printFooter()
{
	/* End the class on the HPP file */
	hpp() << "\n"
	      << "};\n"
	      << "\n"
	      << "#endif /* " << guardName << " */\n";
}

void GenMCPrinter::output()
{
	printHeader();

	auto &module = getModule();
	auto &theory = module.getTheory();

	cpp() << "bool " << className << "::isDepTracking() const\n"
	      << "{\n"
	      << "\treturn " << module.isDepTracking() << ";\n"
	      << "}\n"
	      << "\n";

	/************************************************************
	** calculators, views, etc
	************************************************************/

	// We keep the names of the printed routines saved in the exportedNames map
	auto vc = 0U;
	auto sc = 0U;
	std::unordered_map<Statement *, std::string> exportedNames;
	for (auto &let : module.lets()) {
		if (dynamic_cast<NoSavedExp *>(let->getSaved()))
			continue;

		/* Store the array index printed for the let statement
		 * (NOTE: the index corresponds to either the view or the set array) */
		auto letIdx = dynamic_cast<ViewExp *>(let->getSaved()) ? vc++ : sc++;
		letToIdxMap.insert({&*let, letIdx});

		/* Also keep mappings from recursive relations (these are used in regexps) */
		if (auto *mutRecRE = dynamic_cast<const MutRecRE *>(let->getRE())) {
			mutRecRelToLetMap.emplace(mutRecRE->getRelation().getID(), &*let);
		}

		// Print the calculation routines
		auto exportedNameSuffix = "Calc" + std::to_string(let->getID());
		auto name =
			toCamelCase(let->getName().substr(let->getName().find_last_of(":") + 1));
		printCalculator(&*let, exportedNameSuffix, name);

		// Also print a wrapper around the main entry point (in case we ever want
		// GenMC-specific code to run)
		auto exportedName = "check" + exportedNameSuffix;
		exportedNames[&*let] = exportedName;
		hpp() << "\tauto " << exportedName << "(const EventLabel *lab) const;\n";
		cpp() << "auto " << className << "::" << exportedName
		      << "(const EventLabel *lab) const\n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\n";
		cpp() << "\treturn visit" << exportedNameSuffix << "(lab);\n}\n";
	}
	cpp() << "void " << className << "::calculateSaved(EventLabel *lab)\n"
	      << "{\n";
	for (auto &let : module.lets()) {
		if (!dynamic_cast<SetExp *>(let->getSaved()))
			continue;

		cpp() << "\tlab->addSaved(" << exportedNames[&*let] << "(lab));\n";
	}
	cpp() << "}\n"
	      << "\n";
	cpp() << "void " << className << "::calculateViews(EventLabel *lab)\n"
	      << "{\n"
	      << "\tlab->setViews({});\n";
	for (auto &let : module.lets()) {
		if (!dynamic_cast<ViewExp *>(let->getSaved()))
			continue;
		if (let->hasCodeToPrint())
			cpp() << *let->getCodeToPrint() << "\n";
		cpp() << "\tlab->addView(" << exportedNames[&*let] << "(lab));\n";
	}
	cpp() << "}\n"
	      << "\n";
	cpp() << "void " << className << "::updateMMViews(EventLabel *lab)\n"
	      << "{\n"
	      << "\tcalculateViews(lab);\n"
	      << "\tcalculateSaved(lab);\n";
	if (!module.isDepTracking()) { /* we can optimize the calculation */
		cpp() << "\tlab->setPrefixView(calculatePrefixView(lab));\n";
	}
	cpp() << "}\n"
	      << "\n";

	// FIXME: Somewhere sanitize exports (unless has to be <= )

	// First, print the main consistency check dictated by the constraint.
	for (auto &stmt : module.exports()) {
		std::string exportedNameSuffix;
		bool counterexample = false;
		auto visitor = make_visitor(
			type_list<AcyclicConstraint, SubsetConstraint, EqualityConstraint,
				  WarningConstraint, ErrorConstraint, CoherenceConstraint,
				  TotalityConstraint>{},
			[&](const AcyclicConstraint &acst) {
				exportedNameSuffix = "ConsAcyclic" + std::to_string(stmt->getID());
				printAcyclic(&acst, exportedNameSuffix);
			},
			[&](const SubsetConstraint &scst) {
				exportedNameSuffix =
					"ConsInclusion" + std::to_string(stmt->getID());
				printSubset(&scst, exportedNameSuffix);
			},
			[&](const EqualityConstraint &ecst) {
				exportedNameSuffix = "ConsEquality" + std::to_string(stmt->getID());
				printSubset(&ecst, exportedNameSuffix + "Direct");
				auto convC = SubsetConstraint::create(
					ecst.getRHS()->clone(), ecst.getLHS()->clone(),
					ecst.sameEnds(), ecst.rotated());
				printSubset(&*convC, exportedNameSuffix + "Converse");
				cpp() << "bool visit" + exportedNameSuffix
				      << "(const EventLabel *lab){ return visit"
				      << exportedNameSuffix + "Direct(lab) && visit "
				      << exportedNameSuffix << "Converse(lab); }";
			},
			[&](const WarningConstraint &wcst) {
				counterexample = true;
				exportedNameSuffix = "Warning" + std::to_string(stmt->getID());
				printWarning(&wcst, exportedNameSuffix);
			},
			[&](const ErrorConstraint &wcst) {
				counterexample = true;
				exportedNameSuffix = "Error" + std::to_string(stmt->getID());
				printWarning(&wcst, exportedNameSuffix);
			},
			[&](const CoherenceConstraint &ccst) { printCoherence(&ccst); },
			[&](const TotalityConstraint &tcst) {
				std::cerr << "[Error] Cannot export totality constraint.\n";
			});
		visitor(*stmt->getConstraint());

		// Skip if there was nothing to export
		if (exportedNameSuffix.empty())
			continue;

		auto exportedName = "check" + exportedNameSuffix;
		exportedNames[&*stmt] = exportedName;

		// Then, print the "unless" routine with the respective name
		printUnless(stmt->getUnless(), "Unless" + exportedNameSuffix, counterexample);

		// Finally, print a checker that combines the main routine and the unless
		// clause, as well as GenMC-specific code

		//  Incremental version:
		hpp() << "\tbool " << exportedName << "(const EventLabel *lab) const;\n";
		cpp() << "bool " << className << "::" << exportedName
		      << "(const EventLabel *lab) const\n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\n";
		if (stmt->hasCodeToPrint())
			cpp() << *stmt->getCodeToPrint() << "\n";
		if (stmt->getUnless())
			cpp() << "\tif (visitUnless" << exportedNameSuffix << "(lab))\n"
			      << "\t\treturn true;\n"
			      << "\n";
		cpp() << "\treturn visit" << exportedNameSuffix << "(lab);\n}\n";

		//  Full version (currently acyclicity only):
		if (!dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint()))
			continue;
		hpp() << "\tbool " << exportedName << "(const ExecutionGraph &g) const;\n";
		cpp() << "bool " << className << "::" << exportedName
		      << "(const ExecutionGraph &g) const\n"
		      << "{\n"
		      << "\treturn visit" << exportedNameSuffix << "Full(g);\n}\n";
	}

	cpp() << "std::optional<VerificationError> " << className
	      << "::checkErrors(const EventLabel *lab, const EventLabel *&race) const\n"
	      << "{";
	for (auto &stmt : module.exports()) {
		auto *errorCst = dynamic_cast<const ErrorConstraint *>(stmt->getConstraint());
		if (!errorCst) {
			continue;
		}
		cpp() << "\n\tif (!" << exportedNames[&*stmt] << "(lab)) {"
		      << "\n\t\trace = cexLab;"
		      << "\n\t\treturn {VerificationError::" << errorCst->getWarningName() << "};"
		      << "\n\t}\n";
	}
	cpp() << "\n\treturn {};\n"
	      << "}\n"
	      << "\n";
	cpp() << "std::vector<VerificationError> " << className
	      << "::checkWarnings(const EventLabel *lab, const VSet<VerificationError> "
		 "&seenWarnings, std::vector<const EventLabel *> &racyLabs) const\n"
	      << "{\n"
	      << "\tstd::vector<VerificationError> result;\n";
	for (auto &stmt : module.exports()) {
		auto *warnCst = dynamic_cast<const WarningConstraint *>(stmt->getConstraint());
		if (!warnCst || dynamic_cast<const ErrorConstraint *>(warnCst)) {
			continue;
		}
		cpp() << "\n\tif (seenWarnings.count(VerificationError::"
		      << warnCst->getWarningName() << ") == 0 && !" << exportedNames[&*stmt]
		      << "(lab)) {"
		      << "\n\t\tracyLabs.push_back(cexLab);"
		      << "\n\t\tresult.push_back(VerificationError::" << warnCst->getWarningName()
		      << ");"
		      << "\n\t}\n";
	}
	cpp() << "\n\treturn result;\n"
	      << "}\n"
	      << "\n";

	/************************************************************
	 * consistency
	 ************************************************************/

	/* incremental version */
	cpp() << "bool " << className << "::isConsistent(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\n\treturn true";
	for (auto &stmt : module.exports()) {
		auto *acycCst = dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
		if (!acycCst) {
			continue;
		}
		if (!stmt->isExtra())
			cpp() << "\n\t\t&& " << exportedNames[&*stmt] << "(lab)";
	}
	// FIXME: for equality
	for (auto &stmt : module.exports()) {
		auto *subCst = dynamic_cast<const SubsetConstraint *>(stmt->getConstraint());
		if (!subCst) {
			continue;
		}
		if (!stmt->isExtra())
			cpp() << "\n\t\t&& " << exportedNames[&*stmt] << "(lab)";
	}
	cpp() << ";\n"
	      << "}\n"
	      << "\n";

	/* full version */
	cpp() << "bool " << className << "::isConsistent(const ExecutionGraph &g) const\n"
	      << "{\n"
	      << "\n\treturn true";
	for (auto &stmt : module.exports()) {
		auto *acycCst = dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
		if (!acycCst) {
			continue;
		}
		if (!stmt->isExtra())
			cpp() << "\n\t\t&& " << exportedNames[&*stmt] << "(g)";
	}
	// FIXME: for equality
	for (auto &stmt : module.exports()) {
		auto *subCst = dynamic_cast<const SubsetConstraint *>(stmt->getConstraint());
		if (!subCst) {
			continue;
		}
		if (!stmt->isExtra())
			cpp() << "\n\t\t&& " << exportedNames[&*stmt] << "(g)";
	}
	cpp() << ";\n"
	      << "}\n"
	      << "\n";

	/* coherence (special treatment) */
	cpp() << "bool " << className << "::isCoherentRelinche(const ExecutionGraph &g) const\n"
	      << "{\n"
	      << "\n\treturn true";
	for (auto &stmt : module.exports()) {
		auto *cohCst = dynamic_cast<const CoherenceConstraint *>(stmt->getConstraint());
		if (!cohCst) {
			continue;
		}
		assert(!stmt->isExtra());
		cpp() << "\n\t\t&& visitCoherenceRelinche(g)";
	}
	cpp() << ";\n"
	      << "}\n"
	      << "\n";

	/* print the extras */
	for (auto &stmt : module.exports()) {
		if (stmt->isExtra()) {
			hpp() << "\tbool " << *stmt->getNameOfExtra()
			      << "(const EventLabel *lab) { return " << exportedNames[&*stmt]
			      << "(lab); }\n";
		}
	}
	hpp() << "\n";

	/* pporf-before getter */
	auto pporfNFA = module.createPPORF()->toNFA();
	simplify(pporfNFA, theory);
	printPPoRfHpp(pporfNFA, module.isDepTracking());
	printPPoRfCpp(pporfNFA, module.isDepTracking());
	cpp() << "std::unique_ptr<VectorClock> " << className
	      << "::calculatePrefixView(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\treturn std::make_unique<" << (module.isDepTracking() ? "DepView" : "View")
	      << ">(calcPPoRfBefore(lab));\n"
	      << "}\n"
	      << "\n";

	printFooter();
}

template <typename ITER>
auto assignStateIDs(ITER &&begin, ITER &&end) -> std::unordered_map<NFA::State *, unsigned>
{
	std::unordered_map<NFA::State *, unsigned> result;

	auto i = 0U;
	std::for_each(begin, end, [&](auto &s) { result[&*s] = i++; });
	return result;
}

auto GenMCPrinter::getStateVisitAssignment(const NFA &nfa) const
	-> std::unordered_map<NFA::State *, bool>
{
	std::unordered_map<NFA::State *, bool> result;

	/* Helper that determines whether a state has any "outpoints" (i.e.,
	 * whether the edges leaving a state lead anywhere) */
	auto hasOutpoints = [&](NFA::State *s) {
		return std::ranges::any_of(s->ins(),
					   [&](auto &t) { return t.dest->hasIncoming(); });
	};
	/* A state should have a visit array if it has many entrypoints,
	 * and these are meaningful (i.e., if they lead nowhere, having a visit
	 * array doesn't really save anything) */
	auto shouldHaveVisitArray = [&](NFA::State *s) {
		return s->getNumOutgoing() > 1 &&
		       std::ranges::any_of(s->ins(), [&](auto &t) { return hasOutpoints(t.dest); });
	};

	for (auto &sUP : nfa.states()) {
		result[&*sUP] = getConf().emitVisitArrays ? true : shouldHaveVisitArray(&*sUP);
	}
	return result;
}

void GenMCPrinter::printSubset(const SubsetConstraint *subCst, std::string prefix,
			       bool counterexample)
{
	auto nfaLHS = subCst->getLHS()->toNFA();
	simplify(nfaLHS, getModule().getTheory());
	auto nfaRHS = subCst->getRHS()->toNFA();
	simplify(nfaRHS, getModule().getTheory());

	/* Create a config for both LHS and RHS */
	DFSParameters paramsLHS = {
		.name = "visitLHS" + prefix,
		.status = "visitedLHS" + prefix,
		.params = "const EventLabel *lab",
		.savedParam = "",
		.createParams = [&](auto &s) { return s; },
		.atFinal =
			[&](auto &s) {
				return paramsLHS.status +
				       "Accepting[lab->getStamp().get()] = true;";
			},
		.atReturnFalse = [&](auto &s) { return "\t\t\treturn false;"; },
		.ids = assignStateIDs(nfaLHS.states_begin(), nfaLHS.states_end()),
		.visit = getStateVisitAssignment(nfaLHS),
	};
	DFSParameters paramsRHS = {
		.name = "visitRHS" + prefix,
		.status = "visitedRHS" + prefix,
		.params = "const EventLabel *lab",
		.savedParam = "",
		.createParams = [&](auto &s) { return s; },
		.atFinal =
			[&](auto &s) {
				return paramsRHS.status +
				       "Accepting[lab->getStamp().get()] = true;";
			},
		.atReturnFalse = [&](auto &s) { return "\t\t\treturn false;"; },
		.ids = assignStateIDs(nfaRHS.states_begin(), nfaRHS.states_end()),
		.visit = getStateVisitAssignment(nfaRHS),
	};

	/* Can we skip visiting the RHS? If so, change the LHS config*/
	LetStatement *viewLet = nullptr;
	std::optional<int> rhsViewIdx;
	auto shouldVisitRHS = true;
	if (subCst->isEmpty()) {
		/* Case e <= 0 : we can optimize and return false if any accepting is
		 * reachable */
		paramsLHS.atFinal = [&](auto &s) { return "\treturn false;\n"; };
	} else if (std::ranges::any_of(getModule().lets(), [&](auto &let) {
			   viewLet = &*let;
			   return dynamic_cast<const ViewExp *>(let->getSaved()) &&
				  *let->getRE() == *subCst->getRHS();
		   })) {
		shouldVisitRHS = false;
		rhsViewIdx = getPrintedIdx(viewLet);
		/* Case e <= VIEW: return false if any accepting is not in view */
		paramsLHS.params = "const EventLabel *lab, const View &v";
		paramsLHS.createParams = [&](auto &s) { return s + ", v"; },
		paramsLHS.atFinal = [&](auto &s) {
			return "\tif (!v.contains(lab->getPos())) {\n" +
			       (counterexample ? std::string("cexLab = lab;\n") : std::string("")) +
			       "\t\treturn false;\n"
			       "\t}\n";
		};
	}

	/* Print the DFS routines */
	outputDFSCode(nfaLHS, paramsLHS);
	if (shouldVisitRHS) {
		outputDFSCode(nfaRHS, paramsRHS);
	}

	/* Print extra arrays used by the DFS routines */
	hpp() << "\tmutable std::vector<bool> " << paramsLHS.status << "Accepting;\n";
	if (shouldVisitRHS) {
		hpp() << "\tmutable std::vector<bool> " << paramsRHS.status << "Accepting;\n";
	}

	/* Print a "visit" function for the automaton (again based on the RHS) */
	hpp() << "\tbool "
	      << "visit" + prefix << "(const EventLabel *lab) const;\n";
	cpp() << "bool " << className << "::visit" + prefix << "(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\tauto &g = *lab->getParent();\n"
	      << "\n";
	for (auto &s : nfaLHS.states() | std::views::filter([&](auto &sUP) {
			       return paramsLHS.visit.at(&*sUP);
		       })) {
		cpp() << "\t" << paramsLHS.status << "_" << paramsLHS.ids.at(&*s) << ".clear();\n"
		      << "\t" << paramsLHS.status << "_" << paramsLHS.ids.at(&*s)
		      << ".resize(g.getMaxStamp().get() + 1, NodeStatus::unseen);\n";
	}
	if (shouldVisitRHS) {
		for (auto &s : nfaRHS.states() | std::views::filter([&](auto &sUP) {
				       return paramsRHS.visit.at(&*sUP);
			       })) {
			cpp() << "\t" << paramsRHS.status << "_" << paramsRHS.ids.at(&*s)
			      << ".clear();\n"
			      << "\t" << paramsRHS.status << "_" << paramsRHS.ids.at(&*s)
			      << ".resize(g.getMaxStamp().get() + 1, "
				 "NodeStatus::unseen);\n";
		}
	}
	cpp() << "\t" << paramsLHS.status << "Accepting.clear();\n "
	      << "\t" << paramsLHS.status
	      << "Accepting.resize(g.getMaxStamp().get() + 1, false);\n";

	if (shouldVisitRHS) {
		cpp() << "\t" << paramsRHS.status << "Accepting.clear();\n"
		      << "\t" << paramsRHS.status
		      << "Accepting.resize(g.getMaxStamp().get() + 1, false);\n"
		      << "\n";
	}

	if (!shouldVisitRHS) {
		cpp() << "\tauto &v = lab->view(" << *rhsViewIdx << ");\n"
		      << "\n";
		cpp() << "\treturn true";
		for (auto &s : nfaLHS.accepting()) {
			cpp() << "\n\t\t&& " << paramsLHS.name << "_" << paramsLHS.ids.at(s)
			      << "(lab, v)";
		}
		cpp() << ";\n"
		      << "}\n"
		      << "\n";
	} else {
		for (auto &s : nfaLHS.accepting()) {
			cpp() << "\tif (!" << paramsLHS.name << "_" << paramsLHS.ids.at(s)
			      << "(lab))\n"
			      << "\t\treturn false;\n";
		}
		for (auto &s : nfaRHS.accepting()) {
			cpp() << "\tif (!" << paramsRHS.name << "_" << paramsRHS.ids.at(s)
			      << "(lab))\n"
			      << "\t\treturn false;\n";
		}

		cpp() << "\tfor (auto i = 0u; i < " << paramsLHS.status
		      << "Accepting.size(); i++) {\n"
		      << "\t\tif (" << paramsLHS.status << "Accepting[i] && !" << paramsRHS.status
		      << "Accepting[i]) {\n";
		if (counterexample) {
			cpp() << "\t\t\tcexLab = &*std::find_if(g.label_begin(), "
				 "g.label_end(), "
				 "[&](auto &lab){ "
				 "return "
				 "lab.getStamp() == i; });\n";
		}
		cpp() << "\t\t\treturn false;\n"
		      << "\t\t}\n"
		      << "\t}\n"
		      << "\treturn true;\n"
		      << "}\n"
		      << "\n";
	}
}

void GenMCPrinter::printUnless(const Constraint *cst, std::string prefix, bool counterexample)
{
	if (!cst) {
		hpp() << "\tbool check" + prefix + "(const EventLabel *lab) { return false; }\n";
		return;
	}

	auto *subCst = dynamic_cast<const SubsetConstraint *>(cst);
	assert(subCst);
	printSubset(subCst, prefix, counterexample);
}

void GenMCPrinter::printWarning(const WarningConstraint *stmt, std::string prefix)
{
	/* Print a "visit" function for the automaton */
	hpp() << "\tbool "
	      << "visit" << prefix << "(const EventLabel *lab) const;\n";
	cpp() << "bool " << className << "::visit" << prefix << "(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\treturn false;\n"
	      << "}\n\n";
}

void GenMCPrinter::printAcyclic(const AcyclicConstraint *acycCst, std::string prefix)
{
	// Take the reflexive-transitive closure, which typically helps minizing the
	// NFA. Doing so is alright because the generated DFS code discounts empty
	// paths anyway.
	auto nfa = acycCst->getRE()->toNFA();
	nfa.star();
	simplify(nfa, getModule().getTheory());
	removeSimilarTransitions(nfa);

	if (getConf().verbose >= 3)
		std::cerr << "Acyclic size " << nfa.size() << "\n";

	// For non-dep-tracking models, we can iterate the NFA based on
	// outgoing transitions. This is more efficient, as maximal graph
	// events typically have more incoming than outgoing edges
	if (shouldPrintSuccAcycChecks())
		nfa.flip();

	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.params = "const EventLabel *lab",
		.savedParam = "",
		.createParams = [&](auto &s) { return s; },
		.atBegin = [&](auto &s) { return ""; },
		.atTreeE = [&](auto &s) { return ""; },
		.atCyclE = [&](auto &s) { return ""; },
		.atBackE = [&](auto &s) { return ""; },
		.atForwE = [&](auto &s) { return ""; },
		.atEnd = [&](auto &s) { return ""; },
		.atFinal = [&](auto &s) { return ""; },
		.atReturnFalse = [&](auto &s) { return "\t\t\t\treturn false;"; },
		.ids = assignStateIDs(nfa.states_begin(), nfa.states_end()),
		.visit = getStateVisitAssignment(nfa),
	};
	outputSCCCode(nfa, params);

	// Helper function for printing the initialization code

	auto printInitializations = [&]() {
		cpp() << "\t" << params.status + "Accepting = 0;\n";
		for (auto &sUP : nfa.states() | std::views::filter([&](auto &sUP) {
					 return params.visit.at(&*sUP);
				 })) {
			cpp() << "\t" << params.status << "_" << params.ids.at(&*sUP)
			      << ".clear();\n"
			      << "\t" << params.status << "_" << params.ids.at(&*sUP)
			      << ".resize(g.getMaxStamp().get() + 1);\n";
		}
	};

	/* Print "visitAcyclic(lab)" and "visitAcyclicFull(G)" for the constraint */
	hpp() << "\tbool "
	      << "visit" << prefix << "(const EventLabel *lab) const;\n"
	      << "\n";
	cpp() << "bool " << className << "::visit" << prefix << "(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\tauto &g = *lab->getParent();\n"
	      << "\n";
	printInitializations();
	cpp() << "\treturn true";
	/* Don't visit all states: for incremental checks, visit the ones you can enter with po/rf.
	 * NOTE: We use po and not po_imm below (even though the NFAs use po_imm) because the
	 * user is now allowed to use po_imm (so all po_imms are po_imm+), and we assume that only
	 * po_imm is included in itself. */
	for (auto &sUP : nfa.states()) {
		auto ts = shouldPrintSuccAcycChecks() ? sUP->ins() : sUP->outs();
		if (std::ranges::all_of(ts, [&](auto &t) {
			    auto rOpt = t.label.getRelation();
			    return rOpt.has_value() && !rOpt->isInverse() &&
				   (getModule().getTheory().isIncludedIn(
					    *rOpt,
					    Relation::createBuiltin(Relation::BuiltinID::po)) ||
				    getModule().getTheory().isIncludedIn(
					    *rOpt,
					    Relation::createBuiltin(Relation::BuiltinID::rf)) ||
				    !rOpt->isBuiltin());
		    })) {
			continue;
		}
		cpp() << "\n\t\t&& (";
		if (params.visit.at(&*sUP)) {
			cpp() << params.status << "_" << params.ids.at(&*sUP)
			      << "[lab->getStamp().get()]"
			      << ".status != NodeStatus::unseen || ";
		}
		cpp() << params.name << "_" << params.ids.at(&*sUP) << "(lab))";
	}
	cpp() << ";\n"
	      << "}\n"
	      << "\n";

	hpp() << "\tbool "
	      << "visit" << prefix << "Full(const ExecutionGraph &g) const;\n"
	      << "\n";
	cpp() << "bool " << className << "::visit" << prefix
	      << "Full(const ExecutionGraph &g) const\n"
	      << "{\n";
	printInitializations();
	cpp() << "\treturn true";
	for (auto &sUP : nfa.accepting()) {
		cpp() << "\n\t\t&& std::ranges::all_of(g.labels(), [&](auto &lab){ return ";
		if (params.visit.at(&*sUP)) {
			cpp() << params.status << "_" << params.ids.at(&*sUP)
			      << "[lab.getStamp().get()]"
			      << ".status != NodeStatus::unseen || ";
		}
		cpp() << params.name << "_" << params.ids.at(&*sUP) << "(&lab); })";
	}
	cpp() << ";\n"
	      << "}\n"
	      << "\n";
}

void GenMCPrinter::printCoherence(const CoherenceConstraint *cohCst)
{
	auto s = std::string(coherenceFuns);
	replaceAll(s, "#CLASS#", className);
	replaceAll(s, "#HB#", std::to_string(getPrintedIdx(getModule().getCOHDeclaration())));
	cpp() << s << "\n";

	// For coherence, we detect violations by performing multiple DFSs (for each memory access).
	// In contrast to acyclicity, we don't take the reflexive-transitive closure here.
	// This is much slower, but can be optimized for Relinche.
	// (This can potentially be optimized by taking the rotational closure of COH instead.)
	//
	// NOTE: As this is currently only used in Relinche, we instead print an optimized
	//       version that checks for hbpo;eco;hbpo;lin irreflexivity.
	const auto &module = getModule();
	auto ecoREUP = PlusRE::createOpt(AltRE::createOpt(module.getRegisteredRE("rf")->clone(),
							  module.getRegisteredRE("mo")->clone(),
							  module.getRegisteredRE("fr")->clone()));
	const auto *hbpoRE = module.getRegisteredRE(cohCst->getID());
	auto nfa = SeqRE::createOpt(hbpoRE->clone(), ecoREUP->clone(), hbpoRE->clone(),
				    module.getRegisteredRE("lin")->clone())
			   ->toNFA();

	simplify(nfa, getModule().getTheory());
	// Opt: We can just get away with predecessor checks

	auto prefix = "Coherence"s;
	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.params = "const EventLabel *lab, const EventLabel *initLab",
		.savedParam = "",
		.createParams = [&](auto &s) { return s + ", initLab"; },
		.atBegin = [&](auto &s) { return ""; },
		.atTreeE = [&](auto &s) { return ""; },
		.atCyclE = [&](auto &s) { return ""; },
		.atBackE = [&](auto &s) { return ""; },
		.atForwE = [&](auto &s) { return ""; },
		.atEnd = [&](auto &s) { return ""; },
		.atFinal = [&](auto &s) { return "if (lab == initLab) return false;"; },
		.atReturnFalse = [&](auto &s) { return "return false;"; },
		.ids = assignStateIDs(nfa.states_begin(), nfa.states_end()),
		.visit = getStateVisitAssignment(nfa),
	};
	outputDFSCode(nfa, params);

	// Helper function for printing the initialization code
	auto printInitializations = [&]() {
		for (auto &sUP : nfa.states() | std::views::filter([&](auto &sUP) {
					 return params.visit.at(&*sUP);
				 })) {
			cpp() << "\t\t" << params.status << "_" << params.ids.at(&*sUP)
			      << ".clear();\n"
			      << "\t\t" << params.status << "_" << params.ids.at(&*sUP)
			      << ".resize(g.getMaxStamp().get() + 1);\n";
		}
	};

	/* Print only a "visitCoherenceRelinche(G)" for the constraint */
	hpp() << "\tbool "
	      << "visit" << prefix << "Relinche(const ExecutionGraph &g) const;\n"
	      << "\n";
	cpp() << "bool " << className << "::visit" << prefix
	      << "Relinche(const ExecutionGraph &g) const\n"
	      << "{\n";
	for (auto &sUP : nfa.accepting()) {
		cpp() << "\tfor (auto &lab : g.labels()) {\n"
		      << "\t\tif (!genmc::isa<MethodBeginLabel>(&lab)) continue;\n";
		printInitializations();
		cpp() << "\t\tif (true ";
		if (params.visit.at(&*sUP)) {
			cpp() << "&& " << params.status << params.ids.at(&*sUP)
			      << "[lab.getStamp().get()] == NodeStatus::unseen ";
		}
		cpp() << "&& !" << params.name << "_" << params.ids.at(&*sUP) << "(&lab, &lab))\n"
		      << "\t\t\treturn false;\n";
		cpp() << "\t}\n";
	}
	cpp() << "\treturn true;\n"
	      << "}\n"
	      << "\n";
}

void GenMCPrinter::printCalculator(const LetStatement *let, std::string prefix, std::string name)
{
	auto *viewExp = dynamic_cast<const ViewExp *>(let->getSaved());
	auto *setExp = dynamic_cast<const SetExp *>(let->getSaved());
	assert(viewExp || setExp);
	auto nfa = viewExp ? viewExp->getRE()->toNFA() : setExp->getRE()->toNFA();
	simplify(nfa, getModule().getTheory());

	bool isView = dynamic_cast<const ViewExp *>(let->getSaved());
	auto paramType = isView ? "View"s : "VSet<Event>"s;
	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.params = "const EventLabel *lab, " + paramType + " &calcRes",
		.savedParam = "calcRes",
		.createParams = [&](auto &s) { return s + ", calcRes"; },
		.atBegin = [&](auto &s) { return ""; },
		.atTreeE = [&](auto &s) { return ""; },
		.atCyclE = [&](auto &s) { return ""; },
		.atBackE = [&](auto &s) { return ""; },
		.atForwE = [&](auto &s) { return ""; },
		.atEnd = [&](auto &s) { return ""; },
		.atFinal = [&](auto &s) { return ""; },
		.atReturnFalse = [&](auto &s) { return "\t\t\t\treturn false;"; },
		.ids = assignStateIDs(nfa.states_begin(), nfa.states_end()),
		.visit = getStateVisitAssignment(nfa),

	};
	outputDFSCode(nfa, params);

	/* Print "visitCalc(lab) for the calculation */
	hpp() << "\t" << paramType << " visit" << prefix << "(const EventLabel *lab) const;\n";
	cpp() << paramType << " " << className << "::visit" << prefix
	      << "(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\tauto &g = *lab->getParent();\n"
	      << "\t" << paramType << " calcRes;\n"
	      << "\n"
	      << (isView ? "calcRes.updateIdx(lab->getPos());\n" : "FIXME") << "\n";
	for (auto &sUP :
	     nfa.states() | std::views::filter([&](auto &sUP) { return params.visit.at(&*sUP); })) {
		cpp() << "\t" << params.status << "_" << params.ids.at(&*sUP) << ".clear();\n"
		      << "\t" << params.status << "_" << params.ids.at(&*sUP)
		      << ".resize(g.getMaxStamp().get() + 1);\n";
	}
	cpp() << "\n";
	for (auto &sUP : nfa.accepting()) {
		cpp() << "\t" << params.name << "_" << params.ids.at(&*sUP) << "(lab, calcRes);\n";
	}
	cpp() << "\treturn calcRes;\n"
	      << "}\n";

	/* Print a getter for result */
	hpp() << "\tconst " << paramType << "&get" << name << ((isView) ? "View" : "Set")
	      << "(const EventLabel *lab) const { return lab->"
	      << ((isView) ? "view" : "calculated") << "(" << getPrintedIdx(let) << "); }\n"
	      << "\n";
}

void GenMCPrinter::printPPoRfHpp(const NFA &nfa, bool deps)
{
	auto ids = assignStateIDs(nfa.states_begin(), nfa.states_end());

	/* visitPPoRfXX for each state */
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		hpp() << "\tvoid visitPPoRf" << ids[&*s] << "(const EventLabel *lab, "
		      << (deps ? "DepView" : "View") << " &pporf) const;\n";
	});
	hpp() << "\n";

	/* calcPPoRfBefore for the automaton */
	hpp() << "\t" << (deps ? "DepView" : "View")
	      << " calcPPoRfBefore(const EventLabel *lab) const;\n";
	hpp() << "\n";

	/* status arrays */
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		hpp() << "\tmutable std::vector<NodeStatus> visitedPPoRf" << ids[&*s] << ";\n";
	});
	hpp() << "\n";
}

void GenMCPrinter::printPPoRfCpp(const NFA &nfa, bool deps)
{
	/* Optimization for non-dep-tracking models */
	if (!deps) {
		cpp() << (deps ? "DepView " : "View ") << className
		      << "::calcPPoRfBefore(const EventLabel *lab) const\n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\tView pporf;\n"
		      << "\tpporf.updateIdx(lab->getPos());\n"
		      << "\n"
		      << "\tauto *pLab = g.po_imm_pred(lab);\n"
		      << "\tif (!pLab)\n"
		      << "\t\treturn pporf;\n"
		      << "\tpporf.update(pLab->getPrefixView());\n"
		      << "\tif (auto *rLab = genmc::dyn_cast<ReadLabel>(pLab))\n"
		      << "\t\tpporf.update(rLab->getRf()->getPrefixView());\n"
		      << "\tauto *tsLab = genmc::dyn_cast<ThreadStartLabel>(pLab);\n"
		      << "\tif (tsLab && tsLab->getCreate())\n"
		      << "\t\tpporf.update(tsLab->getCreate()->getPrefixView());\n"
		      << "\tif (auto *tjLab = genmc::dyn_cast<ThreadJoinLabel>(pLab))\n"
		      << "\t\tpporf.update(g.getLastThreadLabel(tjLab->getChildId())->"
			 "getPrefixView());\n"
		      << "\treturn pporf;\n"
		      << "}\n";
		return;
	}

	auto ids = assignStateIDs(nfa.states_begin(), nfa.states_end());

	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		cpp() << "void " << className << "::visitPPoRf" << ids[&*s]
		      << "(const EventLabel *lab, " << (deps ? "DepView" : "View")
		      << " &pporf) const\n"
		      << "{\n"
		      << "\tauto &g = *lab->getParent();\n"
		      << "\n"
		      << "\tvisitedPPoRf" << ids[&*s]
		      << "[lab->getStamp().get()] = NodeStatus::entered;\n";
		if (s->isStarting()) {
			cpp() << "\tpporf.updateIdx(lab->getPos());\n";
		}
		std::for_each(s->in_begin(), s->in_end(), [&](auto &t) {
			cpp() << "\t";
			printTransLabel(cpp(), t, "pLab", "lab", "pporf");
			cpp() << " {\n"
			      << "\t\tauto status = visitedPPoRf" << ids[t.dest]
			      << "[pLab->getStamp().get()];\n"
			      << "\t\tif (status == NodeStatus::unseen)\n"
			      << "\t\t\tvisitPPoRf" << ids[t.dest] << "(pLab, pporf);\n"
			      << "\t}\n";
		});
		cpp() << "\tvisitedPPoRf" << ids[&*s]
		      << "[lab->getStamp().get()] = NodeStatus::left;\n"
		      << "}\n"
		      << "\n";
	});

	cpp() << (deps ? "DepView " : "View ") << className
	      << "::calcPPoRfBefore(const EventLabel *lab) const\n"
	      << "{\n"
	      << "\tauto &g = *lab->getParent();\n"
	      << "\t" << (deps ? "DepView" : "View") << " pporf;\n"
	      << "\tpporf.updateIdx(lab->getPos());\n";
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		cpp() << "\tvisitedPPoRf" << ids[&*s] << ".clear();\n"
		      << "\tvisitedPPoRf" << ids[&*s]
		      << ".resize(g.getMaxStamp().get() + 1, NodeStatus::unseen);\n";
	});
	cpp() << "\n";
	std::for_each(nfa.accept_begin(), nfa.accept_end(),
		      [&](auto &a) { cpp() << "\tvisitPPoRf" << ids[a] << "(lab, pporf);\n"; });
	cpp() << "\treturn pporf;\n"
	      << "}\n";
}
