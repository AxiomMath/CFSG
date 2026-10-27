module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Ru.Rels
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.R
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdRu

@[expose] def nGens : Nat := 3

theorem gens_eq : TauCeti.Sporadic.ruPresentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.ruPresentation_generatorNames, nGens]

theorem hinv_tau : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) L H CM RM) (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) L H) TauCeti.Sporadic.ruPresentation.generatorCount ONE = true := by
  rw [gens_eq]
  exact hinv

theorem hroots_tau : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) L H) (nat_lit 1) (Nat.succ TauCeti.Sporadic.ruPresentation.generatorCount) = true := by
  rw [gens_eq]
  exact hroots

theorem relB_tau : CFSG.KC.Ord.relsBounded rels TauCeti.Sporadic.ruPresentation.generatorCount = true := by
  rw [gens_eq]
  exact relB

end CFSG.KD.OrdRu

end
