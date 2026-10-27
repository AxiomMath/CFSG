module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co1.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Co1.Rels
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdCo1

@[expose] def nGens : Nat := 8

theorem gens_eq : TauCeti.Sporadic.co1Presentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co1Presentation_generatorNames, nGens]

theorem hinv_tau : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 144) (nat_lit 24) (nat_lit 4) L H CM RM) (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 3456) L H) TauCeti.Sporadic.co1Presentation.generatorCount ONE = true := by
  rw [gens_eq]
  exact hinv

theorem hroots_tau : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 3456) L H) (nat_lit 1) (Nat.succ TauCeti.Sporadic.co1Presentation.generatorCount) = true := by
  rw [gens_eq]
  exact hroots

theorem relB_tau : CFSG.KC.Ord.relsBounded rels TauCeti.Sporadic.co1Presentation.generatorCount = true := by
  rw [gens_eq]
  exact relB

end CFSG.KD.OrdCo1

end
