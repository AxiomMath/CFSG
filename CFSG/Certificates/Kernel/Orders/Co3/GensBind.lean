module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co3.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Co3.Rels
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdCo3

@[expose] def nGens : Nat := 7

theorem gens_eq : TauCeti.Sporadic.co3Presentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co3Presentation_generatorNames, nGens]

theorem hinv_tau : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 132) (nat_lit 22) (nat_lit 4) L H CM RM) (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 2904) L H) TauCeti.Sporadic.co3Presentation.generatorCount ONE = true := by
  rw [gens_eq]
  exact hinv

theorem hroots_tau : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 2904) L H) (nat_lit 1) (Nat.succ TauCeti.Sporadic.co3Presentation.generatorCount) = true := by
  rw [gens_eq]
  exact hroots

theorem relB_tau : CFSG.KC.Ord.relsBounded rels TauCeti.Sporadic.co3Presentation.generatorCount = true := by
  rw [gens_eq]
  exact relB

end CFSG.KD.OrdCo3

end
