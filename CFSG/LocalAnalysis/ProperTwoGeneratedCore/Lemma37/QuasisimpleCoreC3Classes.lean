module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Coords

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z)
include hb

theorem orderOf_caseC3Word [Finite G] {v : Fin 64} (hv : c3Mul v v = 0) (hv0 : v ≠ 0) :
    orderOf (caseC3Word Z u m y x v) = 2 := by
  refine orderOf_eq_prime ?_ fun h1 =>
    hv0 (hb.caseC3Word_bijective.1 (h1.trans caseC3Word_zero.symm))
  rw [pow_two, hb.caseC3Word_mul, hv, caseC3Word_zero]

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
