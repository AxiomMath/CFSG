module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter

public section

namespace CFSG.QuasithinUnique.Id2519.SporHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem not_kOrder_20160 : ¬ KOrder 20160 := by
  rintro (h | h | ⟨p, hp, h7, hpn⟩)
  · omega
  · omega
  · have hp34 : p ≤ 34 := by
      by_contra hlt
      push Not at hlt
      have h35 : 35 * (35 * 35 - 1) ≤ p * (p * p - 1) :=
        Nat.mul_le_mul hlt (Nat.sub_le_sub_right (Nat.mul_le_mul hlt hlt) 1)
      omega
    interval_cases p <;> omega

theorem tabIdentFor_hs
    : TabIdentFor (@Ident.FamSporadic .HS) := by
  refine tabIdentFor_hs_of ?_
  have : IsSimpleGroup ↥(commutator ↥HSAut.outerC) := HSAut.commutator_simple'
  have h : ¬ HasKComponent ↥HSAut.outerC := by
    refine not_hasKComponent_of_commutator_simple ?_
    rw [HSAut.card_commutator']
    exact not_kOrder_20160
  exact h

end CFSG.QuasithinUnique.Id2519.SporHS
