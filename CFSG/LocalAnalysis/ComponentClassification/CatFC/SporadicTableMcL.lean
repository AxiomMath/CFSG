module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section McLRow


theorem sporadic_rows_mcl {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .McL)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .McL (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .McL (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 20160) (fun u hu B hB => ?_), fun hout => ?_⟩
  · obtain ⟨θ⟩ := ComponentClassification.RestrictedStd.Spor.mcl_inner_comps e u hu B hB
    rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
  · obtain ⟨B, hB, hcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
    rw [← hcard]
    exact ComponentClassification.RestrictedStd.Spor.mcl_outer_comps e σ
      (mul_self_eq_one_of_orderOf_eq_two' hσ) hout B hB

end McLRow

end CFSG.ComponentClassification.CatFC
