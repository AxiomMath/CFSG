module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (mcl_inner_comps mcl_outer_comps
  mclX_order_six)

section McL


theorem mcl_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.McL) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 2) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _
        (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
      exact hσ
    let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
    obtain ⟨ψ⟩ := mcl_inner_comps e s hs _ (LocalCores.isComponent_map_mulEquiv φ hD)
    obtain ⟨z, hz, hz6⟩ := mclX_order_six
    exact not_lieModel_psl_three_two_of_mulEquiv_orderOf_six ψ (y := ⟨z, hz⟩)
      (by rw [Subgroup.orderOf_mk, hz6]) (lieModel_map_of_mulEquiv φ hDm)
  · have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix
    have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 7920 :=
      mcl_outer_comps e σ (by rw [← sq, ← hσ, pow_orderOf_eq_one]) hin _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    have hc := LinearPilot.card_of_lieModel_PSL_two (lieModel_map_of_mulEquiv φ hDm)
    rw [h] at hc
    revert hc
    decide

end McL

end CFSG.SeitzReduction.SporadicRefine
