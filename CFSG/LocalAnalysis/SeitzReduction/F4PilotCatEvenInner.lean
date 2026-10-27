module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf

theorem fixedSubgroup_conj {S : Type*} [Group S] (t : S) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set S) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change t * x * t⁻¹ = x ↔ x * t = t * x
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem false_of_isComponent_fixedSubgroup_inner {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hfree : InvolutionCentralizersComponentFree S)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hin : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  obtain ⟨t, rfl⟩ := hin
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) t]
    exact hσ
  exact hfree t ht _ (isComponent_map_mulEquiv (MulEquiv.subgroupCongr (fixedSubgroup_conj t)) hD)

theorem catSp6EvenInner :
    CatSp6EvenInner := by
  intro S _ _ hS hna heven σ hσ hin f D hD _
  have := hS
  exact false_of_isComponent_fixedSubgroup_inner hna
    (involutionCentralizersComponentFree_of_evenLieType heven) hσ hin hD

end CFSG.SeitzReduction.F4Pilot
