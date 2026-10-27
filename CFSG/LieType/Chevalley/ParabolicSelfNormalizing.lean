module

public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.RankOneCentralImage

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem adjointGroup_inf_normalizer_parabolicSubgroup (J : Set (Fin τ.rank)) :
    adjointGroup τ K ⊓ Subgroup.normalizer (parabolicSubgroup τ K J : Set (ModGL τ K)) =
      parabolicSubgroup τ K J := by
  have hPN : parabolicSubgroup τ K J ≤
      adjointGroup τ K ⊓ Subgroup.normalizer (parabolicSubgroup τ K J : Set (ModGL τ K)) :=
    le_inf (parabolicSubgroup_le_adjointGroup τ K J) Subgroup.le_normalizer
  refine le_antisymm ?_ hPN
  have hB : borelGroup τ K ≤
      adjointGroup τ K ⊓ Subgroup.normalizer (parabolicSubgroup τ K J : Set (ModGL τ K)) :=
    (le_sup_left : borelGroup τ K ≤ parabolicSubgroup τ K J).trans hPN
  rw [eq_parabolicSubgroup_of_borelGroup_le hB inf_le_left]
  refine sup_le le_sup_left ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, hi, rfl⟩
  change weylElt τ K i 1 ∈ parabolicSubgroup τ K J
  have hnorm : weylElt τ K i 1 ∈
      Subgroup.normalizer (parabolicSubgroup τ K J : Set (ModGL τ K)) := (Subgroup.mem_inf.1 hi).2
  have hx : xUnit τ K i 1 ∈ parabolicSubgroup τ K J :=
    borelGroup_le_parabolicSubgroup J (Subgroup.mem_sup_right (xUnit_mem_posUnipotent i 1))
  have hy : yUnit τ K i (-1) ∈ parabolicSubgroup τ K J := by
    have h := (Subgroup.mem_normalizer_iff.1 hnorm (xUnit τ K i 1)).1 hx
    rwa [weylElt_one_conj_xUnit] at h
  rw [weylElt_eq_yUnit_mul]
  exact mul_mem (mul_mem hy hx) hy

end CFSG.LieType.Chevalley
