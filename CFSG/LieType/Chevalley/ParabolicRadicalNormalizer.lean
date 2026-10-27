module

public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem xUnit_mem_parabolicRadical
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∉ J)
    (c : K) : xUnit τ K i c ∈ parabolicRadical τ K J := by
  rw [← pinnedX_single]
  refine pinnedX_mem_rootSpan ?_ c
  exact mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i, by rw [height_single]; exact one_pos,
    i, hi, by simp⟩

theorem weylElt_not_mem_normalizer_parabolicRadical
    {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∉ J) :
    weylElt τ K i 1 ∉ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) := by
  intro hn
  have hx := xUnit_mem_parabolicRadical (K := K) hi 1
  have hy := (Subgroup.mem_normalizer_iff.1 hn _).1 hx
  rw [weylElt_one_conj_xUnit] at hy
  have h1 : yUnit τ K i (-1) ∈ borelGroup τ K ⊓ negUnipotent τ K :=
    Subgroup.mem_inf.2 ⟨(le_sup_right : posUnipotent τ K ≤ borelGroup τ K)
      (parabolicRadical_le_posUnipotent J hy),
      yUnit_mem_negUnipotent i (-1)⟩
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at h1
  have hinj : Function.Injective (yUnit τ K i) := fun c d h =>
    yOp_injective i (by rw [← coe_yUnit, ← coe_yUnit, h])
  exact neg_ne_zero.2 one_ne_zero (hinj (h1.trans (yUnit_zero i).symm))

theorem adjointGroup_inf_normalizer_parabolicRadical
    (J : Set (Fin τ.rank)) :
    adjointGroup τ K ⊓ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) =
      parabolicSubgroup τ K J := by
  have hPN : parabolicSubgroup τ K J ≤
      adjointGroup τ K ⊓ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    le_inf (parabolicSubgroup_le_adjointGroup τ K J)
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  refine le_antisymm ?_ hPN
  have hB : borelGroup τ K ≤
      adjointGroup τ K ⊓ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    (le_sup_left : borelGroup τ K ≤ parabolicSubgroup τ K J).trans hPN
  rw [eq_parabolicSubgroup_of_borelGroup_le hB inf_le_left]
  refine sup_le le_sup_left ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, hi, rfl⟩
  by_contra hiJ
  rw [SetLike.mem_coe, weylElt_mem_parabolicSubgroup_iff] at hiJ
  exact weylElt_not_mem_normalizer_parabolicRadical hiJ (Subgroup.mem_inf.1 hi).2

theorem Chevalley_Borel_overgroups_and_radical_normalizers
    (τ : Tag) (K : Type) [Field K] :
    (∀ A : Subgroup (ModGL τ K), borelGroup τ K ≤ A → A ≤ adjointGroup τ K →
      (∃! J : Set (Fin τ.rank), A = parabolicSubgroup τ K J) ∧
        A = parabolicSubgroup τ K {i | weylElt τ K i 1 ∈ A}) ∧
    ∀ J : Set (Fin τ.rank),
      adjointGroup τ K ⊓ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) =
        parabolicSubgroup τ K J :=
  ⟨fun A hB hA => ⟨(borel_overgroup_classification τ K).2 A hB hA,
    (borel_overgroup_classification τ K).1 A hB hA⟩,
    adjointGroup_inf_normalizer_parabolicRadical⟩

end CFSG.LieType.Chevalley
