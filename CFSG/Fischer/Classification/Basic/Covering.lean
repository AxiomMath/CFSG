module

public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem Pair.conj_mem_closure_diff (hP : Pair X E) (U : Subgroup X) {u : X} (hu : u ∈ U)
    {w : X} (hw : w ∈ Subgroup.closure (E \ U)) : u * w * u⁻¹ ∈ Subgroup.closure (E \ U) := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    refine Subgroup.subset_closure ⟨Pair.conj_mem hP hs.1 u, fun h => hs.2 ?_⟩
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) h) hu
    rwa [show u⁻¹ * (u * s * u⁻¹) * u = s by group] at this
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show u * (a * b) * u⁻¹ = u * a * u⁻¹ * (u * b * u⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

theorem Pair.eq_top_or_eq_top_of_cover (hP : Pair X E) (U V : Subgroup X)
    (h : ∀ e ∈ E, e ∈ U ∨ e ∈ V) : U = ⊤ ∨ V = ⊤ := by
  by_cases hEU : E ⊆ U
  · left
    rw [eq_top_iff, ← Pair.closure_eq hP]
    exact (Subgroup.closure_le _).2 hEU
  right
  obtain ⟨e₀, he₀, he₀U⟩ := Set.not_subset.1 hEU
  set W := Subgroup.closure (E \ U)
  have hWV : W ≤ V := (Subgroup.closure_le _).2 fun f hf => (h f hf.1).resolve_left hf.2
  have hWn : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← Pair.closure_eq hP]
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    by_cases hsU : s ∈ U
    · refine Subgroup.mem_normalizer_iff.2 fun w => ⟨Pair.conj_mem_closure_diff hP U hsU, ?_⟩
      intro hw
      have := Pair.conj_mem_closure_diff hP U (U.inv_mem hsU) hw
      rwa [show s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ = w by group] at this
    · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨hs, hsU⟩)
  have hEW : E ⊆ W := fun f hf => by
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP he₀ hf)
    exact hWn.conj_mem e₀ (Subgroup.subset_closure ⟨he₀, he₀U⟩) g
  rw [eq_top_iff, ← Pair.closure_eq hP]
  exact ((Subgroup.closure_le _).2 hEW).trans hWV

end CFSG.Fischer.Classification
