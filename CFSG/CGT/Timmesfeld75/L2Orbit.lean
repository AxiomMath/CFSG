module

public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Matrix

variable {F : Type} [Field F]

theorem exists_utri_mul_wElt_mul_borel {g : SL(2, F)} (hg : g ∉ borel F) :
    ∃ u ∈ utri F, ∃ b ∈ borel F, g = u * wElt * b := by
  have hc : g 1 0 ≠ 0 := hg
  refine ⟨utriElt (g 0 0 / g 1 0), utriElt_mem_utri _,
    utriElt (g 1 1 * g 1 0) * torusElt (Units.mk0 (g 1 0) hc),
    Subgroup.mul_mem _ (utri_le_borel (utriElt_mem_utri _)) (torusElt_mem_borel _), ?_⟩
  have hd := sl2_det g
  apply sl2_ext
  all_goals sl2_simp
  all_goals simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  · field_simp
    ring
  · field_simp
    linear_combination (-(g 1 0)) * hd
  · ring
  · field_simp
    ring

theorem exists_mem_utri_conj_eq_ltri {g : SL(2, F)} (hg : g ∉ borel F) :
    ∃ u ∈ utri F, conjSubgroup g (utri F) = conjSubgroup u (ltri F) := by
  obtain ⟨u, hu, b, hb, rfl⟩ := exists_utri_mul_wElt_mul_borel hg
  refine ⟨u, hu, ?_⟩
  have hbU : conjSubgroup b (utri F) = utri F :=
    mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact hb)
  rw [← conjSubgroup_conjSubgroup, ← conjSubgroup_conjSubgroup, hbU, conjSubgroup_wElt_utri]

theorem exists_mem_utri_conj_eq {g g' : SL(2, F)} (hg : g ∉ borel F) (hg' : g' ∉ borel F) :
    ∃ u ∈ utri F, conjSubgroup g' (utri F) = conjSubgroup u (conjSubgroup g (utri F)) := by
  obtain ⟨u₁, hu₁, h₁⟩ := exists_mem_utri_conj_eq_ltri hg
  obtain ⟨u₂, hu₂, h₂⟩ := exists_mem_utri_conj_eq_ltri hg'
  refine ⟨u₂ * u₁⁻¹, Subgroup.mul_mem _ hu₂ (Subgroup.inv_mem _ hu₁), ?_⟩
  rw [h₁, h₂, conjSubgroup_conjSubgroup]
  congr 1
  group

end Matrix

namespace IsL2Pair

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem exists_mem_conj_eq (h : IsL2Pair X S q) {a b : X}
    (ha : conjSubgroup a S ≠ S) (hb : conjSubgroup b S ≠ S) :
    ∃ s ∈ S, conjSubgroup b S = conjSubgroup s (conjSubgroup a S) := by
  obtain ⟨F, i1, i2, i3, e, -, hS, -, hmemS, hmemN⟩ := h.exists_data
  have hna : e a ∉ borel F := fun hh => ha (mem_normalizer_iff_conjSubgroup_eq.1 ((hmemN a).2 hh))
  have hnb : e b ∉ borel F := fun hh => hb (mem_normalizer_iff_conjSubgroup_eq.1 ((hmemN b).2 hh))
  obtain ⟨u, hu, hconj⟩ := exists_mem_utri_conj_eq hna hnb
  refine ⟨e.symm u, (hmemS _).2 (by rw [e.apply_symm_apply]; exact hu), ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS,
    e.apply_symm_apply]
  exact hconj

end IsL2Pair

end CFSG.CGT.Timmesfeld75
