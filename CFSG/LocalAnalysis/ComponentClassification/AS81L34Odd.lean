module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag Matrix CFSG.LieType.Chevalley

section Matrices

variable {k : Type} [Field k]

theorem mem_projRad_of_sq_eq_one [Finite k] (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx : x ∈ projUnip k) (hx2 : x ^ 2 = 1) :
    x ∈ projRad k 0 ∨ x ∈ projRad k 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [sq, ← map_mul, unipU_mul, proj_unipU_eq_one_iff] at hx2
  have h2 := two_eq_zero_of_card hk
  have hab : a * b = 0 := by
    have := hx2.2.2
    linear_combination this - c * h2
  rcases mul_eq_zero.mp hab with ha | hb
  · right
    exact mem_projRad_one.2 ⟨b, c, by rw [ha]⟩
  · left
    exact mem_projRad_zero.2 ⟨a, c, by rw [hb]⟩

theorem eq_projRad_of_le_projUnip [Finite k] (hk : Nat.card k = 4) {H : Subgroup (projectiveSL 3 k)} (hHU : H ≤ projUnip k)
    (hH2 : ∀ x ∈ H, x ^ 2 = 1) (hH16 : Nat.card H = 16) :
    H = projRad k 0 ∨ H = projRad k 1 := by
  have hcard : ∀ i : Fin 2, Nat.card (projRad k i) = 16 := fun i => by
    rw [card_projRad, hk]
  have hcover : ∀ x ∈ H, x ∈ projRad k 0 ∨ x ∈ projRad k 1 := fun x hx =>
    mem_projRad_of_sq_eq_one hk (hHU hx) (hH2 x hx)
  by_cases h0 : H ≤ projRad k 0
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h0 (by rw [hcard, hH16]))
  by_cases h1 : H ≤ projRad k 1
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, hH16]))
  exfalso
  obtain ⟨x, hx, hx0⟩ := Set.not_subset.mp h0
  obtain ⟨y, hy, hy1⟩ := Set.not_subset.mp h1
  have hx1 : x ∈ projRad k 1 := (hcover x hx).resolve_left hx0
  have hy0 : y ∈ projRad k 0 := (hcover y hy).resolve_right hy1
  rcases hcover (x * y) (H.mul_mem hx hy) with hxy | hxy
  · apply hx0
    have := (projRad k 0).mul_mem hxy ((projRad k 0).inv_mem hy0)
    simpa using this
  · apply hy1
    have := (projRad k 1).mul_mem ((projRad k 1).inv_mem hx1) hxy
    simpa using this

theorem exists_mem_normalizer_conj_eq (i : Fin 2) {r s : projectiveSL 3 k}
    (hr : r ∈ projRad k i) (hs : s ∈ projRad k i) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ y ∈ normalizer (projRad k i : Set (projectiveSL 3 k)), y * r * y⁻¹ = s := by
  fin_cases i
  · obtain ⟨B, hB⟩ := projRad_zero_transitive hr hs hr1 hs1
    exact ⟨_, leviOne_mem_normalizer B, hB⟩
  · obtain ⟨B, hB⟩ := projRad_one_transitive hr hs hr1 hs1
    exact ⟨_, leviTwo_mem_normalizer B, hB⟩

@[expose] noncomputable def torusSL2 {t : k} (ht : t ≠ 0) : SL2 k :=
  ⟨!![t, 0; 0, t⁻¹], by rw [Matrix.det_fin_two_of]; field_simp; ring⟩

theorem coe_torusSL2 {t : k} (ht : t ≠ 0) :
    (torusSL2 ht : Matrix (Fin 2) (Fin 2) k) = !![t, 0; 0, t⁻¹] :=
  rfl

theorem levi_torus_conj (i : Fin 2) {t : k} (ht : t ≠ 0) (c : k) :
    proj 3 k (levi k i (torusSL2 ht)) * proj 3 k (unipU k 0 0 c) *
      (proj 3 k (levi k i (torusSL2 ht)))⁻¹ = proj 3 k (unipU k 0 0 (t * c)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  fin_cases i
  · change leviOne k _ * _ = _ * leviOne k _
    rw [leviOne_mul_unipU, coe_torusSL2]
    congr 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    congr 1 <;> ring
  · change leviTwo k _ * _ = _ * leviTwo k _
    rw [leviTwo_mul_unipU, coe_torusSL2]
    congr 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    congr 1 <;> ring

theorem exists_torus [Finite k] (hk : Nat.card k = 4) (i : Fin 2) :
    ∃ y ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) ⊓
      normalizer (projCenterW k : Set (projectiveSL 3 k)),
      ∀ w ∈ projCenterW k, y * w * y⁻¹ = w → w = 1 := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
  set y := proj 3 k (levi k i (torusSL2 ht0))
  have hyR : y ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
    fin_cases i
    · exact leviOne_mem_normalizer _
    · exact leviTwo_mem_normalizer _
  have hconj : ∀ s : k, ∀ (hs : s ≠ 0) (w : projectiveSL 3 k), w ∈ projCenterW k →
      proj 3 k (levi k i (torusSL2 hs)) * w * (proj 3 k (levi k i (torusSL2 hs)))⁻¹ ∈
        projCenterW k := by
    intro s hs w hw
    obtain ⟨c, rfl⟩ := mem_projCenterW.1 hw
    rw [levi_torus_conj]
    exact mem_projCenterW.2 ⟨_, rfl⟩
  have hinv : y⁻¹ = proj 3 k (levi k i (torusSL2 (inv_ne_zero ht0))) := by
    rw [← map_inv, ← map_inv]
    congr 2
    rw [eq_comm, eq_inv_iff_mul_eq_one]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [coe_torusSL2, Matrix.mul_apply, ht0]
  have hyW : y ∈ normalizer (projCenterW k : Set (projectiveSL 3 k)) := by
    refine mem_normalizer_of_conj_mem (fun w hw => hconj t ht0 w hw) fun w hw => ?_
    have := hconj _ (inv_ne_zero ht0) w hw
    rw [← hinv, inv_inv] at this
    exact this
  refine ⟨y, ⟨hyR, hyW⟩, fun w hw hfix => ?_⟩
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hw
  rw [levi_torus_conj] at hfix
  obtain ⟨-, -, hc⟩ := unipU_eq_of_proj_eq hfix
  have hc0 : c = 0 := by
    have h1 : (t - 1) * c = 0 := by linear_combination hc
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr ht1)
  rw [hc0, unipU_zero, map_one]

theorem projCenterW_le_center : projCenterW k ≤
    (center ↥(projUnip k)).map (projUnip k).subtype := by
  intro w hw
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hw
  have hwU : proj 3 k (unipU k 0 0 c) ∈ projUnip k := mem_projUnip.2 ⟨0, 0, c, rfl⟩
  refine ⟨⟨_, hwU⟩, mem_center_iff.mpr ?_, rfl⟩
  rintro ⟨x, hx⟩
  obtain ⟨a, b, c', rfl⟩ := mem_projUnip.1 hx
  apply Subtype.ext
  simp only [coe_mul]
  rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
  congr 2 <;> ring

theorem center_projUnip : (center ↥(projUnip k)).map (projUnip k).subtype = projCenterW k := by
  refine le_antisymm ?_ (projCenterW_le_center)
  rintro _ ⟨⟨x, hx⟩, hxZ, rfl⟩
  have h1 : proj 3 k (unipU k 1 0 0) ∈ projUnip k := mem_projUnip.2 ⟨1, 0, 0, rfl⟩
  have h2 : proj 3 k (unipU k 0 1 0) ∈ projUnip k := mem_projUnip.2 ⟨0, 1, 0, rfl⟩
  have hc1 := congrArg Subtype.val (mem_center_iff.mp hxZ ⟨_, h1⟩)
  have hc2 := congrArg Subtype.val (mem_center_iff.mp hxZ ⟨_, h2⟩)
  simp only [coe_mul] at hc1 hc2
  exact mem_projCenterW_of_commute hx hc1.symm hc2.symm

end Matrices

end CFSG.ComponentClassification.AS81
