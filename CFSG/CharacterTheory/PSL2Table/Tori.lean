module

public import CFSG.CharacterTheory.PSL2Table.Conjugacy

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mk_conj (M A : SL(2, F)) : mk M * mk A * (mk M)⁻¹ = mk (M * A * M⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem exists_mk_eq (g : PSL(2, F)) : ∃ M : SL(2, F), mk M = g := mk_surjective g

theorem mem_splitTorus_iff_exists (x : PSL(2, F)) :
    x ∈ splitTorus F ↔ ∃ a : Fˣ, x = mk (diag a) := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨a, rfl⟩ := exists_diag_of_mem_splitSL hA
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨diag a, diag_mem_splitSL a, rfl⟩

theorem mk_diag_eq_one_iff (a : Fˣ) : mk (diag a) = 1 ↔ (a : F) ^ 2 = 1 := by
  rw [mk_eq_one_iff, diag_eq_one_or_neg_one_iff]

theorem splitTorus_mul_comm {x y : PSL(2, F)} (hx : x ∈ splitTorus F) (hy : y ∈ splitTorus F) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists x).mp hx
  obtain ⟨b, rfl⟩ := (mem_splitTorus_iff_exists y).mp hy
  rw [← map_mul, ← map_mul, ← diag_mul, ← diag_mul, mul_comm]

@[expose] def splitWeyl (F : Type) [Field F] : PSL(2, F) := mk weyl

theorem splitWeyl_conj {x : PSL(2, F)} (hx : x ∈ splitTorus F) :
    splitWeyl F * x * (splitWeyl F)⁻¹ = x⁻¹ := by
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists x).mp hx
  rw [splitWeyl, mk_conj, weyl_conj_diag, ← diag_inv, map_inv]

theorem splitWeyl_not_mem : splitWeyl F ∉ splitTorus F := by
  rw [splitWeyl, mk_mem_splitTorus_iff]
  exact weyl_not_mem_splitSL

theorem splitWeyl_mul_self : splitWeyl F * splitWeyl F = 1 := by
  rw [splitWeyl, ← map_mul, weyl_sq, mk_neg, map_one]

theorem splitTorus_conj_mem_iff {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1)
    (g : PSL(2, F)) :
    g * x * g⁻¹ ∈ splitTorus F ↔ g ∈ splitTorus F ∨ (splitWeyl F)⁻¹ * g ∈ splitTorus F := by
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists x).mp hx
  have ha : (a : F) ^ 2 ≠ 1 := fun h => hx1 ((mk_diag_eq_one_iff a).mpr h)
  obtain ⟨M, rfl⟩ := exists_mk_eq g
  rw [mk_conj, mk_mem_splitTorus_iff, conj_diag_mem_splitSL_iff ha, splitWeyl, ← map_inv,
    ← map_mul, mk_mem_splitTorus_iff, mk_mem_splitTorus_iff]
  constructor
  · rintro (h | ⟨h0, h1⟩)
    · exact Or.inl h
    · exact Or.inr (weyl_inv_mul_mem_splitSL h0 h1)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (mem_splitSL_of_weyl_inv_mul h)

theorem nonsplitTorus_mul_comm {ν : F} {x y : PSL(2, F)} (hx : x ∈ nonsplitTorus ν)
    (hy : y ∈ nonsplitTorus ν) : x * y = y * x := by
  obtain ⟨A, ⟨hA1, hA2⟩, rfl⟩ := hx
  obtain ⟨B, ⟨hB1, hB2⟩, rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply SL_ext <;> simp only [mul_apply_SL, hA1, hA2, hB1, hB2] <;> ring

theorem exists_of_mem_nonsplitTorus {ν : F} {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν)
    (hx1 : x ≠ 1) : ∃ C : SL(2, F), C ∈ nonsplitSL ν ∧
      (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∧ x = mk C := by
  obtain ⟨C, hC, rfl⟩ := hx
  refine ⟨C, hC, fun hy => hx1 ?_, rfl⟩
  rw [mk_eq_one_iff]
  exact eq_one_or_neg_one_of_mem_nonsplitSL hC hy

variable [Fintype F]

theorem exists_nonsplitWeyl (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    ∃ w : PSL(2, F), w ∉ nonsplitTorus ν ∧ w * w = 1 ∧
      (∀ x ∈ nonsplitTorus ν, w * x * w⁻¹ = x⁻¹) ∧
      ∀ x ∈ nonsplitTorus ν, x ≠ 1 → ∀ g : PSL(2, F),
        g * x * g⁻¹ ∈ nonsplitTorus ν ↔ g ∈ nonsplitTorus ν ∨ w⁻¹ * g ∈ nonsplitTorus ν := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  obtain ⟨W, hW⟩ := exists_antiNS hF hν0
  refine ⟨mk W, ?_, ?_, ?_, ?_⟩
  · rw [mk_mem_nonsplitTorus_iff]
    exact antiNS_not_mem h2 hW hν0
  ·
    have hconj := antiNS_conj hW (nonsplitSL ν).one_mem
    obtain ⟨hW1, hW2⟩ := hW
    have hdet := det_entries W
    rw [hW1, hW2] at hdet
    rw [← map_mul]
    rw [mk_eq_one_iff]
    right
    apply SL_ext <;> simp only [mul_apply_SL, neg_apply_SL, hW1, hW2,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, neg_zero]
    · linear_combination -hdet
    · ring
    · ring
    · linear_combination -hdet
  · rintro x ⟨C, hC, rfl⟩
    rw [mk_conj, antiNS_conj hW hC, map_inv]
  · intro x hx hx1 g
    obtain ⟨C, hC, hy, rfl⟩ := exists_of_mem_nonsplitTorus hx hx1
    obtain ⟨M, rfl⟩ := exists_mk_eq g
    rw [mk_conj, mk_mem_nonsplitTorus_iff, conj_mem_nonsplitSL_iff h2 hν hC hy, ← map_inv,
      ← map_mul, mk_mem_nonsplitTorus_iff, mk_mem_nonsplitTorus_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (inv_mul_mem_of_antiNS hW h)
    · rintro (h | h)
      · exact Or.inl h
      · right
        have := antiNS_mul_mem hW h
        rwa [mul_inv_cancel_left] at this

section Unipotent

variable {F : Type} [Field F]

theorem mk_unip_eq_mk_unip_iff (h2 : (2 : F) ≠ 0) (s t : F) :
    mk (unip s) = mk (unip t) ↔ s = t := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simpa using h01.symm
    · have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp only [coe_unip, neg_apply_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h00
      exact (h2 (by linear_combination h00)).elim
  · rintro rfl
    exact Or.inl rfl

theorem mk_unip_eq_one_iff (h2 : (2 : F) ≠ 0) (t : F) : mk (unip t) = 1 ↔ t = 0 := by
  rw [← mk_unip_eq_mk_unip_iff h2 t 0, unip_zero, map_one]

theorem mem_unipotent_iff_exists (x : PSL(2, F)) :
    x ∈ unipotent F ↔ ∃ t : F, x = mk (unip t) := by
  constructor
  · rintro ⟨A, ⟨h10, h00, h11⟩, rfl⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    congr 1
    apply SL_ext <;> simp [h10, h00, h11]
  · rintro ⟨t, rfl⟩
    exact ⟨unip t, unip_mem_unipSL t, rfl⟩

theorem unipotent_mul_comm {x y : PSL(2, F)} (hx : x ∈ unipotent F) (hy : y ∈ unipotent F) :
    x * y = y * x := by
  obtain ⟨s, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists y).mp hy
  rw [← map_mul, ← map_mul, ← unip_add, ← unip_add, add_comm]

theorem unipotent_conj_mem_iff (h2 : (2 : F) ≠ 0) {x : PSL(2, F)} (hx : x ∈ unipotent F)
    (hx1 : x ≠ 1) (g : PSL(2, F)) : g * x * g⁻¹ ∈ unipotent F ↔ g ∈ borel F := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff h2 t).mpr h)
  obtain ⟨M, rfl⟩ := exists_mk_eq g
  rw [mk_conj, mk_mem_unipotent_iff, mk_mem_borel_iff, mem_borelSL_iff, conj_unip_apply_10,
    conj_unip_apply_00, conj_unip_apply_11]
  constructor
  · rintro ⟨h, -⟩
    have : (M : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 * t = 0 := neg_eq_zero.mp h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp this).resolve_right ht)
  · intro h
    rw [h]
    simp

theorem borel_conj_unip {g : PSL(2, F)} (hg : g ∈ borel F) (t : F) :
    ∃ a : Fˣ, g * mk (unip t) * g⁻¹ = mk (unip ((a : F) ^ 2 * t)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  have hdet := det_entries M
  have hM : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mem_borelSL_iff M).mp hM
  rw [hM, mul_zero, sub_zero] at hdet
  have h0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ h0, ?_⟩
  rw [mk_conj, conj_unip_of_borel hM, Units.val_mk0]

theorem isConj_unip_iff (h2 : (2 : F) ≠ 0) {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    IsConj (mk (unip s)) (mk (unip t)) ↔ IsSquare (s * t) := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hmem : g * mk (unip s) * g⁻¹ ∈ unipotent F := by
      rw [hg]
      exact ⟨unip t, unip_mem_unipSL t, rfl⟩
    have hs1 : mk (unip s) ≠ 1 := fun h => hs ((mk_unip_eq_one_iff h2 s).mp h)
    have hgB := (unipotent_conj_mem_iff h2 ⟨unip s, unip_mem_unipSL s, rfl⟩ hs1 g).mp hmem
    obtain ⟨a, ha⟩ := borel_conj_unip hgB s
    rw [hg, mk_unip_eq_mk_unip_iff h2] at ha
    exact ⟨(a : F) * s, by rw [ha]; ring⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact mul_ne_zero hs ht hc
    refine ⟨mk (diag (Units.mk0 (t / c) (div_ne_zero ht hc0))), ?_⟩
    rw [mk_conj, diag_conj_unip, Units.val_mk0]
    congr 2
    field_simp
    linear_combination hc

theorem centralizer_mk_unip (h2 : (2 : F) ≠ 0) {t : F} (ht : t ≠ 0) :
    Subgroup.centralizer {mk (unip t)} = unipotent F := by
  have hx : mk (unip t) ∈ unipotent F := ⟨unip t, unip_mem_unipSL t, rfl⟩
  have hx1 : mk (unip t) ≠ 1 := fun h => ht ((mk_unip_eq_one_iff h2 t).mp h)
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hcomm
    have hconj : g * mk (unip t) * g⁻¹ = mk (unip t) := by
      rw [hcomm, mul_inv_cancel_right]
    have hgB : g ∈ borel F := (unipotent_conj_mem_iff h2 hx hx1 g).mp (by rw [hconj]; exact hx)
    obtain ⟨M, hM, rfl⟩ := hgB
    have hM : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (mem_borelSL_iff M).mp hM
    rw [mk_conj, conj_unip_of_borel hM, mk_unip_eq_mk_unip_iff h2] at hconj
    have hsq : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1 := by
      have : ((M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 - 1) * t = 0 := by
        linear_combination hconj
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ht)
    have hdet := det_entries M
    rw [hM, mul_zero, sub_zero] at hdet
    rw [mk_mem_unipotent_iff]
    refine ⟨hM, ?_⟩
    rw [sq] at hsq
    have h0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * ((M : Matrix (Fin 2) (Fin 2) F) 0 0 -
        (M : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination hsq - hdet
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h0)
  · intro hg
    exact unipotent_mul_comm hg hx

end Unipotent

end CFSG.PSL2Table
