module

public import CFSG.CharacterTheory.PSL2Table.Conjugacy
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {F : Type} [Field F]

abbrev ProjLine (F : Type) [Field F] := ℙ F (Fin 2 → F)

theorem mk_smul_proj (A : SL(2, F)) (v : Fin 2 → F) (hv : v ≠ 0) :
    mk A • Projectivization.mk F v hv =
      Projectivization.mk F ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
        (fun h => hv ((smul_eq_zero_iff_eq A).mp h)) := by
  change ((QuotientGroup.mk A : PSL(2, F))) • _ = _
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk]
  rfl

theorem mk_smul_proj_eq_iff (A : SL(2, F)) (v : Fin 2 → F) (hv : v ≠ 0) :
    mk A • Projectivization.mk F v hv = Projectivization.mk F v hv ↔
      ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) 0 0 * v 0 + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * v 1 =
          c * v 0 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 * v 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * v 1 =
          c * v 1 := by
  rw [mk_smul_proj, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · have := congrFun ha 0
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      exact this.symm
    · have := congrFun ha 1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      exact this.symm
  · rintro ⟨c, h0, h1⟩
    refine ⟨c, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact h0.symm
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact h1.symm

theorem e0_ne_zero : (![1, 0] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem e1_ne_zero : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

@[expose] def lineZero (F : Type) [Field F] : ProjLine F := Projectivization.mk F ![1, 0] e0_ne_zero

@[expose] def lineOne (F : Type) [Field F] : ProjLine F := Projectivization.mk F ![0, 1] e1_ne_zero

theorem mk_eq_lineZero_iff (v : Fin 2 → F) (hv : v ≠ 0) :
    Projectivization.mk F v hv = lineZero F ↔ v 1 = 0 := by
  rw [lineZero, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [h]

theorem mk_eq_lineOne_iff (v : Fin 2 → F) (hv : v ≠ 0) :
    Projectivization.mk F v hv = lineOne F ↔ v 0 = 0 := by
  rw [lineOne, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    refine ⟨v 1, ?_⟩
    funext i
    fin_cases i <;> simp [h]

theorem lineZero_ne_lineOne : lineZero F ≠ lineOne F := by
  intro h
  rw [lineZero, mk_eq_lineOne_iff] at h
  simp at h

theorem fixedBy_unip {t : F} (ht : t ≠ 0) :
    MulAction.fixedBy (ProjLine F) (mk (unip t)) = {lineZero F} := by
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
  rw [MulAction.mem_fixedBy, Set.mem_singleton_iff, mk_smul_proj_eq_iff, mk_eq_lineZero_iff]
  simp only [coe_unip, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, zero_mul,
    zero_add]
  constructor
  · rintro ⟨c, h0, h1⟩
    by_contra hv1
    have hc : c = 1 := by
      have : (c - 1) * v 1 = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hv1)
    subst hc
    have : t * v 1 = 0 := by linear_combination h0
    exact hv1 ((mul_eq_zero.mp this).resolve_left ht)
  · intro h
    exact ⟨1, by rw [h]; ring, by rw [h]; ring⟩

theorem fixedBy_diag {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) :
    MulAction.fixedBy (ProjLine F) (mk (diag a)) = {lineZero F, lineOne F} := by
  have hd := inv_ne_self_of_sq_ne_one ha
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
  rw [MulAction.mem_fixedBy, Set.mem_insert_iff, Set.mem_singleton_iff, mk_smul_proj_eq_iff,
    mk_eq_lineZero_iff, mk_eq_lineOne_iff]
  simp only [coe_diag, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, add_zero,
    zero_add]
  constructor
  · rintro ⟨c, h0, h1⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hv1, hv0⟩ := hcon
    have hc0 : c = a := by
      have : ((a : F) - c) * v 0 = 0 := by linear_combination h0
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hv0)).symm
    have hc1 : c = (a : F)⁻¹ := by
      have : ((a : F)⁻¹ - c) * v 1 = 0 := by linear_combination h1
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hv1)).symm
    exact hd (by rw [← hc1, ← hc0, sub_self])
  · rintro (h | h)
    · exact ⟨a, rfl, by rw [h]; ring⟩
    · exact ⟨(a : F)⁻¹, by rw [h]; ring, rfl⟩

theorem fixedBy_nonsplit {ν : F} (hν : ¬ IsSquare ν) {C : SL(2, F)} (hC : C ∈ nonsplitSL ν)
    (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    MulAction.fixedBy (ProjLine F) (mk C) = ∅ := by
  obtain ⟨hC1, hC2⟩ := hC
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
  rw [MulAction.mem_fixedBy, mk_smul_proj_eq_iff, hC1, hC2]
  simp only [Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro c h0 h1
  set x := (C : Matrix (Fin 2) (Fin 2) F) 0 0
  set y := (C : Matrix (Fin 2) (Fin 2) F) 1 0
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      funext i
      fin_cases i
      · exact hv0
      · exact hv1
    rw [hv0] at h0
    have : (ν * y) * v 1 = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact mul_ne_zero (ne_zero_of_not_isSquare hν) hy h
    · exact hv1 h
  · have e0 : (c - x) * v 0 = ν * y * v 1 := by linear_combination -h0
    have e1 : (c - x) * v 1 = y * v 0 := by linear_combination -h1
    have hv1 : v 1 ≠ 0 := by
      intro hv1
      rw [hv1, mul_zero] at e1
      exact mul_ne_zero hy hv0 e1.symm
    have key : (c - x) ^ 2 * (v 0 * v 1) = ν * y ^ 2 * (v 0 * v 1) := by
      linear_combination (c - x) * v 1 * e0 + ν * y * v 1 * e1
    have key' : (c - x) ^ 2 = ν * y ^ 2 :=
      mul_right_cancel₀ (mul_ne_zero hv0 hv1) key
    apply hν
    refine ⟨(c - x) / y, ?_⟩
    field_simp
    linear_combination -key'

theorem card_fixedBy_unip {t : F} (ht : t ≠ 0) :
    Nat.card (MulAction.fixedBy (ProjLine F) (mk (unip t))) = 1 := by
  rw [fixedBy_unip ht, Nat.card_unique]

theorem card_fixedBy_diag {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) :
    Nat.card (MulAction.fixedBy (ProjLine F) (mk (diag a))) = 2 := by
  rw [fixedBy_diag ha, Nat.card_coe_set_eq, Set.ncard_pair lineZero_ne_lineOne]

theorem card_fixedBy_nonsplit {ν : F} (hν : ¬ IsSquare ν) {C : SL(2, F)}
    (hC : C ∈ nonsplitSL ν) (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    Nat.card (MulAction.fixedBy (ProjLine F) (mk C)) = 0 := by
  rw [fixedBy_nonsplit hν hC hy]
  simp

theorem card_projLine [Finite F] : Nat.card (ProjLine F) = Nat.card F + 1 :=
  Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)

theorem card_fixedBy_one [Finite F] :
    Nat.card (MulAction.fixedBy (ProjLine F) (1 : PSL(2, F))) = Nat.card F + 1 := by
  rw [MulAction.fixedBy_one_eq_univ, Nat.card_coe_set_eq, Set.ncard_univ, card_projLine]

end CFSG.PSL2Table
