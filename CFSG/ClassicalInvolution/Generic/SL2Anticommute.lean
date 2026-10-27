module

public import CFSG.ClassicalInvolution.GenericLocal.WLemma

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F]

theorem sl_ext {s t : SL(2, F)} (h : (s : Matrix (Fin 2) (Fin 2) F) = t) : s = t :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

private def elemU : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def elemL : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem exists_scalar_of_comm_sl2 (B : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ s : SL(2, F), B * (s : Matrix (Fin 2) (Fin 2) F) = (s : Matrix (Fin 2) (Fin 2) F) * B) :
    ∃ c : F, B = Matrix.scalar (Fin 2) c := by
  have hU := h elemU
  have hL := h elemL
  have e1 := congrFun (congrFun hU 0) 0
  have e2 := congrFun (congrFun hU 0) 1
  have e3 := congrFun (congrFun hL 0) 0
  have e4 := congrFun (congrFun hL 0) 1
  simp [elemU, elemL, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3 e4
  refine ⟨B 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> grind

theorem slConj_eq_iff (A : GL (Fin 2) F) (s t : SL(2, F)) :
    slConjugation 2 F A s = t ↔
      A.val * (s : Matrix (Fin 2) (Fin 2) F) = (t : Matrix (Fin 2) (Fin 2) F) * A.val := by
  constructor
  · intro h
    have h' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h
    simp only [slConjugation_matrix] at h'
    rw [← h', Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · intro h
    apply sl_ext
    rw [slConjugation_matrix, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem coe_mul_neg_one (w : SL(2, F)) :
    ((w * (-1) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -(w : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, mul_neg, mul_one]

theorem mul_neg_one_comm (w : SL(2, F)) : w * (-1) = (-1) * w := by
  apply sl_ext
  rw [coe_mul_neg_one, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, neg_mul, one_mul]

theorem neg_one_inv : ((-1 : SL(2, F)))⁻¹ = -1 := by
  apply inv_eq_of_mul_eq_one_right
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, neg_mul, mul_neg, neg_neg, one_mul]

theorem centralizer_form_aux {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b e : F)
    (hnsc : ¬ (b = 0 ∧ e = 0 ∧ a = 0))
    (M : Matrix (Fin 2) (Fin 2) F)
    (hM : (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) * M = M * !![a, b; e, -a]) :
    ∃ x y : F, M = x • (1 : Matrix (Fin 2) (Fin 2) F) + y • (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have E1 : b * M 1 0 = M 0 1 * e := by linear_combination e00
  have E2 : 2 * a * M 0 1 = b * (M 0 0 - M 1 1) := by linear_combination e01
  have E3 : e * (M 0 0 - M 1 1) = 2 * a * M 1 0 := by linear_combination e10
  by_cases hb : b = 0
  · by_cases he : e = 0
    · have ha : a ≠ 0 := fun ha => hnsc ⟨hb, he, ha⟩
      have hq : M 0 1 = 0 := by
        have : 2 * a * M 0 1 = 0 := by rw [E2, hb]; ring
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 ha)
      have hr : M 1 0 = 0 := by
        have : 2 * a * M 1 0 = 0 := by rw [← E3, he]; ring
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 ha)
      refine ⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / (2 * a), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hb, he]; field_simp; ring
      · simp [hb, he, hq]
      · simp [hb, he, hr]
      · simp [hb, he]; field_simp; ring
    · have hq : M 0 1 = 0 := by
        have : M 0 1 * e = 0 := by rw [← E1, hb]; ring
        exact (mul_eq_zero.mp this).resolve_right he
      refine ⟨M 0 0 - M 1 0 / e * a, M 1 0 / e, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp [hb, hq]
      · simp; field_simp
      · simp; field_simp; linear_combination (-1 : F) * E3
  · refine ⟨M 0 0 - M 0 1 / b * a, M 0 1 / b, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp; field_simp
    · simp; field_simp; linear_combination E1
    · simp; field_simp; linear_combination E2

structure IsInvolDiag (A : GL (Fin 2) F) : Prop where
  sq : ∀ s : SL(2, F), slConjugation 2 F A (slConjugation 2 F A s) = s
  ne : ∃ s : SL(2, F), slConjugation 2 F A s ≠ s

namespace IsInvolDiag

variable {A : GL (Fin 2) F}

theorem sq_scalar (h : IsInvolDiag A) :
    ∃ c : F, c ≠ 0 ∧ A.val * A.val = Matrix.scalar (Fin 2) c := by
  have hcomm : ∀ s : SL(2, F), (A.val * A.val) * (s : Matrix (Fin 2) (Fin 2) F) =
      (s : Matrix (Fin 2) (Fin 2) F) * (A.val * A.val) := by
    intro s
    have h1 := (slConj_eq_iff A s (slConjugation 2 F A s)).mp rfl
    have h2 := (slConj_eq_iff A (slConjugation 2 F A s) s).mp (h.sq s)
    calc A.val * A.val * (s : Matrix (Fin 2) (Fin 2) F)
        = A.val * (A.val * (s : Matrix (Fin 2) (Fin 2) F)) := Matrix.mul_assoc _ _ _
      _ = A.val * ((slConjugation 2 F A s : Matrix (Fin 2) (Fin 2) F) * A.val) := by rw [h1]
      _ = (A.val * (slConjugation 2 F A s : Matrix (Fin 2) (Fin 2) F)) * A.val :=
          (Matrix.mul_assoc _ _ _).symm
      _ = ((s : Matrix (Fin 2) (Fin 2) F) * A.val) * A.val := by rw [h2]
      _ = (s : Matrix (Fin 2) (Fin 2) F) * (A.val * A.val) := Matrix.mul_assoc _ _ _
  obtain ⟨c, hc⟩ := exists_scalar_of_comm_sl2 _ hcomm
  refine ⟨c, ?_, hc⟩
  rintro rfl
  have h0 : A.val * A.val = 0 := by rw [hc]; simp
  have h1 : (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have hu : (A * A * (A⁻¹ * A⁻¹) : (Matrix (Fin 2) (Fin 2) F)ˣ) = 1 := by group
    have hv := congrArg Units.val hu
    rw [Units.val_mul, Units.val_mul, Units.val_mul, h0, Matrix.zero_mul] at hv
    exact hv.symm
  exact one_ne_zero (congrFun (congrFun h1 0) 0)

theorem not_scalar (h : IsInvolDiag A) (k : F) : A.val ≠ Matrix.scalar (Fin 2) k := by
  intro hk
  obtain ⟨s, hs⟩ := h.ne
  apply hs
  rw [slConj_eq_iff, hk]
  exact (Matrix.scalar_commute k (fun _ => Commute.all _ _) _).eq

theorem entries (h : IsInvolDiag A) :
    ∃ a b e c : F, c ≠ 0 ∧ A.val = !![a, b; e, -a] ∧ a ^ 2 + b * e = c ∧
      A.val * A.val = Matrix.scalar (Fin 2) c := by
  obtain ⟨c, hc0, hc⟩ := h.sq_scalar
  have h00 : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 0
  have h01 : A.val 0 0 * A.val 0 1 + A.val 0 1 * A.val 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 1
  have h10 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 0
  have h11 : A.val 1 0 * A.val 0 1 + A.val 1 1 * A.val 1 1 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 1
  have htr : A.val 1 1 = -A.val 0 0 := by
    by_contra hne
    have hsum : A.val 0 0 + A.val 1 1 ≠ 0 := by
      intro h0
      apply hne
      linear_combination h0
    have hb : A.val 0 1 = 0 := by
      have : A.val 0 1 * (A.val 0 0 + A.val 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right hsum
    have he : A.val 1 0 = 0 := by
      have : A.val 1 0 * (A.val 0 0 + A.val 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right hsum
    have hdiag : A.val 0 0 = A.val 1 1 := by
      have : (A.val 0 0 - A.val 1 1) * (A.val 0 0 + A.val 1 1) = 0 := by
        rw [hb, he] at h00 h11
        linear_combination h00 - h11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)
    apply h.not_scalar (A.val 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, he, ← hdiag]
  refine ⟨A.val 0 0, A.val 0 1, A.val 1 0, c, hc0, ?_, ?_, hc⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [htr]
  · linear_combination h00

theorem exists_comm_eq (h : IsInvolDiag A) (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 2) (Fin 2) F)
    (hM : A.val * M = M * A.val) :
    ∃ x y : F, M = x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A.val := by
  obtain ⟨a, b, e, c, hc0, hA, hac, -⟩ := h.entries
  rw [hA] at hM ⊢
  refine centralizer_form_aux h2 a b e ?_ M hM
  rintro ⟨hb, he, ha⟩
  apply h.not_scalar 0
  rw [hA, hb, he, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem anticomm_matrix {s : SL(2, F)} (hs : slConjugation 2 F A s = s * (-1)) :
    A.val * (s : Matrix (Fin 2) (Fin 2) F) = -((s : Matrix (Fin 2) (Fin 2) F) * A.val) := by
  have := (slConj_eq_iff A s (s * (-1))).mp hs
  rw [coe_mul_neg_one, neg_mul] at this
  exact this

theorem ne_of_anticomm (hneg : (-1 : SL(2, F)) ≠ 1) {s : SL(2, F)}
    (hs : slConjugation 2 F A s = s * (-1)) : slConjugation 2 F A s ≠ s := by
  intro h
  rw [h] at hs
  exact hneg (mul_left_cancel (a := s) (by simpa using hs.symm))

theorem sq_eq_neg_one (h2 : (2 : F) ≠ 0) {s : SL(2, F)}
    (hs : slConjugation 2 F A s = s * (-1)) : s * s = -1 := by
  have hA := anticomm_matrix hs
  have htr : Matrix.trace (s : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have hconj : A.val * (s : Matrix (Fin 2) (Fin 2) F) * (A⁻¹).val = -(s : Matrix (Fin 2) (Fin 2) F) := by
      rw [hA, Matrix.neg_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    have := Matrix.trace_units_conj A (s : Matrix (Fin 2) (Fin 2) F)
    rw [hconj, Matrix.trace_neg] at this
    have h22 : (2 : F) * Matrix.trace (s : Matrix (Fin 2) (Fin 2) F) = 0 := by
      linear_combination -this
    exact (mul_eq_zero.mp h22).resolve_left h2
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  have htr' : (s : Matrix (Fin 2) (Fin 2) F) 0 0 + (s : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    simpa [Matrix.trace_fin_two] using htr
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem mul_inv_eq_inv (h : IsInvolDiag A) (h2 : (2 : F) ≠ 0) {s k : SL(2, F)}
    (hs : slConjugation 2 F A s = s * (-1)) (hk : slConjugation 2 F A k = k) :
    s * k * s⁻¹ = k⁻¹ := by
  have hAs := anticomm_matrix hs
  have hAk : A.val * (k : Matrix (Fin 2) (Fin 2) F) = (k : Matrix (Fin 2) (Fin 2) F) * A.val :=
    (slConj_eq_iff A k k).mp hk
  obtain ⟨x, y, hxy⟩ := h.exists_comm_eq h2 _ hAk
  obtain ⟨a, b, e, c, hc0, hA, hac, hAA⟩ := h.entries
  have hsA : (s : Matrix (Fin 2) (Fin 2) F) * A.val = -(A.val * (s : Matrix (Fin 2) (Fin 2) F)) := by
    rw [hAs, neg_neg]
  have hdet : x ^ 2 - c * y ^ 2 = 1 := by
    have hd := k.2
    rw [hxy, hA, Matrix.det_fin_two] at hd
    simp at hd
    linear_combination hd + y ^ 2 * hac
  have hsk : (s : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) =
      (x • (1 : Matrix (Fin 2) (Fin 2) F) - y • A.val) * (s : Matrix (Fin 2) (Fin 2) F) := by
    rw [hxy]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, hsA, smul_neg]
    abel
  have hKk : (x • (1 : Matrix (Fin 2) (Fin 2) F) - y • A.val) * (k : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [hxy, hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have h1 : ((s * k * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      x • (1 : Matrix (Fin 2) (Fin 2) F) - y • A.val := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hsk,
      Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have h2 : (s * k * s⁻¹) * k = 1 := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, h1, hKk, Matrix.SpecialLinearGroup.coe_one]
  exact eq_inv_of_mul_eq_one_left h2

theorem fixed_of_anticomm_inv_mul {s t : SL(2, F)}
    (hs : slConjugation 2 F A s = s * (-1)) (ht : slConjugation 2 F A t = t * (-1)) :
    slConjugation 2 F A (s⁻¹ * t) = s⁻¹ * t := by
  rw [map_mul, map_inv, hs, ht, _root_.mul_inv_rev, neg_one_inv]
  apply sl_ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, neg_mul, mul_neg, one_mul, mul_one, neg_neg]

theorem exists_anticomm [Finite F] (h : IsInvolDiag A) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : ∃ w : SL(2, F), slConjugation 2 F A w = w * (-1) := by
  refine CFSG.ClassicalInvolution.w_lemma hodd h5 (slConjugation 2 F A) ?_ ?_
  · exact MulEquiv.ext fun s => h.sq s
  · intro h1
    obtain ⟨s, hs⟩ := h.ne
    exact hs (by rw [h1]; rfl)

end IsInvolDiag

end CFSG.ClassicalInvolution.Generic
