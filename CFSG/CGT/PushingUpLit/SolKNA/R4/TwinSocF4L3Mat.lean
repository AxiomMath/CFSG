module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3B

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem coe_blkP_scalar_gen (l : Kˣ) :
    ((blkP 1 (GeneralLinearGroup.scalar (Fin 2) l) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), l, ((l : K) * l)⁻¹] := by
  rw [coe_blkP_one, GeneralLinearGroup.coe_scalar]
  have hdet : (scalar (Fin 2) (l : K)).det = (l : K) * l := by
    rw [Matrix.det_fin_two]
    simp
  rw [hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem eig_rel (h2 : (2 : K) ≠ 0) {a m l n ω : K} (hm : a * a * m = 1) (hn : l * l * n = 1)
    (hω : ω ^ 3 = 1) {g : GL (Fin 3) K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, a, m] *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ω • diagonal ![l, l, n]) :
    (a = ω * l ∨ a = ω * n) ∧ (m = ω * l ∨ m = ω * n) ∧ (ω * l = a ∨ ω * l = m) ∧
      (ω * n = a ∨ ω * n = m) := by
  obtain ⟨E1, E2⟩ := trace_eq_of_conj h
  rw [trace_diagonal, trace_diagonal, Fin.sum_univ_three, Fin.sum_univ_three] at E1
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal, trace_diagonal, trace_diagonal,
    Fin.sum_univ_three, Fin.sum_univ_three] at E2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply] at E1 E2
  have key : ∀ T : K, (T - a) ^ 2 * (T - m) = (T - ω * l) ^ 2 * (T - ω * n) := by
    intro T
    have h' : (2 : K) * ((T - a) ^ 2 * (T - m) - (T - ω * l) ^ 2 * (T - ω * n)) = 0 := by
      linear_combination (-2 * T ^ 2 + T * ((a + a + m) + ω * (l + l + n))) * E1 - T * E2 -
        2 * (hm - ω ^ 3 * hn - hω)
    have := (mul_eq_zero.mp h').resolve_left h2
    linear_combination this
  have root : ∀ r₁ r₂ r₃ : K, (r₁ - r₂) ^ 2 * (r₁ - r₃) = 0 →
      r₁ = r₂ ∨ r₁ = r₃ := fun r₁ r₂ r₃ hh => by
    rcases mul_eq_zero.mp hh with h1 | h1
    · exact Or.inl (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1))
    · exact Or.inr (sub_eq_zero.mp h1)
  refine ⟨root a (ω * l) (ω * n) ?_, root m (ω * l) (ω * n) ?_,
    root (ω * l) a m ?_, root (ω * n) a m ?_⟩
  · rw [← key a]; ring
  · rw [← key m]; ring
  · rw [key (ω * l)]; ring
  · rw [key (ω * n)]; ring

theorem eq_of_eig (h2 : (2 : K) ≠ 0) {l a : Kˣ} {k : ℕ} (hl : l ^ 2 ^ k = 1) (ha : a ^ 2 ^ k = 1)
    (hl3 : (l : K) ^ 3 ≠ 1) {ω : K} (hω : ω ^ 3 = 1) {g : GL (Fin 3) K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![(a : K), a, ((a : K) * a)⁻¹] *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • diagonal ![(l : K), l, ((l : K) * l)⁻¹]) : (a : K) = l ∧ ω = 1 := by
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hm : (a : K) * a * ((a : K) * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ha0 ha0)
  have hn : (l : K) * l * ((l : K) * l)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hl0 hl0)
  obtain ⟨d1, d2, d3, d4⟩ := eig_rel h2 hm hn hω h
  have hl' : (l : K) ^ 2 ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hl, Units.val_one]
  have ha' : (a : K) ^ 2 ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have hωone : ω = 1 := by
    have hω2 : ω ^ 2 ^ k = 1 := by
      rcases d1 with h1 | h1
      · have : (a : K) ^ 2 ^ k = ω ^ 2 ^ k * (l : K) ^ 2 ^ k := by rw [h1, mul_pow]
        rwa [ha', hl', mul_one, eq_comm] at this
      · have : (a : K) ^ 2 ^ k = ω ^ 2 ^ k * (((l : K) * l)⁻¹) ^ 2 ^ k := by rw [h1, mul_pow]
        rwa [ha', inv_pow, mul_pow, hl', one_mul, inv_one, mul_one, eq_comm] at this
    have := pow_gcd_eq_one.mpr ⟨hω2, hω⟩
    rwa [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), pow_one] at this
  subst hωone
  refine ⟨?_, rfl⟩
  simp only [one_mul] at d1 d3
  rcases d1 with h1 | h1
  · exact h1
  · exfalso
    rcases d3 with h3 | h3
    · apply hl3
      have : (l : K) = ((l : K) * l)⁻¹ := h3.trans h1
      field_simp at this
      linear_combination this
    · apply hl3
      have h4 : (l : K) = ((a : K) * a)⁻¹ := h3
      rw [h1] at h4
      have h5 : (l : K) = ((l : K) * l) * ((l : K) * l) :=
        h4.trans (by rw [_root_.mul_inv_rev, inv_inv])
      have h6 : (l : K) * ((l : K) ^ 3 - 1) = 0 := by linear_combination -h5
      exact sub_eq_zero.mp ((mul_eq_zero.mp h6).resolve_left hl0)

theorem map_diag_scalar (τ : K ≃+* K) (l : Kˣ) :
    ((SpecialLinearGroup.map τ.toRingHom (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)) :
        SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![τ (l : K), τ (l : K), (τ (l : K) * τ (l : K))⁻¹] := by
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_blkP_scalar_gen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem fix_field (h2 : (2 : K) ≠ 0) {l : Kˣ} {k : ℕ} (hl : l ^ 2 ^ k = 1) (hl3 : (l : K) ^ 3 ≠ 1)
    {g : GL (Fin 3) K} {τ : K ≃+* K}
    (h : conjAut 3 K g (fieldAut 3 K τ
        (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) : τ (l : K) = l := by
  rw [fieldAut_proj] at h
  obtain ⟨ω, hω3, hω⟩ := exists_conj_eq_smul h
  rw [map_diag_scalar, coe_blkP_scalar_gen] at hω
  have hτ0 : τ (l : K) ≠ 0 := by simpa using l.ne_zero
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hl' : (l : K) ^ 2 ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hl, Units.val_one]
  have ha : (Units.mk0 (τ (l : K)) hτ0) ^ 2 ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hl', map_one, Units.val_one]
  exact (eq_of_eig h2 hl ha hl3 hω3' hω).1

theorem fix_graph (h2 : (2 : K) ≠ 0) {l : Kˣ} {k : ℕ} (hl : l ^ 2 ^ k = 1) (hl3 : (l : K) ^ 3 ≠ 1)
    {g : GL (Fin 3) K} {τ : K ≃+* K}
    (h : (conjAut 3 K g * fieldAut 3 K τ * dualAut 3 K)
        (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) : τ ((l⁻¹ : Kˣ) : K) = l := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, ← map_inv, ← map_inv, fieldAut_proj] at h
  obtain ⟨ω, hω3, hω⟩ := exists_conj_eq_smul h
  have hx : ((SpecialLinearGroup.map τ.toRingHom
      (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l⁻¹)).transpose : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) =
      diagonal ![τ ((l⁻¹ : Kˣ) : K), τ ((l⁻¹ : Kˣ) : K),
        (τ ((l⁻¹ : Kˣ) : K) * τ ((l⁻¹ : Kˣ) : K))⁻¹] := by
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      SpecialLinearGroup.coe_transpose, coe_blkP_scalar_gen, diagonal_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  rw [hx, coe_blkP_scalar_gen] at hω
  have hτ0 : τ ((l⁻¹ : Kˣ) : K) ≠ 0 := by simpa using (l⁻¹).ne_zero
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hl' : (l : K) ^ 2 ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hl, Units.val_one]
  have ha : (Units.mk0 (τ ((l⁻¹ : Kˣ) : K)) hτ0) ^ 2 ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, Units.val_inv_eq_inv_val, inv_pow, hl',
      inv_one, map_one, Units.val_one]
  exact (eq_of_eig h2 hl ha hl3 hω3' hω).1

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
