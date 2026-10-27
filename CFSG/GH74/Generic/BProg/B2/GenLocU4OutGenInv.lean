module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrDa

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K]

@[expose] def vconj (σ : K →+* K) (v : Fin 4 → K) : Fin 4 → K := fun j => σ (v j)

@[expose] def projE (σ : K →+* K) (w w' : Fin 4 → K) (a : K) : Matrix (Fin 4) (Fin 4) K :=
  (σ a)⁻¹ • Matrix.vecMulVec w (vconj σ w') + a⁻¹ • Matrix.vecMulVec w' (vconj σ w)

theorem projE_mul_self (σ : K →+* K) {w w' : Fin 4 → K} {a : K}
    (hww : vconj σ w ⬝ᵥ w = 0) (hw'w' : vconj σ w' ⬝ᵥ w' = 0) (ha : vconj σ w ⬝ᵥ w' = a)
    (hb : vconj σ w' ⬝ᵥ w = σ a) (ha0 : a ≠ 0) :
    projE σ w w' a * projE σ w w' a = projE σ w w' a := by
  have hσa : σ a ≠ 0 := by simpa using ha0
  unfold projE
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hww, hw'w', ha,
    hb, zero_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  field_simp
  ring

theorem projE_trace (σ : K →+* K) {w w' : Fin 4 → K} {a : K}
    (ha : vconj σ w ⬝ᵥ w' = a) (hb : vconj σ w' ⬝ᵥ w = σ a) (ha0 : a ≠ 0) :
    (projE σ w w' a).trace = 2 := by
  have hσa : σ a ≠ 0 := by simpa using ha0
  unfold projE
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm w (vconj σ w'), hb, dotProduct_comm w' (vconj σ w), ha]
  simp only [smul_eq_mul]
  field_simp
  norm_num

theorem projE_conjTranspose (σ : K →+* K) (hσσ : ∀ x, σ (σ x) = x) (w w' : Fin 4 → K) (a : K) :
    ((projE σ w w' a).map σ)ᵀ = projE σ w w' a := by
  ext i j
  simp only [projE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, vconj, map_add, map_mul, map_inv₀, hσσ]
  ring

theorem vconj_vecMul_skew (σ : K →+* K) {M : Matrix (Fin 4) (Fin 4) K} (hMt : Mᵀ = -M) (hMσ : M.map σ = M)
    {v : Fin 4 → K} {c : K} (hv : M *ᵥ v = c • v) : vconj σ v ᵥ* M = (-(σ c)) • vconj σ v := by
  ext j
  have h1 := congrFun hv j
  have e1 : ∀ k, M k j = -σ (M j k) := fun k => by
    have h0 := congrFun (congrFun hMt j) k
    have h' := congrFun (congrFun hMσ j) k
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h0 h'
    rw [h']
    exact h0
  calc (vconj σ v ᵥ* M) j = ∑ k, -(σ (M j k * v k)) := by
        simp only [Matrix.vecMul, dotProduct, vconj]
        exact Finset.sum_congr rfl fun k _ => by rw [e1 k, map_mul]; ring
    _ = -σ ((M *ᵥ v) j) := by
        simp only [Matrix.mulVec, dotProduct, map_sum, Finset.sum_neg_distrib]
    _ = ((-(σ c)) • vconj σ v) j := by
        rw [h1]
        simp only [Pi.smul_apply, smul_eq_mul, vconj, map_mul]
        ring

theorem projE_comm_skew (σ : K →+* K) {M : Matrix (Fin 4) (Fin 4) K} (hMt : Mᵀ = -M) (hMσ : M.map σ = M)
    {w w' : Fin 4 → K} {a c c' : K} (hw : M *ᵥ w = c • w) (hw' : M *ᵥ w' = c' • w')
    (hc : -(σ c) = c') (hc' : -(σ c') = c) :
    projE σ w w' a * M = M * projE σ w w' a := by
  unfold projE
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
    vconj_vecMul_skew σ hMt hMσ hw, vconj_vecMul_skew σ hMt hMσ hw', hw, hw', hc, hc']
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem projE_comm_sym (σ : K →+* K) (hσσ : ∀ x, σ (σ x) = x) {B : Matrix (Fin 4) (Fin 4) K} (hBt : Bᵀ = B)
    {w w' : Fin 4 → K} {a : K} (hBw : B *ᵥ vconj σ w = w') (hBw' : B *ᵥ vconj σ w' = w) :
    B * (projE σ w w' a).map σ = projE σ w w' a * B := by
  have hmap : (projE σ w w' a).map σ = a⁻¹ • Matrix.vecMulVec (vconj σ w) w' +
      (σ a)⁻¹ • Matrix.vecMulVec (vconj σ w') w := by
    ext i j
    simp only [projE, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, vconj, map_add, map_mul, map_inv₀, hσσ]
  have hrow : ∀ v : Fin 4 → K, v ᵥ* B = B *ᵥ v := fun v => by
    rw [← hBt, Matrix.vecMul_transpose, hBt]
  rw [hmap, projE, mul_add, add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hrow, hrow, hBw, hBw']
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

section Appl

variable {p f : ℕ}

theorem xi_transpose : (xi : Matrix (Fin 4) (Fin 4) K)ᵀ = -xi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi]

theorem xi_map (σ : K →+* K) : (xi : Matrix (Fin 4) (Fin 4) K).map σ = xi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi]

theorem xi_mulVec_eigen {i : K} (hi : i * i = -1) (s t : K) :
    (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ ![s, i * s, t, i * t] = i • ![s, i * s, t, i * t] := by
  ext j
  fin_cases j <;> simp [xi, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | linear_combination (-s) * hi | linear_combination (-t) * hi

theorem eigen_dot {i : K} (hi : i * i = -1) (s t : K) :
    (![s, i * s, t, i * t] : Fin 4 → K) ⬝ᵥ ![s, i * s, t, i * t] = 0 := by
  simp only [dotProduct, Fin.sum_univ_four]
  simp
  linear_combination (s * s + t * t) * hi

theorem eigen_neg {B : Matrix (Fin 4) (Fin 4) K} (hξB : (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi))
    {i : K} {w : Fin 4 → K} (hw : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ w = i • w) :
    (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ (B *ᵥ w) = (-i) • (B *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, hξB, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, neg_smul]

theorem exists_nonisotropic (h2 : (2 : K) ≠ 0) {i : K} (hi : i * i = -1) {B : Matrix (Fin 4) (Fin 4) K}
    (hBt : Bᵀ = B) (hinj : ∀ v, B *ᵥ v = 0 → v = 0)
    (hξB : (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi)) :
    ∃ s t : K, (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) ∧
      (![s, i * s, t, i * t] : Fin 4 → K) ⬝ᵥ (B *ᵥ ![s, i * s, t, i * t]) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hrow : ∀ v : Fin 4 → K, v ᵥ* B = B *ᵥ v := fun v => by
    rw [← hBt, Matrix.vecMul_transpose, hBt]
  set u1 : Fin 4 → K := ![1, i * 1, 0, i * 0] with hu1
  set u2 : Fin 4 → K := ![0, i * 0, 1, i * 1] with hu2
  have q1 : u1 ⬝ᵥ (B *ᵥ u1) = 0 := hcon 1 0 (Or.inr rfl) (Or.inl rfl)
  have q2 : u2 ⬝ᵥ (B *ᵥ u2) = 0 := hcon 0 1 (Or.inl rfl) (Or.inr rfl)
  have q3 : (u1 + u2) ⬝ᵥ (B *ᵥ (u1 + u2)) = 0 := by
    have := hcon 1 1 (Or.inr rfl) (Or.inr rfl)
    have e : (![1, i * 1, 1, i * 1] : Fin 4 → K) = u1 + u2 := by
      ext j
      fin_cases j <;> simp [hu1, hu2]
    rw [e] at this
    exact this
  have hsym : u2 ⬝ᵥ (B *ᵥ u1) = u1 ⬝ᵥ (B *ᵥ u2) := by
    rw [Matrix.dotProduct_mulVec, hrow, dotProduct_comm]
  have hc : u1 ⬝ᵥ (B *ᵥ u2) = 0 := by
    have e : (u1 + u2) ⬝ᵥ (B *ᵥ (u1 + u2)) = u1 ⬝ᵥ (B *ᵥ u1) + u1 ⬝ᵥ (B *ᵥ u2) + u2 ⬝ᵥ (B *ᵥ u1) +
        u2 ⬝ᵥ (B *ᵥ u2) := by
      simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
      ring
    rw [e, q1, q2, hsym] at q3
    have : (2 : K) * (u1 ⬝ᵥ (B *ᵥ u2)) = 0 := by linear_combination q3
    exact (mul_eq_zero.1 this).resolve_left h2
  have hu1eig : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ u1 = i • u1 := xi_mulVec_eigen hi 1 0
  have hy := eigen_neg hξB hu1eig
  set y : Fin 4 → K := B *ᵥ u1 with hydef
  have d1 : u1 ⬝ᵥ y = 0 := q1
  have d2 : u2 ⬝ᵥ y = 0 := by rw [hydef, hsym, hc]
  have hyc : ∀ j, ((xi : Matrix (Fin 4) (Fin 4) K) *ᵥ y) j = ((-i) • y) j := fun j => by rw [hy]
  have e0 := hyc 0
  have e1 := hyc 1
  have e2 := hyc 2
  have e3 := hyc 3
  simp [xi, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  have d1' : y 0 + i * y 1 = 0 := by simpa [hu1, dotProduct, Fin.sum_univ_four] using d1
  have d2' : y 2 + i * y 3 = 0 := by simpa [hu2, dotProduct, Fin.sum_univ_four] using d2
  have hy0 : y 0 = 0 := by
    have : (2 : K) * y 0 = 0 := by linear_combination d1' - i * e0 + y 0 * hi
    exact (mul_eq_zero.1 this).resolve_left h2
  have hy2 : y 2 = 0 := by
    have : (2 : K) * y 2 = 0 := by linear_combination d2' - i * e2 + y 2 * hi
    exact (mul_eq_zero.1 this).resolve_left h2
  have hy1 : y 1 = 0 := by linear_combination e0 + (-i) * hy0
  have hy3 : y 3 = 0 := by linear_combination e2 + (-i) * hy2
  have hyz : B *ᵥ u1 = 0 := by
    ext j
    fin_cases j
    · exact hy0
    · exact hy1
    · exact hy2
    · exact hy3
  have hu10 : u1 = 0 := hinj u1 hyz
  have := congrFun hu10 0
  simp [hu1] at this

theorem vconj_mulVec (σ : K →+* K) (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    vconj σ (M *ᵥ v) = (M.map σ) *ᵥ vconj σ v := by
  ext j
  simp [vconj, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem reflect_sq (M : Matrix (Fin 4) (Fin 4) K) (hM : M * M = M) :
    (1 - (2 : K) • M) * (1 - (2 : K) • M) = 1 := by
  have e : (1 - (2 : K) • M) * (1 - (2 : K) • M) = 1 - (2 : K) • M - (2 : K) • M + ((2 : K) * 2) • (M * M) := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel
  rw [e, hM]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem reflect_map (σ : K →+* K) (E : Matrix (Fin 4) (Fin 4) K) :
    ((1 - (2 : K) • E).map σ) = 1 - (2 : K) • E.map σ := by
  have h2σ : σ (2 : K) = 2 := map_ofNat σ 2
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, h2σ]
  · simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, hij, h2σ]

theorem reflect_transpose (E : Matrix (Fin 4) (Fin 4) K) : (1 - (2 : K) • E)ᵀ = 1 - (2 : K) • Eᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply]
  · simp [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, hij, Ne.symm hij]

theorem exists_split_involution [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {B : Matrix (Fin 4) (Fin 4) K} (hBU : IsUnitaryU (p ^ f) B) (hBt : Bᵀ = B)
    (hξB : (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi)) :
    ∃ x : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) x ∧ x * x = 1 ∧ x.trace = 0 ∧
      (xi : Matrix (Fin 4) (Fin 4) K) * x = x * xi ∧ x * B = B * x.map (· ^ (p ^ f)) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨i, hi⟩ := GenLocU4OutFrDa.exists_neg_one_sq hK hq
  let σ : K →+* K := h.bar
  have hσσ : ∀ x, σ (σ x) = x := h.bar_bar
  have hσq : ∀ x : K, σ x = x ^ (p ^ f) := fun x => h.bar_apply x
  have hσmap : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map σ = M.map (· ^ (p ^ f)) := fun M => by
    ext a b
    simp [Matrix.map_apply, hσq]
  have hσi : σ i = i := by
    rw [hσq]
    exact GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hi
  have hsymq : (B.map (· ^ (p ^ f)))ᵀ = B.map (· ^ (p ^ f)) := by rw [← Matrix.transpose_map, hBt]
  have hBσ : B.map σ * B = 1 := by
    rw [hσmap, ← hsymq]
    exact hBU
  have hBBσ : B * B.map σ = 1 := mul_eq_one_comm.1 hBσ
  have hinj : ∀ v, B *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e : (B.map σ * B) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [hBσ, Matrix.one_mulVec] at e
    exact e
  have hrowB : ∀ v : Fin 4 → K, v ᵥ* B = B *ᵥ v := fun v => by
    rw [← hBt, Matrix.vecMul_transpose, hBt]
  obtain ⟨s, t, hs, ht, hne⟩ := exists_nonisotropic h2 hi hBt hinj hξB
  have hσs : σ s = s := by rcases hs with rfl | rfl <;> simp
  have hσt : σ t = t := by rcases ht with rfl | rfl <;> simp
  set w : Fin 4 → K := ![s, i * s, t, i * t] with hw
  have hwσ : vconj σ w = w := by
    ext j
    fin_cases j <;> simp [vconj, hw, hσs, hσt, hσi, map_mul]
  have hw1 : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ w = i • w := xi_mulVec_eigen hi s t
  have hww : w ⬝ᵥ w = 0 := eigen_dot hi s t
  set w' : Fin 4 → K := B *ᵥ w with hw'
  have hw'1 : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ w' = (-i) • w' := eigen_neg hξB hw1
  set a : K := vconj σ w ⬝ᵥ w' with ha
  have ha0 : a ≠ 0 := by
    rw [ha, hwσ]
    exact hne
  have hvw' : vconj σ w' = (B.map σ) *ᵥ w := by rw [hw', vconj_mulVec, hwσ]
  have hw'w' : vconj σ w' ⬝ᵥ w' = 0 := by
    rw [hvw', hw', Matrix.dotProduct_mulVec, hrowB, Matrix.mulVec_mulVec, hBBσ, Matrix.one_mulVec]
    exact hww
  have hb : vconj σ w' ⬝ᵥ w = σ a := by
    rw [ha]
    simp only [dotProduct, vconj, map_sum, map_mul, hσσ]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hBw : B *ᵥ vconj σ w = w' := by rw [hwσ]
  have hBw' : B *ᵥ vconj σ w' = w := by
    rw [hvw', Matrix.mulVec_mulVec, hBBσ, Matrix.one_mulVec]
  have hww' : vconj σ w ⬝ᵥ w = 0 := by rw [hwσ]; exact hww
  have hE2 := projE_mul_self σ hww' hw'w' rfl hb ha0
  have hEtr := projE_trace σ rfl hb ha0
  have hEct := projE_conjTranspose σ hσσ w w' a
  have hEξ : projE σ w w' a * (xi : Matrix (Fin 4) (Fin 4) K) = (xi : Matrix (Fin 4) (Fin 4) K) * projE σ w w' a :=
    projE_comm_skew σ xi_transpose (xi_map σ) hw1 hw'1 (by rw [hσi]) (by rw [map_neg, hσi, neg_neg])
  have hEB := projE_comm_sym σ hσσ hBt hBw hBw' (a := a)
  refine ⟨1 - (2 : K) • projE σ w w' a, ?_, reflect_sq _ hE2, ?_, ?_, ?_⟩
  · show ((1 - (2 : K) • projE σ w w' a).map (· ^ (p ^ f)))ᵀ * (1 - (2 : K) • projE σ w w' a) = 1
    rw [← hσmap, reflect_map, reflect_transpose, hEct]
    exact reflect_sq _ hE2
  · rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, hEtr]
    simp only [Fintype.card_fin, smul_eq_mul]
    norm_num
  · rw [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hEξ]
  · rw [← hσmap, reflect_map, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hEB]

end Appl

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
