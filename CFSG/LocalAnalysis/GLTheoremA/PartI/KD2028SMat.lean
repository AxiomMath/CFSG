module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix

variable {K : Type} [Field K]

@[expose] def kdsE (a : K) (x : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (3 : K)⁻¹ • (1 + a • x + (a ^ 2) • x ^ 2)

theorem kdsE_comm (a : K) (x : Matrix (Fin 3) (Fin 3) K) : Commute x (kdsE a x) := by
  unfold kdsE
  exact (((Commute.one_right x).add_right ((Commute.refl x).smul_right a)).add_right
    (((Commute.refl x).pow_right 2).smul_right _)).smul_right _

theorem kdsE_eigen {a : K} (ha : a ^ 3 = 1) {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1) :
    x * kdsE a x = a ^ 2 • kdsE a x := by
  have h3 : x * x ^ 2 = 1 := by rw [← pow_succ']; exact hx
  unfold kdsE
  simp only [mul_smul_comm, mul_add, mul_one, ← sq, h3]
  match_scalars <;> first | ring1 | linear_combination (-(3 : K)⁻¹) * ha |
    linear_combination (-((3 : K)⁻¹ * a)) * ha

theorem kdsE_mul {a b : K} (hb : b ^ 3 = 1) {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1) :
    kdsE a x * kdsE b x = ((3 : K)⁻¹ * (1 + a * b ^ 2 + a ^ 2 * b ^ 4)) • kdsE b x := by
  have h1 := kdsE_eigen hb hx
  have h2 : x ^ 2 * kdsE b x = b ^ 4 • kdsE b x := by
    rw [pow_two, mul_assoc, h1, mul_smul_comm, h1, smul_smul]
    ring_nf
  set Eb := kdsE b x with hEb
  show ((3 : K)⁻¹ • (1 + a • x + (a ^ 2) • x ^ 2)) * Eb = _
  rw [smul_mul_assoc, add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, h1, h2,
    smul_smul, smul_smul]
  module

theorem kdsE_idem {a : K} (ha : a ^ 3 = 1) (h3 : (3 : K) ≠ 0) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x ^ 3 = 1) : kdsE a x * kdsE a x = kdsE a x := by
  rw [kdsE_mul ha hx]
  have e : 1 + a * a ^ 2 + a ^ 2 * a ^ 4 = 3 := by linear_combination (a ^ 3 + 2) * ha
  rw [e, inv_mul_cancel₀ h3, one_smul]

theorem kds_cube_aux {a b : K} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a ≠ b) :
    1 + a * b ^ 2 + a ^ 2 * b ^ 4 = 0 := by
  have hu3 : (a * b ^ 2) ^ 3 = 1 := by
    calc (a * b ^ 2) ^ 3 = a ^ 3 * (b ^ 3) ^ 2 := by ring
      _ = 1 := by rw [ha, hb]; ring
  have hu1 : a * b ^ 2 ≠ 1 := by
    intro h
    apply hab
    calc a = a * b ^ 3 := by rw [hb, mul_one]
      _ = (a * b ^ 2) * b := by ring
      _ = b := by rw [h, one_mul]
  have h0 : (a * b ^ 2 - 1) * (1 + a * b ^ 2 + (a * b ^ 2) ^ 2) = 0 := by linear_combination hu3
  have := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hu1)
  linear_combination this

theorem kdsE_orth {a b : K} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a ≠ b)
    {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1) : kdsE a x * kdsE b x = 0 := by
  rw [kdsE_mul hb hx, kds_cube_aux ha hb hab, mul_zero, zero_smul]

theorem kdsE_sum {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    (x : Matrix (Fin 3) (Fin 3) K) : kdsE 1 x + kdsE ω x + kdsE (ω ^ 2) x = 1 := by
  have h33 : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
  unfold kdsE
  match_scalars
  · linear_combination h33
  · linear_combination (3 : K)⁻¹ * hω
  · linear_combination ((3 : K)⁻¹ * (ω ^ 2 - ω + 1)) * hω

theorem kdsE_eq_one {a : K} (ha : a ^ 3 = 1) {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1)
    (h : kdsE a x = 1) : x = a ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  calc x = x * 1 := (mul_one x).symm
    _ = x * kdsE a x := by rw [h]
    _ = a ^ 2 • kdsE a x := kdsE_eigen ha hx
    _ = a ^ 2 • 1 := by rw [h]

theorem kds_three_ne_zero {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h3
  apply hω1
  have h : (ω - 1) ^ 3 = 0 := by linear_combination hω3 + (ω - ω ^ 2) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem kds_quad {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)

theorem kds_exists_two {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x ^ 3 = 1) (hns : ∀ c : K, x ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ a b : K, (a = 1 ∨ a = ω ∨ a = ω ^ 2) ∧ (b = 1 ∨ b = ω ∨ b = ω ^ 2) ∧ a ≠ b ∧
      kdsE a x ≠ 0 ∧ kdsE b x ≠ 0 := by
  have h3 := kds_three_ne_zero hω3 hω1
  have hq := kds_quad hω3 hω1
  have hsum := kdsE_sum hq h3 x
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hne1 : ∀ a : K, a ^ 3 = 1 → kdsE a x ≠ 1 := fun a ha h => hns (a ^ 2) (kdsE_eq_one ha hx h)
  have d01 : (1 : K) ≠ ω := fun h => hω1 h.symm
  have d02 : (1 : K) ≠ ω ^ 2 := by
    intro h
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [← h, mul_one]
      _ = 1 := by rw [← pow_succ']; exact hω3
  have d12 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    linear_combination hω3 - (1 + ω) * h.symm
  by_cases h0 : kdsE 1 x = 0 <;> by_cases h1 : kdsE ω x = 0 <;>
    by_cases h2 : kdsE (ω ^ 2) x = 0
  · exfalso
    rw [h0, h1, h2] at hsum
    simp at hsum
  · exfalso
    rw [h0, h1, zero_add, zero_add] at hsum
    exact hne1 _ hω23 hsum
  · exfalso
    rw [h0, h2, zero_add, add_zero] at hsum
    exact hne1 _ hω3 hsum
  · exact ⟨ω, ω ^ 2, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), d12, h1, h2⟩
  · exfalso
    rw [h1, h2, add_zero, add_zero] at hsum
    exact hne1 _ (one_pow 3) hsum
  · exact ⟨1, ω ^ 2, Or.inl rfl, Or.inr (Or.inr rfl), d02, h0, h2⟩
  · exact ⟨1, ω, Or.inl rfl, Or.inr (Or.inl rfl), d01, h0, h1⟩
  · exact ⟨1, ω, Or.inl rfl, Or.inr (Or.inl rfl), d01, h0, h1⟩

theorem kds_inv_of_idem {P : Matrix (Fin 3) (Fin 3) K} (hP : P * P = P) (h0 : P ≠ 0)
    (h1 : P ≠ 1) (h2 : (2 : K) ≠ 0) :
    ∃ t : Matrix (Fin 3) (Fin 3) K, t * t = 1 ∧ t ≠ 1 ∧ t.det = 1 ∧
      (∀ M : Matrix (Fin 3) (Fin 3) K, Commute P M → Commute t M) ∧
      (∀ σ : K →+* K, (P.map σ)ᵀ = P → (t.map σ)ᵀ = t) := by
  set s : Matrix (Fin 3) (Fin 3) K := (2 : K) • P - 1 with hs_def
  have hs : s * s = 1 := by
    simp only [hs_def, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hP, one_mul, mul_one,
      smul_smul]
    module
  have hdet : s.det * s.det = 1 := by rw [← det_mul, hs, det_one]
  have hsc : ∀ M : Matrix (Fin 3) (Fin 3) K, Commute P M → Commute s M := fun M hM =>
    (hM.smul_left _).sub_left (Commute.one_left M)
  have hss : ∀ σ : K →+* K, (P.map σ)ᵀ = P → (s.map σ)ᵀ = s := by
    intro σ hσ
    ext i j
    have hij : σ (P j i) = P i j := congrFun (congrFun hσ i) j
    have h2σ : σ 2 = 2 := map_ofNat σ 2
    by_cases hji : i = j
    · subst hji
      simp [hs_def, hij, h2σ]
    · simp [hs_def, hij, h2σ, Matrix.one_apply_ne hji, Matrix.one_apply_ne (Ne.symm hji)]
  have h2inv : ∀ A B : Matrix (Fin 3) (Fin 3) K, (2 : K) • A = (2 : K) • B → A = B := by
    intro A B h
    calc A = (2 : K)⁻¹ • ((2 : K) • A) := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : K)⁻¹ • ((2 : K) • B) := by rw [h]
      _ = B := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  rcases mul_self_eq_one_iff.mp hdet with hd | hd
  · refine ⟨s, hs, ?_, hd, hsc, hss⟩
    intro h
    apply h1
    refine h2inv _ _ ?_
    rw [hs_def, sub_eq_iff_eq_add] at h
    rw [h, two_smul]
  · refine ⟨-s, by rw [neg_mul_neg, hs], ?_, ?_, fun M hM => (hsc M hM).neg_left, ?_⟩
    · intro h
      apply h0
      refine h2inv _ _ ?_
      have h' : s = -1 := neg_eq_iff_eq_neg.mp h
      rw [hs_def, sub_eq_iff_eq_add] at h'
      rw [h', smul_zero]
      simp
    · rw [det_neg, hd]
      norm_num
    · intro σ hσ
      ext i j
      have := congrFun (congrFun (hss σ hσ) i) j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, map_neg] at this ⊢
      rw [this]

theorem kdsE_star {a : K} (ha : a ^ 3 = 1) {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1)
    (σ : K →+* K) (hσa : σ a = a ^ 2) (hxs : (x.map σ)ᵀ = x ^ 2) :
    ((kdsE a x).map σ)ᵀ = kdsE a x := by
  have h4 : (x ^ 2) ^ 2 = x := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx, one_mul]
  have hσ3 : σ ((3 : K)⁻¹) = (3 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hσa2 : σ (a ^ 2) = a := by
    rw [map_pow, hσa, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]
  have hmx2 : ((x ^ 2).map σ)ᵀ = x := by
    have : (x ^ 2).map σ = (x.map σ) ^ 2 := map_pow σ.mapMatrix x 2
    rw [this, Matrix.transpose_pow, hxs, h4]
  unfold kdsE
  simp only [Matrix.map_smul' _ _ _ (map_mul σ), Matrix.map_add _ (map_add σ),
    Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_one, hσ3, hσa, hσa2, hxs, hmx2]
  module

theorem kds_exists_mul_ne_zero {P Q : Matrix (Fin 3) (Fin 3) K} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ y : Matrix (Fin 3) (Fin 3) K, P * y * Q ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra h
    apply hP
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨k, l, hkl⟩ : ∃ k l, Q k l ≠ 0 := by
    by_contra h
    apply hQ
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  refine ⟨Matrix.single j k 1, fun h => ?_⟩
  have hrow : ∀ b, (P * Matrix.single j k (1 : K)) i b * Q b l =
      if b = k then P i j * Q k l else 0 := by
    intro b
    by_cases hb : b = k
    · subst hb
      simp
    · simp [hb]
  have h1 : (P * Matrix.single j k (1 : K) * Q : Matrix (Fin 3) (Fin 3) K) i l =
      P i j * Q k l := by
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun b _ => hrow b)]
    simp
  rw [h] at h1
  exact mul_ne_zero hij hkl (by rw [← h1]; rfl)

theorem kdsPyQ_mul {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 0)
    (y z : Matrix (Fin 3) (Fin 3) K) :
    (1 + P * y * Q) * (1 + P * z * Q) = 1 + P * (y + z) * Q := by
  have h0 : (P * y * Q) * (P * z * Q) = 0 := by
    calc (P * y * Q) * (P * z * Q) = P * y * (Q * P) * z * Q := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQP]; simp
  calc (1 + P * y * Q) * (1 + P * z * Q)
      = 1 + P * y * Q + P * z * Q + (P * y * Q) * (P * z * Q) := by noncomm_ring
    _ = 1 + P * (y + z) * Q := by rw [h0, add_zero, mul_add, add_mul]; abel

theorem kdsPyQ_zero (P Q : Matrix (Fin 3) (Fin 3) K) :
    (1 + P * 0 * Q : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp

@[expose] def kdsUnip (P Q : Matrix (Fin 3) (Fin 3) K) (hQP : Q * P = 0) :
    Subgroup (GL (Fin 3) K) where
  carrier := {A | ∃ y : Matrix (Fin 3) (Fin 3) K,
    (A : Matrix (Fin 3) (Fin 3) K) = 1 + P * y * Q}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro A B ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [Units.val_mul, hy, hz, kdsPyQ_mul hQP]⟩
  inv_mem' := by
    rintro A ⟨y, hy⟩
    refine ⟨-y, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hy, kdsPyQ_mul hQP, add_neg_cancel, kdsPyQ_zero]

theorem kdsPyQ_conj {P Q x : Matrix (Fin 3) (Fin 3) K} {α β : K} (hx : x ^ 3 = 1)
    (hxP : x * P = α • P) (hQx : Q * x ^ 2 = β • Q) (y : Matrix (Fin 3) (Fin 3) K) :
    x * (1 + P * y * Q) * x ^ 2 = 1 + P * ((α * β) • y) * Q := by
  have h3 : x * x ^ 2 = 1 := by rw [← pow_succ']; exact hx
  calc x * (1 + P * y * Q) * x ^ 2 = x * x ^ 2 + (x * P) * y * (Q * x ^ 2) := by noncomm_ring
    _ = 1 + (α • P) * y * (β • Q) := by rw [h3, hxP, hQx]
    _ = 1 + P * ((α * β) • y) * Q := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm β α]

theorem kdsPyQ_sq {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 0) (h2 : (2 : K) = 0)
    (y : Matrix (Fin 3) (Fin 3) K) : (1 + P * y * Q) * (1 + P * y * Q) = 1 := by
  rw [kdsPyQ_mul hQP, ← two_smul K y, h2, zero_smul, kdsPyQ_zero]

theorem kdsPyQ_det {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 0) (h2 : (2 : K) = 0)
    (y : Matrix (Fin 3) (Fin 3) K) : (1 + P * y * Q).det = 1 := by
  have h : (1 + P * y * Q).det * (1 + P * y * Q).det = 1 := by
    rw [← det_mul, kdsPyQ_sq hQP h2, det_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1]
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

@[expose] def kdsUnipGL {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 0)
    (y : Matrix (Fin 3) (Fin 3) K) : GL (Fin 3) K :=
  ⟨1 + P * y * Q, 1 + P * (-y) * Q, by rw [kdsPyQ_mul hQP, add_neg_cancel, kdsPyQ_zero],
    by rw [kdsPyQ_mul hQP, neg_add_cancel, kdsPyQ_zero]⟩

theorem kdsUnipGL_mem {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 0)
    (y : Matrix (Fin 3) (Fin 3) K) : kdsUnipGL hQP y ∈ kdsUnip P Q hQP :=
  ⟨y, rfl⟩

theorem kds_odd_matrix {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (h2 : (2 : K) ≠ 0)
    {x : Matrix (Fin 3) (Fin 3) K} (hx : x ^ 3 = 1)
    (hns : ∀ c : K, x ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ t : Matrix (Fin 3) (Fin 3) K, t * t = 1 ∧ t ≠ 1 ∧ t.det = 1 ∧ x * t = t * x ∧
      ∀ σ : K →+* K, σ ω = ω ^ 2 → (x.map σ)ᵀ = x ^ 2 → (t.map σ)ᵀ = t := by
  have h3 := kds_three_ne_zero hω3 hω1
  obtain ⟨a, b, ha, -, -, hEa, -⟩ := kds_exists_two hω3 hω1 hx hns
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have ha3 : a ^ 3 = 1 := by
    rcases ha with rfl | rfl | rfl
    · exact one_pow 3
    · exact hω3
    · exact hω23
  have hE1 : kdsE a x ≠ 1 := fun h => hns (a ^ 2) (kdsE_eq_one ha3 hx h)
  obtain ⟨t, htt, ht1, hdet, hcomm, hstar⟩ :=
    kds_inv_of_idem (kdsE_idem ha3 h3 hx) hEa hE1 h2
  refine ⟨t, htt, ht1, hdet, (hcomm x (kdsE_comm a x).symm).symm.eq, ?_⟩
  intro σ hσω hxs
  refine hstar σ (kdsE_star ha3 hx σ ?_ hxs)
  rcases ha with rfl | rfl | rfl
  · rw [map_one, one_pow]
  · exact hσω
  · rw [map_pow, hσω]

theorem kds_even_matrix {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x ^ 3 = 1) (hns : ∀ c : K, x ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (P Q : Matrix (Fin 3) (Fin 3) K) (α β : K), Q * P = 0 ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      x * P = α • P ∧ Q * x ^ 2 = β • Q := by
  obtain ⟨a, b, ha, hb, hab, hEa, hEb⟩ := kds_exists_two hω3 hω1 hx hns
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hcube : ∀ c : K, (c = 1 ∨ c = ω ∨ c = ω ^ 2) → c ^ 3 = 1 := by
    rintro c (rfl | rfl | rfl)
    · exact one_pow 3
    · exact hω3
    · exact hω23
  have ha3 := hcube a ha
  have hb3 := hcube b hb
  refine ⟨kdsE a x, kdsE b x, a ^ 2, b ^ 4, kdsE_orth hb3 ha3 hab.symm hx, hEa, hEb,
    kdsE_eigen ha3 hx, ?_⟩
  have h1 : kdsE b x * x = b ^ 2 • kdsE b x := by
    rw [← (kdsE_comm b x).eq]
    exact kdsE_eigen hb3 hx
  rw [pow_two, ← mul_assoc, h1, smul_mul_assoc, h1, smul_smul]
  ring_nf

end CFSG.LocalAnalysis.GLTheoremA
