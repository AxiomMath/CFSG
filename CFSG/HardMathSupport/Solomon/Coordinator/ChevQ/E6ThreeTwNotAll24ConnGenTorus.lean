module

public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.HardMathSupport.Lang.TwE6Step3 Matrix

section Torus

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def langMat (τ : Equiv.Perm ι) (e : ℤ) (i₀ : ι) : Matrix ι ι ℤ :=
  Matrix.of fun i j => (if j = i then 1 else 0) + e * (if j = τ i then 1 else 0) +
    (if i = i₀ then -e else 0)

theorem langMat_mulVec (τ : Equiv.Perm ι) (e : ℤ) (i₀ : ι) (v : ι → ℚ) (i : ι) :
    ((langMat τ e i₀).map (Int.castRingHom ℚ) *ᵥ v) i =
      v i + e * v (τ i) + (if i = i₀ then -(e : ℚ) * ∑ j, v j else 0) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, langMat, Matrix.of_apply]
  simp only [map_add, map_mul, map_intCast, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Int.cast_neg, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h <;> simp [Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem langMat_injective (τ : Equiv.Perm ι) {e : ℤ} (he : 2 ≤ e.natAbs) (i₀ : ι) (v : ι → ℚ)
    (hv : (langMat τ e i₀).map (Int.castRingHom ℚ) *ᵥ v = 0) : v = 0 := by
  have h1 : ∀ i, v i + e * v (τ i) + (if i = i₀ then -(e : ℚ) * ∑ j, v j else 0) = 0 :=
    fun i => by rw [← langMat_mulVec, hv]; rfl
  have hsum : ∑ j, v j = 0 := by
    have h2 := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i)
    simp only [Finset.sum_add_distrib, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, ← Finset.mul_sum] at h2
    rw [Equiv.sum_comp τ v] at h2
    linarith
  have h3 : ∀ i, v i = -(e : ℚ) * v (τ i) := fun i => by
    have := h1 i
    rw [hsum, mul_zero, ite_self, add_zero] at this
    linarith
  have h4 : ∀ (k : ℕ) (i : ι), v i = (-(e : ℚ)) ^ k * v ((τ ^ k) i) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have hτ : (τ ^ (k + 1)) i = τ ((τ ^ k) i) := by rw [pow_succ' τ k, Equiv.Perm.mul_apply]
      rw [ih i, h3 ((τ ^ k) i), hτ, pow_succ (-(e : ℚ)) k]
      ring
  funext i
  have hk := h4 (orderOf τ) i
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at hk
  have hpos : 0 < orderOf τ := orderOf_pos τ
  have hne : (-(e : ℚ)) ^ orderOf τ ≠ 1 := by
    intro h
    have habs : |(e : ℚ)| ^ orderOf τ = 1 := by
      have := congrArg abs h
      rwa [abs_pow, abs_neg, abs_one] at this
    have hQ' : (2 : ℚ) ≤ |(e : ℚ)| := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast he
    have : (2 : ℚ) ≤ |(e : ℚ)| ^ orderOf τ := by
      calc (2 : ℚ) ≤ |(e : ℚ)| := hQ'
        _ = |(e : ℚ)| ^ 1 := (pow_one _).symm
        _ ≤ |(e : ℚ)| ^ orderOf τ := pow_le_pow_right₀ (by linarith) hpos
    linarith
  have h5 : (1 - (-(e : ℚ)) ^ orderOf τ) * v i = 0 := by
    rw [sub_mul, one_mul]; linarith
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd (by linarith) hne
  · simpa using h

theorem langMat_det_ne_zero (τ : Equiv.Perm ι) {e : ℤ} (he : 2 ≤ e.natAbs) (i₀ : ι) :
    (langMat τ e i₀).det ≠ 0 := by
  intro h
  have hd : ((langMat τ e i₀).map (Int.castRingHom ℚ)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  exact hv0 (langMat_injective τ he i₀ v hv)

theorem monoHom_langMat_apply {G : Type*} [CommGroup G] (τ : Equiv.Perm ι) (e : ℤ) (i₀ : ι)
    (x : ι → G) (i : ι) :
    monoHom (langMat τ e i₀) x i =
      x i * x (τ i) ^ e * (if i = i₀ then (∏ j, x j) ^ (-e) else 1) := by
  simp only [monoHom_apply, langMat, Matrix.of_apply, zpow_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h1 : ∏ j, x j ^ (if j = i then (1 : ℤ) else 0) = x i := by
    have : ∀ j, x j ^ (if j = i then (1 : ℤ) else 0) = if j = i then x j else 1 := fun j => by
      split_ifs <;> simp
    simp [this, Finset.prod_ite_eq']
  have h2 : ∏ j, x j ^ (e * (if j = τ i then (1 : ℤ) else 0)) = x (τ i) ^ e := by
    have : ∀ j, x j ^ (e * (if j = τ i then (1 : ℤ) else 0)) =
        if j = τ i then x j ^ e else 1 := fun j => by
      split_ifs <;> simp
    simp [this, Finset.prod_ite_eq']
  have h3 : ∏ j, x j ^ (if i = i₀ then -e else 0) =
      if i = i₀ then (∏ j, x j) ^ (-e) else 1 := by
    split_ifs with h
    · rw [Finset.prod_zpow]
    · simp
  rw [h1, h2, h3]

theorem prod_monoHom_langMat {G : Type*} [CommGroup G] (τ : Equiv.Perm ι) (e : ℤ) (i₀ : ι)
    (x : ι → G) : ∏ i, monoHom (langMat τ e i₀) x i = ∏ j, x j := by
  simp only [monoHom_langMat_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_zpow,
    Equiv.prod_comp τ x, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have : ∀ P : G, P * P ^ e * P ^ (-e) = P := fun P => by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  exact this _

theorem exists_lang_monomial {L : Type} [Field L] [IsAlgClosed L] [Nonempty ι]
    (τ : Equiv.Perm ι) {e : ℤ} (he : 2 ≤ e.natAbs) (w : ι → Lˣ) (hw : ∏ i, w i = 1) :
    ∃ x : ι → Lˣ, ∏ i, x i = 1 ∧ ∀ i, x i * x (τ i) ^ e = w i := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨x, hx⟩ := monoHom_surjective_of_det_ne_zero (L := L) (langMat τ e i₀)
    (langMat_det_ne_zero τ he i₀) w
  have hprod : ∏ j, x j = 1 := by
    rw [← prod_monoHom_langMat τ e i₀ x, hx, hw]
  refine ⟨x, hprod, fun i => ?_⟩
  have := congrFun hx i
  rw [monoHom_langMat_apply, hprod] at this
  split_ifs at this <;> simpa using this

end Torus

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
