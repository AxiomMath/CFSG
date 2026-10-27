module

public import Mathlib.FieldTheory.Finite.Extension
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.FixedBasis

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open Module FiniteField

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance charP_extension_two (k : ℕ) [NeZero k] : CharP (FiniteField.Extension K 2 k) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_injective_algebraMap (algebraMap (ZMod 2) (FiniteField.Extension K 2 k)).injective 2

omit [CharP K 2] in
theorem pow_two_pow_mul_odd (σ : K ≃+* K) (j k : ℕ) (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) (c : K) : c ^ 2 ^ (j * k) = σ c := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨r, rfl⟩ := hk
  have h1 : ∀ r : ℕ, c ^ 2 ^ (j * (2 * r + 1)) = c ^ 2 ^ j := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      have : 2 ^ (j * (2 * (r + 1) + 1)) = 2 ^ (j * (2 * r + 1)) * 2 ^ (2 * j) := by
        rw [← pow_add]; congr 1; ring
      rw [this, pow_mul, ih, ← pow_mul, mul_comm (2^j), ← hK, pow_mul, FiniteField.pow_card]
  rw [h1, hσ]


theorem pow_pow_E (j k : ℕ) (hK : Nat.card K = 2 ^ (2 * j)) [NeZero k]
    (x : FiniteField.Extension K 2 k) : (x ^ 2 ^ (j * k)) ^ 2 ^ (j * k) = x := by
  have : Fintype (FiniteField.Extension K 2 k) := Fintype.ofFinite _
  have hE : Fintype.card (FiniteField.Extension K 2 k) = 2 ^ (2 * (j * k)) := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, hK, ← pow_mul]; ring_nf
  rw [← pow_mul, ← pow_add, ← two_mul, ← hE, FiniteField.pow_card]

@[expose] noncomputable def frobSemilinear (σ : K ≃+* K) (j k : ℕ) (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) [NeZero k] :
    FiniteField.Extension K 2 k →ₛₗ[(σ : K →+* K)] FiniteField.Extension K 2 k where
  toFun x := x ^ 2 ^ (j * k)
  map_add' x y := (iterateFrobenius (FiniteField.Extension K 2 k) 2 (j * k)).map_add x y
  map_smul' c v := by
    simp only [Algebra.smul_def, mul_pow, RingHom.coe_coe]
    rw [← map_pow, pow_two_pow_mul_odd σ j k hσ hK hk]


@[expose] noncomputable def frobProd (σ : K ≃+* K) (j k r : ℕ) (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) [NeZero k] :
    (FiniteField.Extension K 2 k × (Fin r → K)) →ₛₗ[(σ : K →+* K)]
      (FiniteField.Extension K 2 k × (Fin r → K)) where
  toFun v := (frobSemilinear σ j k hσ hK hk v.1, fun i => σ (v.2 i))
  map_add' v w := by
    ext
    · exact map_add _ _ _
    · simp
  map_smul' c v := by
    ext
    · exact map_smulₛₗ _ _ _
    · simp

theorem frobProd_apply (σ : K ≃+* K) (j k r : ℕ) (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) [NeZero k] (v) :
    frobProd σ j k r hσ hK hk v = (v.1 ^ 2 ^ (j * k), fun i => σ (v.2 i)) := rfl

theorem frobProd_frobProd (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) (j k r : ℕ) (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) [NeZero k] (v) :
    frobProd σ j k r hσ hK hk (frobProd σ j k r hσ hK hk v) = v := by
  simp only [frobProd_apply]
  ext
  · exact pow_pow_E j k hK _
  · simp [hσσ]


theorem exists_inverted_matrix (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ 1) (j k n : ℕ)
    (hσ : ∀ x, σ x = x ^ 2 ^ j) (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) (hkn : k ≤ n)
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ (2 ^ j) ^ k + 1) (hpq : ¬ p ∣ Nat.card K - 1) :
    ∃ M M' : Matrix (Fin n) (Fin n) K, M.map σ = M' ∧ M * M' = 1 ∧ M ^ p = 1 ∧ M.det = 1 ∧
      ∀ c : K, M ≠ Matrix.scalar (Fin n) c := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero k := ⟨hk.pos.ne'⟩
  have hfp : Fact p.Prime := ⟨hp⟩
  set E := FiniteField.Extension K 2 k with hE
  have hEcard : Nat.card E = 2 ^ (2 * (j * k)) := by
    rw [FiniteField.natCard_extension, hK, ← pow_mul]; ring_nf
  have hpE : p ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hEcard]
    have : 2 ^ (2 * (j * k)) - 1 = ((2 ^ j) ^ k + 1) * ((2 ^ j) ^ k - 1) := by
      have : 2 ^ (2 * (j * k)) = ((2 ^ j) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
      rw [this]
      have h3 := Nat.sq_sub_sq ((2 ^ j) ^ k) 1
      simpa using h3
    rw [this]
    exact Dvd.dvd.mul_right hpd _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpE
  set x : E := (u : E) with hxdef
  have hxp : x ^ p = 1 := by rw [hxdef, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]; rfl
  have hx0 : x ≠ 0 := u.ne_zero
  have hxτ : x ^ 2 ^ (j * k) * x = 1 := by
    have h1 : x ^ ((2 ^ j) ^ k + 1) = 1 := by
      obtain ⟨c, hc⟩ := hpd
      rw [hc, pow_mul, hxp, one_pow]
    rw [← pow_succ]
    rwa [← pow_mul] at h1
  set T := frobProd σ j k (n - k) hσ hK hk with hT
  have hTT : ∀ v, T (T v) = v := frobProd_frobProd σ hσσ j k (n - k) hσ hK hk
  have hfin : Module.finrank K (E × (Fin (n - k) → K)) = n := by
    rw [Module.finrank_prod, FiniteField.finrank_extension, Module.finrank_fin_fun]
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨b, hb⟩ := exists_basis_map_toMatrix hσσ hx₀ T hTT hfin
  let t : (E × (Fin (n - k) → K)) →ₗ[K] (E × (Fin (n - k) → K)) := (LinearMap.mulLeft K x).prodMap LinearMap.id
  let t' : (E × (Fin (n - k) → K)) →ₗ[K] (E × (Fin (n - k) → K)) := (LinearMap.mulLeft K x⁻¹).prodMap LinearMap.id
  have htT : ∀ v, T (t v) = t' (T v) := by
    intro v
    simp only [hT, frobProd_apply, t, t', LinearMap.prodMap_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply, mul_pow]
    ext
    · simp only
      rw [eq_inv_of_mul_eq_one_left hxτ]
    · rfl
  have htt' : t * t' = 1 := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp [t, t', mul_inv_cancel_left₀ hx0]
    · simp [t, t']
  have htpow : ∀ m : ℕ, ∀ v : E × (Fin (n - k) → K), (t ^ m) v = (x ^ m * v.1, v.2) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply]
      simp only [t, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, LinearMap.id_apply]
      rw [ih]
      simp only [pow_succ]
      ext
      · simp only; ring
      · rfl
  have htp : t ^ p = 1 := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp [htpow, hxp]
    · simp [htpow]
  have hmat_pow : ∀ m : ℕ, LinearMap.toMatrix b b (t ^ m) = (LinearMap.toMatrix b b t) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]
  have hMM' : LinearMap.toMatrix b b t * LinearMap.toMatrix b b t' = 1 := by
    rw [← LinearMap.toMatrix_mul, htt', LinearMap.toMatrix_one]
  have hMp : (LinearMap.toMatrix b b t) ^ p = 1 := by
    rw [← hmat_pow, htp, LinearMap.toMatrix_one]
  have : Fintype K := Fintype.ofFinite K
  have hpq' : ¬ p ∣ Fintype.card K - 1 := by rwa [← Nat.card_eq_fintype_card]
  refine ⟨LinearMap.toMatrix b b t, LinearMap.toMatrix b b t', hb t t' htT, hMM', hMp, ?_, ?_⟩
  · have hd0 : (LinearMap.toMatrix b b t).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hMM'
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have h1 : (LinearMap.toMatrix b b t).det ^ p = 1 := by
      rw [← Matrix.det_pow, hMp, Matrix.det_one]
    have h2 := FiniteField.pow_card_sub_one_eq_one _ hd0
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩ 
    rwa [(Nat.Prime.coprime_iff_not_dvd hp).mpr hpq', pow_one] at h3
  · intro c hc
    have htc : t = c • LinearMap.id := by
      refine (LinearMap.toMatrix b b).injective ?_
      rw [hc, map_smul, LinearMap.toMatrix_id]
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    have h1 := congrArg (fun f : (E × (Fin (n - k) → K)) →ₗ[K] (E × (Fin (n - k) → K)) =>
      (f ((1 : E), (0 : Fin (n - k) → K))).1) htc
    simp only [t, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Prod.smul_mk, mul_one] at h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact hx0 h1
    have h2 : x ^ (Fintype.card K - 1) = 1 := by
      rw [h1, Algebra.smul_def, mul_one, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ hc0,
        map_one]
    have h3 : u ^ (Fintype.card K - 1) = 1 := Units.ext (by simpa [hxdef] using h2)
    exact hpq' (hu ▸ orderOf_dvd_of_pow_eq_one h3)

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
