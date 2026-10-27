module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabDefs

public section

namespace CFSG.LieType.SeitzGeneration.HeisP

open Matrix Fin.NatCast

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

private def twistP (α : K) (b : Fin p) : K := if (b : ℕ) + 1 = p then α else 1

private def adjP (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun a b => σ (M b a)

private def adP (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) :
    Module.End K (Matrix (Fin p) (Fin p) K) :=
  LinearMap.mulLeft K M ∘ₗ LinearMap.mulRight K (adjP σ M)

private theorem twistP_ne_zero {α : K} (hα : α ≠ 0) (b : Fin p) : twistP α b ≠ 0 := by
  unfold twistP
  split_ifs
  · exact hα
  · exact one_ne_zero

private theorem star_twistP (σ : K ≃+* K) {α : K} (hασ : σ α * α = 1) (b : Fin p) :
    σ (twistP α b) * twistP α b = 1 := by
  unfold twistP
  split_ifs
  · exact hασ
  · simp

private theorem Gj_apply' (ζ α : K) (j : ℕ) (a b : Fin p) :
    Gj ζ α j a b = if a = b + 1 then ζ ^ (j * (b : ℕ)) * twistP α b else 0 := rfl

private theorem Gj_zero_apply (ζ α : K) (a b : Fin p) :
    Gj ζ α 0 a b = if a = b + 1 then twistP α b else 0 := by
  rw [Gj_apply']
  simp

private theorem Zm_pow_apply' (ζ : K) (k : ℕ) :
    Zm ζ ^ k = Matrix.diagonal fun a : Fin p => (ζ ^ (a : ℕ)) ^ k := by
  rw [Zm, Matrix.diagonal_pow]
  rfl

private theorem wh_pow_p {ζ : K} (hζ : ζ ^ p = 1) (n : ℕ) : (ζ ^ n) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem Zm_pow_p' {ζ : K} (hζ : ζ ^ p = 1) : Zm (p := p) ζ ^ p = 1 := by
  rw [Zm_pow_apply', ← Matrix.diagonal_one]
  congr 1
  funext a
  exact wh_pow_p hζ (a : ℕ)

private theorem Gj_eq_mul_Zm_pow' (ζ α : K) (j : ℕ) :
    Gj (p := p) ζ α j = Gj ζ α 0 * Zm ζ ^ j := by
  ext a b
  rw [Zm_pow_apply', Matrix.mul_diagonal]
  simp only [Gj_apply', Gj_zero_apply, zero_mul, pow_zero, one_mul]
  split_ifs
  · ring
  · ring

private theorem diagonal_mul_Zm (v : Fin p → K) (ζ : K) :
    Matrix.diagonal v * Zm ζ = Zm ζ * Matrix.diagonal v := by
  rw [Zm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

private theorem wh_pow_mod {ζ : K} (hζ : ζ ^ p = 1) (n : ℕ) : ζ ^ (n % p) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζ, one_pow, mul_one]

private theorem wh_val_add_one (b : Fin p) : ((b + 1 : Fin p) : ℕ) = ((b : ℕ) + 1) % p := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

private theorem Zm_mul_Gj_zero {ζ α : K} (hζ : ζ ^ p = 1) :
    Zm (p := p) ζ * Gj ζ α 0 = ζ • (Gj ζ α 0 * Zm ζ) := by
  ext a b
  simp only [Zm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Gj_zero_apply]
  by_cases h : a = b + 1
  · subst h
    rw [if_pos rfl, wh_val_add_one, wh_pow_mod hζ, pow_succ]
    ring
  · simp [h]

private theorem Zm_mul_Gj_zero_pow {ζ α : K} (hζ : ζ ^ p = 1) (k : ℕ) :
    Zm (p := p) ζ * Gj ζ α 0 ^ k = (ζ ^ k) • (Gj ζ α 0 ^ k * Zm ζ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (Gj ζ α 0) k, ← mul_assoc, ih, smul_mul_assoc,
      mul_assoc (Gj ζ α 0 ^ k) (Zm ζ) (Gj ζ α 0), Zm_mul_Gj_zero hζ, mul_smul_comm, smul_smul,
      pow_succ ζ k, mul_assoc (Gj ζ α 0 ^ k) (Gj ζ α 0) (Zm ζ)]

private theorem Zm_mul_Gj_zero_pow_p {ζ α : K} (hζ : ζ ^ p = 1) :
    Zm (p := p) ζ * Gj ζ α 0 ^ p = Gj ζ α 0 ^ p * Zm ζ := by
  rw [Zm_mul_Gj_zero_pow hζ p, hζ, one_smul]

private theorem Gj_pow_p_offdiag {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (a b : Fin p)
    (hab : a ≠ b) : (Gj ζ α 0 ^ p) a b = 0 := by
  have h := congrArg (fun M : Matrix (Fin p) (Fin p) K => M a b)
    (Zm_mul_Gj_zero_pow_p (α := α) hζ.pow_eq_one)
  simp only [Zm, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  have hne : ζ ^ (a : ℕ) ≠ ζ ^ (b : ℕ) := fun e => hab (Fin.ext (hζ.pow_inj a.isLt b.isLt e))
  have h2 : (ζ ^ (a : ℕ) - ζ ^ (b : ℕ)) * (Gj ζ α 0 ^ p) a b = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · exact h3

private theorem Gj_pow_p_diag_succ {ζ α : K} (hα : α ≠ 0) (x : Fin p) :
    (Gj ζ α 0 ^ p) (x + 1) (x + 1) = (Gj ζ α 0 ^ p) x x := by
  have hUT : Gj (p := p) ζ α 0 ^ p * Gj ζ α 0 = Gj ζ α 0 * Gj ζ α 0 ^ p := by
    rw [← pow_succ, pow_succ']
  have hc := congrArg (fun M : Matrix (Fin p) (Fin p) K => M (x + 1) x) hUT
  simp only [Matrix.mul_apply] at hc
  have e1 : ∑ k, (Gj ζ α 0 ^ p) (x + 1) k * Gj ζ α 0 k x
      = (Gj ζ α 0 ^ p) (x + 1) (x + 1) * Gj ζ α 0 (x + 1) x := by
    apply Finset.sum_eq_single
    · intro k _ hk
      simp [Gj_zero_apply, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e2 : ∑ k, Gj ζ α 0 (x + 1) k * (Gj ζ α 0 ^ p) k x
      = Gj ζ α 0 (x + 1) x * (Gj ζ α 0 ^ p) x x := by
    apply Finset.sum_eq_single x
    · intro k _ hk
      simp [Gj_zero_apply, hk, Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [e1, e2] at hc
  simp only [Gj_zero_apply, eq_self_iff_true, if_true] at hc
  exact mul_right_cancel₀ (twistP_ne_zero hα x) (hc.trans (mul_comm _ _))

private theorem Gj_pow_p_diag_const {ζ α : K} (hα : α ≠ 0) (x : Fin p) :
    (Gj ζ α 0 ^ p) x x = (Gj (p := p) ζ α 0 ^ p) 0 0 := by
  have key : ∀ n : ℕ, (Gj (p := p) ζ α 0 ^ p) (n : Fin p) (n : Fin p)
      = (Gj (p := p) ζ α 0 ^ p) 0 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, Gj_pow_p_diag_succ hα, ih]
  have h := key x.val
  rwa [Fin.cast_val_eq_self] at h

private theorem Gj_pow_p_eq_smul {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (hα : α ≠ 0) :
    Gj (p := p) ζ α 0 ^ p = (Gj (p := p) ζ α 0 ^ p) 0 0 • (1 : Matrix (Fin p) (Fin p) K) := by
  ext a b
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : a = b
  · subst h
    simp [Gj_pow_p_diag_const hα a]
  · simp [h, Gj_pow_p_offdiag hζ a b h]

private theorem adjP_apply (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) (a b : Fin p) :
    adjP σ M a b = σ (M b a) := rfl

private theorem adjP_mul (σ : K ≃+* K) (M N : Matrix (Fin p) (Fin p) K) :
    adjP σ (M * N) = adjP σ N * adjP σ M := by
  ext a b
  simp only [adjP_apply, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem adjP_one (σ : K ≃+* K) : adjP σ (1 : Matrix (Fin p) (Fin p) K) = 1 := by
  ext a b
  rw [adjP_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem adjP_pow (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) (k : ℕ) :
    adjP σ (M ^ k) = adjP σ M ^ k := by
  induction k with
  | zero => simp [adjP_one]
  | succ k ih => rw [pow_succ, adjP_mul, ih, pow_succ']

private theorem adjP_adjP (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    (M : Matrix (Fin p) (Fin p) K) : adjP σ (adjP σ M) = M := by
  ext a b
  simp [adjP_apply, hσ]

private theorem adjP_smul (σ : K ≃+* K) (c : K) (M : Matrix (Fin p) (Fin p) K) :
    adjP σ (c • M) = σ c • adjP σ M := by
  ext a b
  simp [adjP_apply]

private theorem adjP_sub (σ : K ≃+* K) (X Y : Matrix (Fin p) (Fin p) K) :
    adjP σ (X - Y) = adjP σ X - adjP σ Y := by
  ext a b
  simp [adjP_apply]

private theorem adjP_sum (σ : K ≃+* K) {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin p) (Fin p) K) :
    adjP σ (∑ i ∈ s, X i) = ∑ i ∈ s, adjP σ (X i) := by
  ext a b
  simp [adjP_apply, Matrix.sum_apply]

private theorem adjP_diagonal (σ : K ≃+* K) (v : Fin p → K) :
    adjP σ (Matrix.diagonal v) = Matrix.diagonal fun a => σ (v a) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [adjP_apply]
  · simp [adjP_apply, Matrix.diagonal_apply, h, Ne.symm h]

private theorem adjP_eq_iff (σ : K ≃+* K) (X : Matrix (Fin p) (Fin p) K) :
    adjP σ X = X ↔ ∀ a b, σ (X b a) = X a b := by
  constructor
  · intro h a b
    have h1 := adjP_apply σ X a b
    rw [h] at h1
    exact h1.symm
  · intro h
    ext a b
    rw [adjP_apply]
    exact h a b

private theorem adP_apply (σ : K ≃+* K) (M S : Matrix (Fin p) (Fin p) K) :
    adP σ M S = M * (S * adjP σ M) := rfl

private theorem adP_mul (σ : K ≃+* K) (M N : Matrix (Fin p) (Fin p) K) :
    adP σ (M * N) = adP σ M * adP σ N := by
  ext S : 1
  simp only [Module.End.mul_apply, adP_apply, adjP_mul, Matrix.mul_assoc]

private theorem adP_one (σ : K ≃+* K) : adP σ (1 : Matrix (Fin p) (Fin p) K) = 1 := by
  ext S : 1
  simp [adP_apply, adjP_one]

private theorem adP_pow (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) (k : ℕ) :
    adP σ (M ^ k) = adP σ M ^ k := by
  induction k with
  | zero => simp [adP_one]
  | succ k ih => rw [pow_succ, adP_mul, ih, pow_succ]

private theorem adP_smul_of_unit (σ : K ≃+* K) {c : K} (hc : σ c * c = 1)
    (M : Matrix (Fin p) (Fin p) K) : adP σ (c • M) = adP σ M := by
  have hc' : c * σ c = 1 := by rw [mul_comm]; exact hc
  ext S : 1
  simp only [adP_apply, adjP_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hc, hc', one_smul]

private theorem commute_adP_T_Z (σ : K ≃+* K) {ζ α : K} (hζ : ζ ^ p = 1)
    (hζσ : σ ζ * ζ = 1) : Commute (adP σ (Gj (p := p) ζ α 0)) (adP σ (Zm ζ)) := by
  show adP σ (Gj ζ α 0) * adP σ (Zm ζ) = adP σ (Zm ζ) * adP σ (Gj ζ α 0)
  rw [← adP_mul, ← adP_mul, Zm_mul_Gj_zero hζ, adP_smul_of_unit σ hζσ]

private theorem adP_Gj_pow (σ : K ≃+* K) {ζ α : K} (hζ : ζ ^ p = 1) (hζσ : σ ζ * ζ = 1)
    (j i : ℕ) :
    adP σ (Gj (p := p) ζ α j) ^ i = adP σ (Gj ζ α 0) ^ i * adP σ (Zm ζ) ^ (j * i) := by
  rw [Gj_eq_mul_Zm_pow' ζ α j, adP_mul, adP_pow,
    ((commute_adP_T_Z σ hζ hζσ).pow_right j).mul_pow, ← pow_mul]

private theorem adP_Zm_pow_p (σ : K ≃+* K) {ζ : K} (hζ : ζ ^ p = 1) :
    adP σ (Zm (p := p) ζ) ^ p = 1 := by
  rw [← adP_pow, Zm_pow_p' hζ, adP_one]

private theorem adjP_pow_mul_pow (σ : K ≃+* K) (M : Matrix (Fin p) (Fin p) K) (k : ℕ)
    (hM : adjP σ M * M = 1) : adjP σ (M ^ k) * M ^ k = 1 := by
  have hM' : M * adjP σ M = 1 := mul_eq_one_comm.mp hM
  have hc : Commute (adjP σ M) M := by
    show adjP σ M * M = M * adjP σ M
    rw [hM, hM']
  rw [adjP_pow, ← hc.mul_pow, hM, one_pow]

private theorem adjP_mul_Gj (σ : K ≃+* K) {ζ α : K} (hζσ : σ ζ * ζ = 1) (hασ : σ α * α = 1)
    (j : ℕ) : adjP σ (Gj (p := p) ζ α j) * Gj ζ α j = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (a + 1)]
  · by_cases hab : a = b
    · subst hab
      have e1 : σ ζ ^ (j * (a : ℕ)) * ζ ^ (j * (a : ℕ)) = 1 := by
        rw [← mul_pow, hζσ, one_pow]
      have e2 := star_twistP σ hασ a
      simp only [adjP_apply, Gj_apply', eq_self_iff_true, if_true, map_mul, map_pow]
      linear_combination (σ (twistP α a) * twistP α a) * e1 + e2
    · simp [adjP_apply, Gj_apply', hab]
  · intro k _ hk
    simp [adjP_apply, Gj_apply', hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem adP_Gj_zero_pow_p (σ : K ≃+* K) {ζ α : K} (hζ : IsPrimitiveRoot ζ p)
    (hα : α ≠ 0) (hζσ : σ ζ * ζ = 1) (hασ : σ α * α = 1) :
    adP σ (Gj (p := p) ζ α 0) ^ p = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : K, Gj (p := p) ζ α 0 ^ p = u • (1 : Matrix (Fin p) (Fin p) K) :=
    ⟨_, Gj_pow_p_eq_smul hζ hα⟩
  have hpow := adjP_pow_mul_pow σ (Gj (p := p) ζ α 0) p (adjP_mul_Gj σ hζσ hασ 0)
  rw [hu, adjP_smul, adjP_one] at hpow
  have hσu : σ u * u = 1 := by
    have h0 := congrArg (fun M : Matrix (Fin p) (Fin p) K => M 0 0) hpow
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h0
    linear_combination h0
  rw [← adP_pow, hu, adP_smul_of_unit σ hσu, adP_one]

private theorem adP_Gj_pow_p (σ : K ≃+* K) {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (hα : α ≠ 0)
    (hζσ : σ ζ * ζ = 1) (hασ : σ α * α = 1) (j : ℕ) :
    adP σ (Gj (p := p) ζ α j) ^ p = 1 := by
  rw [adP_Gj_pow σ hζ.pow_eq_one hζσ j p, adP_Gj_zero_pow_p σ hζ hα hζσ hασ, one_mul,
    pow_mul', adP_Zm_pow_p σ hζ.pow_eq_one, one_pow]

private theorem adP_Zm_pow_apply (σ : K ≃+* K) {ζ : K} (hζσ : σ ζ = ζ⁻¹) (k : ℕ)
    (S : Matrix (Fin p) (Fin p) K) (a b : Fin p) :
    (adP σ (Zm ζ) ^ k) S a b = (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ k * S a b := by
  rw [← adP_pow, Zm_pow_apply', adP_apply, adjP_diagonal]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, map_pow, hζσ, inv_pow]
  rw [mul_pow]
  ring

private theorem sum_adP_Zm_pow (σ : K ≃+* K) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hζσ : σ ζ = ζ⁻¹) (i : ℕ) (hi : ¬ p ∣ i) (S : Matrix (Fin p) (Fin p) K) :
    ∑ j : Fin p, (adP σ (Zm ζ) ^ ((j : ℕ) * i)) S
      = (p : K) • Matrix.diagonal (fun a => S a a) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  ext a b
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  simp only [adP_Zm_pow_apply σ hζσ]
  rw [← Finset.sum_mul]
  by_cases h : a = b
  · subst h
    have hw : ζ ^ (a : ℕ) * (ζ ^ (a : ℕ))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hζ0)
    simp [hw]
  · have hne : ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹ ≠ 1 := by
      intro h1
      rw [mul_inv_eq_one₀ (pow_ne_zero _ hζ0)] at h1
      exact h (Fin.ext (hζ.pow_inj a.isLt b.isLt h1))
    have hwp : (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, wh_pow_p hζp, wh_pow_p hζp, inv_one, mul_one]
    have hxp : ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) ^ p = 1 := by
      rw [← pow_mul, mul_comm i p, pow_mul, hwp, one_pow]
    have hx1 : (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i ≠ 1 := by
      intro h1
      have hcop : Nat.gcd i p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi)
      have h2 := (pow_gcd_eq_one).mpr ⟨h1, hwp⟩
      rw [hcop, pow_one] at h2
      exact hne h2
    have hsum : ∑ j : Fin p, (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ ((j : ℕ) * i) = 0 := by
      have hg : ∀ j : Fin p, (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ ((j : ℕ) * i)
          = ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) ^ (j : ℕ) := by
        intro j
        rw [← pow_mul, Nat.mul_comm (j : ℕ) i]
      simp only [hg]
      have h1 : ∑ j : Fin p, ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) ^ (j : ℕ)
          = ∑ j ∈ Finset.range p, ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) ^ j :=
        Fin.sum_univ_eq_sum_range (fun j => ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) ^ j) p
      rw [h1]
      have h3 := geom_sum_mul ((ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ i) p
      rw [hxp, sub_self] at h3
      exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hx1)
    rw [hsum]
    simp [h]

private theorem adP_T_diagonal (σ : K ≃+* K) {ζ α : K} (hασ : σ α * α = 1) (d : Fin p → K) :
    adP σ (Gj ζ α 0) (Matrix.diagonal d) = Matrix.diagonal (fun a => d (a - 1)) := by
  ext a b
  rw [adP_apply, Matrix.diagonal_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, adjP_apply, Gj_zero_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single (a - 1)]
    · simp only [sub_add_cancel, eq_self_iff_true, if_true]
      linear_combination (d (a - 1)) * star_twistP σ hασ (a - 1)
    · intro l _ hl
      have hne : ¬ a = l + 1 := fun h => hl (by rw [h, add_sub_cancel_right])
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro l _
    by_cases h1 : a = l + 1
    · have h2 : ¬ b = l + 1 := fun h2 => hab (h1.trans h2.symm)
      simp [h1, h2]
    · simp [h1]

private theorem adP_T_pow_diagonal (σ : K ≃+* K) {ζ α : K} (hασ : σ α * α = 1)
    (d : Fin p → K) (i : ℕ) :
    (adP σ (Gj ζ α 0) ^ i) (Matrix.diagonal d)
      = Matrix.diagonal (fun a => d (a - (i : Fin p))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, adP_T_diagonal σ hασ]
    congr 1
    funext a
    show d (a - 1 - (i : Fin p)) = d (a - ((i + 1 : ℕ) : Fin p))
    rw [Nat.cast_succ, sub_sub, add_comm 1]

private theorem sum_adP_T_diagonal (σ : K ≃+* K) {ζ α : K} (hασ : σ α * α = 1)
    (d : Fin p → K) :
    ∑ i : Fin p, (adP σ (Gj ζ α 0) ^ (i : ℕ)) (Matrix.diagonal d)
      = (∑ x, d x) • (1 : Matrix (Fin p) (Fin p) K) := by
  simp only [adP_T_pow_diagonal σ hασ, Fin.cast_val_eq_self]
  ext a b
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq, eq_self_iff_true, if_true, mul_one]
    exact Equiv.sum_comp (Equiv.subLeft a) d
  · simp [Matrix.diagonal_apply, h]

private theorem sum_Gj_twirl (σ : K ≃+* K) {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (hζσ : σ ζ = ζ⁻¹) (hζσ' : σ ζ * ζ = 1) (hασ : σ α * α = 1)
    (S : Matrix (Fin p) (Fin p) K) :
    ∑ j : Fin p, (p : K)⁻¹ • ∑ i : Fin p, (adP σ (Gj ζ α j) ^ (i : ℕ)) S
      = (∑ x, S x x) • (1 : Matrix (Fin p) (Fin p) K) + (S - Matrix.diagonal (fun a => S a a)) := by
  have hX : ∀ i : Fin p, ∑ j : Fin p, (adP σ (Zm ζ) ^ ((j : ℕ) * (i : ℕ))) S
      = (p : K) • Matrix.diagonal (fun a => S a a) +
        (if i = 0 then (p : K) • (S - Matrix.diagonal (fun a => S a a)) else 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have h0 : ∀ j : Fin p, (adP σ (Zm ζ) ^ ((j : ℕ) * ((0 : Fin p) : ℕ))) S = S := by
        intro j
        simp
      simp only [h0, eq_self_iff_true, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K,
        ← smul_add]
      congr 1
      abel
    · rw [if_neg hi, add_zero]
      exact sum_adP_Zm_pow σ hζ hp hζσ (i : ℕ)
        (fun hd => hi (Fin.ext (Nat.eq_zero_of_dvd_of_lt hd i.isLt))) S
  have hL : ∑ j : Fin p, (p : K)⁻¹ • ∑ i : Fin p, (adP σ (Gj ζ α j) ^ (i : ℕ)) S
      = (p : K)⁻¹ • ∑ i : Fin p, (adP σ (Gj ζ α 0) ^ (i : ℕ))
          (∑ j : Fin p, (adP σ (Zm ζ) ^ ((j : ℕ) * (i : ℕ))) S) := by
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [adP_Gj_pow σ hζ.pow_eq_one hζσ' j i, Module.End.mul_apply]
  have hR : ∑ i : Fin p, (adP σ (Gj ζ α 0) ^ (i : ℕ))
      (∑ j : Fin p, (adP σ (Zm ζ) ^ ((j : ℕ) * (i : ℕ))) S)
      = (p : K) • ((∑ x, S x x) • (1 : Matrix (Fin p) (Fin p) K))
        + (p : K) • (S - Matrix.diagonal (fun a => S a a)) := by
    simp only [hX, map_add, map_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, sum_adP_T_diagonal σ hασ]
    congr 1
    rw [Finset.sum_eq_single (0 : Fin p)]
    · simp
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR]
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hpK, inv_mul_cancel_left₀ hpK, one_mul, one_smul]

private theorem sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (hn : f n = f 0) : ∑ i ∈ Finset.range n, f (i + 1) = ∑ i ∈ Finset.range n, f i := by
  have h1 := Finset.sum_range_succ' f n
  have h2 := Finset.sum_range_succ f n
  rw [hn] at h2
  rw [h1] at h2
  exact add_right_cancel h2

private theorem sum_fin_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (hf : f p = f 0) :
    ∑ i : Fin p, f ((i : ℕ) + 1) = ∑ i : Fin p, f i := by
  have h1 : ∑ i : Fin p, f ((i : ℕ) + 1) = ∑ i ∈ Finset.range p, f (i + 1) :=
    Fin.sum_univ_eq_sum_range (fun m => f (m + 1)) p
  have h2 : ∑ i : Fin p, f (i : ℕ) = ∑ i ∈ Finset.range p, f i :=
    Fin.sum_univ_eq_sum_range f p
  rw [h1, h2]
  exact sum_range_shift f p hf

private theorem adjP_adP (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (M X : Matrix (Fin p) (Fin p) K)
    (hX : adjP σ X = X) : adjP σ (adP σ M X) = adP σ M X := by
  simp only [adP_apply, adjP_mul, adjP_adjP σ hσ, hX, Matrix.mul_assoc]

private theorem adjP_adP_pow (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (M S : Matrix (Fin p) (Fin p) K)
    (hS : adjP σ S = S) (i : ℕ) : adjP σ ((adP σ M ^ i) S) = (adP σ M ^ i) S := by
  induction i with
  | zero => simpa using hS
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact adjP_adP σ hσ M _ ih

private theorem fix_sum_pow {F : Module.End K (Matrix (Fin p) (Fin p) K)} (hF : F ^ p = 1)
    (S : Matrix (Fin p) (Fin p) K) (c : K) :
    F (c • ∑ i : Fin p, (F ^ (i : ℕ)) S) = c • ∑ i : Fin p, (F ^ (i : ℕ)) S := by
  have hfp : (F ^ p) S = (F ^ 0) S := by rw [hF, pow_zero]
  have h : ∀ i : Fin p, F ((F ^ (i : ℕ)) S) = (F ^ ((i : ℕ) + 1)) S := fun i => by
    rw [pow_succ', Module.End.mul_apply]
  rw [map_smul, map_sum]
  congr 1
  simp only [h]
  exact sum_fin_shift (fun m => (F ^ m) S) hfp

private theorem commute_of_fix {σ : K ≃+* K} {G Q : Matrix (Fin p) (Fin p) K}
    (hunit : adjP σ G * G = 1) (hfix : adP σ G Q = Q) : Q * G = G * Q := by
  rw [adP_apply] at hfix
  calc Q * G = (G * (Q * adjP σ G)) * G := by rw [hfix]
    _ = G * (Q * (adjP σ G * G)) := by simp only [Matrix.mul_assoc]
    _ = G * Q := by rw [hunit, mul_one]

private theorem adjP_fix_sum (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (M S : Matrix (Fin p) (Fin p) K)
    (hS : adjP σ S = S) (c : K) (hc : σ c = c) :
    adjP σ (c • ∑ i : Fin p, (adP σ M ^ (i : ℕ)) S)
      = c • ∑ i : Fin p, (adP σ M ^ (i : ℕ)) S := by
  rw [adjP_smul, hc, adjP_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => adjP_adP_pow σ hσ M S hS i

theorem decompP {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ⁻¹) (hα : α ≠ 0)
    (hασ : σ α = α⁻¹) (S : Matrix (Fin p) (Fin p) K) (hS : ∀ a b, σ (S b a) = S a b) :
    ∃ Q : Fin (p + 1) → Matrix (Fin p) (Fin p) K, (∀ i a b, σ (Q i b a) = Q i a b) ∧
      Q 0 * Zm ζ = Zm ζ * Q 0 ∧ (∀ j : Fin p, Q j.succ * Gj ζ α j = Gj ζ α j * Q j.succ) ∧
      S = ∑ i, Q i := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζσ' : σ ζ * ζ = 1 := by rw [hζσ, inv_mul_cancel₀ hζ0]
  have hασ' : σ α * α = 1 := by rw [hασ, inv_mul_cancel₀ hα]
  have hSadj : adjP σ S = S := by
    ext a b
    rw [adjP_apply]
    exact hS a b
  have hτ : σ (∑ x, S x x) = ∑ x, S x x := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => hS x x
  have hD : adjP σ (Matrix.diagonal fun a => S a a) = Matrix.diagonal fun a => S a a := by
    rw [adjP_diagonal]
    congr 1
    funext a
    exact hS a a
  have hcp : σ ((p : K)⁻¹) = (p : K)⁻¹ := by
    rw [map_inv₀, map_natCast]
  obtain ⟨Q0, hQ0⟩ : ∃ Q0 : Matrix (Fin p) (Fin p) K,
      Q0 = Matrix.diagonal (fun a => S a a) - (∑ x, S x x) • (1 : Matrix (Fin p) (Fin p) K) :=
    ⟨_, rfl⟩
  obtain ⟨Qs, hQs⟩ : ∃ Qs : Fin p → Matrix (Fin p) (Fin p) K,
      ∀ j, Qs j = (p : K)⁻¹ • ∑ i : Fin p, (adP σ (Gj ζ α j) ^ (i : ℕ)) S :=
    ⟨_, fun _ => rfl⟩
  have hQ0h : adjP σ Q0 = Q0 := by
    rw [hQ0, adjP_sub, adjP_smul, adjP_one, hD, hτ]
  have hQsh : ∀ j, adjP σ (Qs j) = Qs j := by
    intro j
    rw [hQs j]
    exact adjP_fix_sum σ hσ (Gj ζ α j) S hSadj ((p : K)⁻¹) hcp
  refine ⟨(Fin.cons Q0 Qs : Fin (p + 1) → Matrix (Fin p) (Fin p) K), ?_, ?_, ?_, ?_⟩
  · intro i a b
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact (adjP_eq_iff σ Q0).mp hQ0h a b
    | succ j =>
      rw [Fin.cons_succ]
      exact (adjP_eq_iff σ (Qs j)).mp (hQsh j) a b
  · rw [Fin.cons_zero, hQ0]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, diagonal_mul_Zm]
  · intro j
    rw [Fin.cons_succ, hQs j]
    exact commute_of_fix (adjP_mul_Gj σ hζσ' hασ' j)
      (fix_sum_pow (adP_Gj_pow_p σ hζ hα hζσ' hασ' j) S _)
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hQ0]
    simp only [hQs]
    rw [sum_Gj_twirl σ hζ hp hpK hζσ hζσ' hασ' S]
    abel

end CFSG.LieType.SeitzGeneration.HeisP
