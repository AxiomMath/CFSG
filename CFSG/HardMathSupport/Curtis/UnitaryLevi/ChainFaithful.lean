module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.GradedAction
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def chainFil (B : V →ₛₗ[σ] V →ₗ[K] K) (s : ℕ) (W : ℕ → Submodule K V) (i : ℕ) :
    Submodule K V :=
  if i = 0 then ⊥ else if i ≤ s then W i else if i ≤ 2 * s then (W (2 * s + 1 - i)).orthogonalBilin B
    else ⊤

theorem chainFil_zero (B : V →ₛₗ[σ] V →ₗ[K] K) (s : ℕ) (W : ℕ → Submodule K V) :
    chainFil B s W 0 = ⊥ := by simp [chainFil]

theorem chainFil_of_le {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V} {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ s) : chainFil B s W i = W i := by
  simp [chainFil, show i ≠ 0 by omega, h2]

theorem chainFil_of_dual {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V} {i : ℕ}
    (h1 : s < i) (h2 : i ≤ 2 * s) :
    chainFil B s W i = (W (2 * s + 1 - i)).orthogonalBilin B := by
  simp [chainFil, show i ≠ 0 by omega, show ¬ i ≤ s by omega, h2]

theorem chainFil_of_gt {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V} {i : ℕ}
    (h : 2 * s < i) : chainFil B s W i = ⊤ := by
  simp [chainFil, show i ≠ 0 by omega, show ¬ i ≤ s by omega, show ¬ i ≤ 2 * s by omega]

theorem eq_one_of_trivial_on_pieces [CharP K 2] {B : V →ₛₗ[σ] V →ₗ[K] K}
    (s : ℕ) (W : ℕ → Submodule K V) (hW0 : W 0 = ⊥)
    (g : LinearMap.GeneralLinearGroup K V)
    (hiso : ∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w)
    (hst : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (g : Module.End K V) v ∈ W j)
    (hP : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (g : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) → (g : Module.End K V) v - v ∈ W s)
    {k : ℕ} (hg : g ^ 3 ^ k = 1) (hs : 1 ≤ s) : g = 1 := by
  have hpow : ∀ j, 1 ≤ j → j ≤ s → ∀ n : ℕ, ∀ v ∈ W j, ((g ^ n : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) v ∈ W j := by
    intro j hj1 hjs n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Units.val_mul, Module.End.mul_apply]
      exact ih _ (hst j hj1 hjs v hv)
  have hinv : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) v ∈ W j := by
    intro j hj1 hjs v hv
    have h3k : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have : g⁻¹ = g ^ (3 ^ k - 1) := by
      have h1 : g ^ (3 ^ k - 1) * g = 1 := by rw [← pow_succ, Nat.sub_add_cancel h3k, hg]
      exact inv_eq_of_mul_eq_one_left h1
    rw [this]
    exact hpow j hj1 hjs _ v hv
  have hdual : ∀ a, a < s → ∀ v, (∀ w ∈ W a, B w v = 0) →
      ∀ w ∈ W (a + 1), B w ((g : Module.End K V) v - v) = 0 := by
    intro a has v hv w hw
    have h1 : ((g : Module.End K V) w - w) ∈ W a := by
      have := hP (a + 1) (by omega) (by omega) w hw
      simpa using this
    have h2 : ∀ u ∈ W a, B u ((g : Module.End K V) v) = 0 := by
      intro u hu
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [hW0, Submodule.mem_bot] at hu
        simp [hu]
      · have := hiso (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) u) v
        have e : (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
            Module.End K V) u) = u := by
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
          rfl
        rw [e] at this
        rw [this]
        exact hv _ (hinv a ha (by omega) u hu)
    have h3 := hiso w v
    rw [map_sub, ← h3]
    have e : B w ((g : Module.End K V) v) - B ((g : Module.End K V) w) ((g : Module.End K V) v) =
        - B ((g : Module.End K V) w - w) ((g : Module.End K V) v) := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    rw [e, h2 _ h1, neg_zero]
  have hs' : 1 ≤ s := hs
  have htriv : ∀ i, ∀ v ∈ chainFil B s W (i + 1),
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) v ∈ chainFil B s W i := by
    intro i v hv
    have hgm : ((g : Module.End K V) - 1) v = (g : Module.End K V) v - v := by simp
    rw [hgm]
    by_cases hi0 : i = 0
    · subst hi0
      rw [chainFil_zero]
      rw [chainFil_of_le (by omega) hs'] at hv
      simpa [hW0] using hP 1 le_rfl hs v hv
    · by_cases hi1 : i < s
      · rw [chainFil_of_le (by omega) (by omega)] at hv
        rw [chainFil_of_le (by omega) (by omega)]
        simpa using hP (i + 1) (by omega) (by omega) v hv
      · by_cases his : i = s
        · subst his
          rw [chainFil_of_le (by omega) le_rfl]
          rw [chainFil_of_dual (by omega) (by omega)] at hv
          have : 2 * i + 1 - (i + 1) = i := by omega
          rw [this, Submodule.mem_orthogonalBilin] at hv
          exact hM v fun w hw => hv w hw
        · have hi2 : s < i := by omega
          by_cases hi3 : i < 2 * s
          · rw [chainFil_of_dual hi2 (by omega)]
            rw [chainFil_of_dual (by omega) (by omega)] at hv
            have e1 : 2 * s + 1 - (i + 1) = 2 * s - i := by omega
            have e2 : 2 * s + 1 - i = (2 * s - i) + 1 := by omega
            rw [e1, Submodule.mem_orthogonalBilin] at hv
            rw [e2, Submodule.mem_orthogonalBilin]
            intro w hw
            exact hdual (2 * s - i) (by omega) v (fun w' hw' => hv w' hw') w hw
          · by_cases hi4 : i = 2 * s
            · subst hi4
              rw [chainFil_of_dual (by omega) le_rfl]
              have e2 : 2 * s + 1 - 2 * s = 0 + 1 := by omega
              rw [e2, Submodule.mem_orthogonalBilin]
              intro w hw
              exact hdual 0 (by omega) v (fun w' hw' => by
                rw [hW0, Submodule.mem_bot] at hw'; simp [hw']) w hw
            · rw [chainFil_of_gt (by omega)]
              trivial
  exact eq_one_of_pow_three_pow_of_trivial_graded g hg (chainFil B s W) (chainFil_zero B s W)
    htriv (N := 2 * s + 1) (chainFil_of_gt (by omega))

end CFSG.HardMathSupport.Curtis.UnitaryLevi
