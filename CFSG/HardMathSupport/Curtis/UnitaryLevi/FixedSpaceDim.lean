module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FixedSpacePieces

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem chainFil_eq_of_le {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
    (hW0 : W 0 = ⊥) {i : ℕ} (hi : i ≤ s) : chainFil B s W i = W i := by
  rcases Nat.eq_zero_or_pos i with rfl | h
  · rw [chainFil_zero, hW0]
  · exact chainFil_of_le h hi

theorem chainFil_eq_dual {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
    (hW0 : W 0 = ⊥) {a : ℕ} (ha : a ≤ s) :
    chainFil B s W (2 * s + 1 - a) = (W a).orthogonalBilin B := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · rw [Nat.sub_zero, chainFil_of_gt (by omega), hW0]
    ext v
    simp
  · rw [chainFil_of_dual (by omega) (by omega)]
    have : 2 * s + 1 - (2 * s + 1 - a) = a := by omega
    rw [this]

theorem chainFil_monotone {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} (hs : 1 ≤ s) {W : ℕ → Submodule K V}
    (hmono : ∀ j, W j ≤ W (j + 1)) (hiso : ∀ v ∈ W s, ∀ w ∈ W s, B v w = 0) : Monotone (chainFil B s W) := by
  refine monotone_nat_of_le_succ fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [chainFil_zero]
    exact bot_le
  by_cases h1 : i < s
  · rw [chainFil_of_le (by omega) (by omega), chainFil_of_le (by omega) (by omega)]
    exact hmono i
  by_cases h2 : i = s
  · subst h2
    rw [chainFil_of_le (by omega) le_rfl, chainFil_of_dual (by omega) (by omega)]
    have : 2 * i + 1 - (i + 1) = i := by omega
    rw [this]
    intro v hv
    rw [Submodule.mem_orthogonalBilin]
    exact fun w hw => hiso w hw v hv
  by_cases h3 : i < 2 * s
  · rw [chainFil_of_dual (by omega) (by omega), chainFil_of_dual (by omega) (by omega)]
    have e1 : 2 * s + 1 - (i + 1) = 2 * s - i := by omega
    have e2 : 2 * s + 1 - i = (2 * s - i) + 1 := by omega
    rw [e1, e2]
    intro v hv
    rw [Submodule.mem_orthogonalBilin] at hv ⊢
    exact fun w hw => hv w (hmono _ hw)
  · rw [chainFil_of_gt (by omega : 2 * s < i + 1)]
    exact le_top

theorem isom_orth_of_pow_three {B : V →ₛₗ[σ] V →ₗ[K] K} {g : Module.End K V}
    (hiso : ∀ v w, B (g v) (g w) = B v w) (hg3 : ∀ w, g (g (g w)) = w) {G : Submodule K V}
    (hG : ∀ u ∈ G, g u ∈ G) {v : V} (hv : ∀ u ∈ G, B u v = 0) : ∀ u ∈ G, B u (g v) = 0 := by
  intro u hu
  have h1 : B (g (g (g u))) (g v) = B (g (g u)) v := hiso _ _
  rw [hg3] at h1
  rw [h1]
  exact hv _ (hG _ (hG _ hu))

theorem apply_pow_three {x : LinearMap.GeneralLinearGroup K V} (hx : x ^ 3 = 1) (w : V) :
    (x : Module.End K V) ((x : Module.End K V) ((x : Module.End K V) w)) = w := by
  have h : ((x ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 := by
    rw [hx]; rfl
  have := congrArg (fun f : Module.End K V => f w) h
  simpa [pow_succ, Module.End.mul_apply] using this

theorem chainFil_stable {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
    (hW0 : W 0 = ⊥) {x : LinearMap.GeneralLinearGroup K V} (hx : x ^ 3 = 1)
    (hxiso : ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    (hst : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (x : Module.End K V) v ∈ W j) (i : ℕ) :
    ∀ v ∈ chainFil B s W i, (x : Module.End K V) v ∈ chainFil B s W i := by
  have hW : ∀ a, a ≤ s → ∀ v ∈ W a, (x : Module.End K V) v ∈ W a := by
    intro a ha v hv
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [hW0, Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact hst a h ha v hv
  by_cases h1 : i ≤ s
  · rw [chainFil_eq_of_le hW0 h1]
    exact hW i h1
  by_cases h2 : i ≤ 2 * s
  · rw [chainFil_of_dual (by omega) h2]
    intro v hv
    rw [Submodule.mem_orthogonalBilin] at hv ⊢
    exact isom_orth_of_pow_three hxiso (apply_pow_three hx) (hW _ (by omega)) hv
  · rw [chainFil_of_gt (by omega)]
    intro v _
    trivial

theorem chainFil_trivial_off {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} (hs : 1 ≤ s)
    {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥) {x : LinearMap.GeneralLinearGroup K V}
    (hx : x ^ 3 = 1)
    (hxiso : ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    (hst : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (x : Module.End K V) v ∈ W j) {j₀ : ℕ}
    (hP : ∀ j, 1 ≤ j → j ≤ s → j ≠ j₀ → ∀ v ∈ W j, (x : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) → (x : Module.End K V) v - v ∈ W s) (i : ℕ)
    (hi1 : i + 1 ≠ j₀) (hi2 : i + j₀ ≠ 2 * s + 1) :
    ∀ v ∈ chainFil B s W (i + 1), ((x : Module.End K V) - 1) v ∈ chainFil B s W i := by
  have hW : ∀ a, a ≤ s → ∀ v ∈ W a, (x : Module.End K V) v ∈ W a := by
    intro a ha v hv
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [hW0, Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact hst a h ha v hv
  have hdual : ∀ a, a < s → a + 1 ≠ j₀ → ∀ v, (∀ w ∈ W a, B w v = 0) →
      ∀ w ∈ W (a + 1), B w ((x : Module.End K V) v - v) = 0 := by
    intro a has hne v hv w hw
    have h1 : (x : Module.End K V) w - w ∈ W a := by
      simpa using hP (a + 1) (by omega) (by omega) hne w hw
    have h2 := isom_orth_of_pow_three hxiso (apply_pow_three hx) (hW a has.le) hv
    have h3 := hxiso w v
    rw [map_sub, ← h3]
    have e : B w ((x : Module.End K V) v) - B ((x : Module.End K V) w) ((x : Module.End K V) v) =
        - B ((x : Module.End K V) w - w) ((x : Module.End K V) v) := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    rw [e, h2 _ h1, neg_zero]
  intro v hv
  have hgm : ((x : Module.End K V) - 1) v = (x : Module.End K V) v - v := by simp
  rw [hgm]
  by_cases hi0 : i = 0
  · subst hi0
    rw [chainFil_zero]
    rw [chainFil_of_le (by omega) hs] at hv
    simpa [hW0] using hP 1 le_rfl hs (by omega) v hv
  · by_cases hi1' : i < s
    · rw [chainFil_of_le (by omega) (by omega)] at hv
      rw [chainFil_of_le (by omega) (by omega)]
      simpa using hP (i + 1) (by omega) (by omega) hi1 v hv
    · by_cases his : i = s
      · subst his
        rw [chainFil_of_le (by omega) le_rfl]
        rw [chainFil_of_dual (by omega) (by omega)] at hv
        have : 2 * i + 1 - (i + 1) = i := by omega
        rw [this, Submodule.mem_orthogonalBilin] at hv
        exact hM v fun w hw => hv w hw
      · have hi2' : s < i := by omega
        by_cases hi3 : i < 2 * s
        · rw [chainFil_of_dual hi2' (by omega)]
          rw [chainFil_of_dual (by omega) (by omega)] at hv
          have e1 : 2 * s + 1 - (i + 1) = 2 * s - i := by omega
          have e2 : 2 * s + 1 - i = (2 * s - i) + 1 := by omega
          rw [e1, Submodule.mem_orthogonalBilin] at hv
          rw [e2, Submodule.mem_orthogonalBilin]
          intro w hw
          exact hdual (2 * s - i) (by omega) (by omega) v (fun w' hw' => hv w' hw') w hw
        · by_cases hi4 : i = 2 * s
          · subst hi4
            rw [chainFil_of_dual (by omega) le_rfl]
            have e2 : 2 * s + 1 - 2 * s = 0 + 1 := by omega
            rw [e2, Submodule.mem_orthogonalBilin]
            intro w hw
            exact hdual 0 (by omega) (by omega) v (fun w' hw' => by
              rw [hW0, Submodule.mem_bot] at hw'; simp [hw']) w hw
          · rw [chainFil_of_gt (by omega)]
            trivial

variable [CharP K 2] [FiniteDimensional K V]

theorem fixed_space_dim (hσ : Function.Surjective σ) {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hB : B.SeparatingLeft) {s : ℕ} (hs : 1 ≤ s) {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥)
    (hmono : ∀ j, W j ≤ W (j + 1))
    (hWiso : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, ∀ w ∈ W j, B v w = 0)
    {x : LinearMap.GeneralLinearGroup K V} (hx : x ^ 3 = 1)
    (hxiso : ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    (hst : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (x : Module.End K V) v ∈ W j) {j₀ : ℕ}
    (hj₀ : 1 ≤ j₀) (hj₀s : j₀ ≤ s) (hdim : finrank K (W j₀) = finrank K (W (j₀ - 1)) + 2)
    (hP : ∀ j, 1 ≤ j → j ≤ s → j ≠ j₀ → ∀ v ∈ W j, (x : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) → (x : Module.End K V) v - v ∈ W s) :
    finrank K V - 4 ≤ finrank K (LinearMap.ker ((x : Module.End K V) - 1)) := by
  have key := finrank_le_finrank_ker_add_of_trivial_pieces (N := 2 * s + 1) x hx
    (chainFil B s W) (chainFil_zero B s W)
    (chainFil_monotone hs hmono (hWiso s hs le_rfl)) (chainFil_of_gt (by omega))
    (chainFil_stable hW0 hx hxiso hst) {j₀ - 1, 2 * s + 1 - j₀}
    (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact chainFil_trivial_off hs hW0 hx hxiso hst hP hM i (by omega) (by omega))
  have hne : j₀ - 1 ≠ 2 * s + 1 - j₀ := by omega
  rw [Finset.sum_pair hne] at key
  have e1 : j₀ - 1 + 1 = j₀ := by omega
  have h1 : finrank K (chainFil B s W (j₀ - 1 + 1)) - finrank K (chainFil B s W (j₀ - 1)) = 2 := by
    rw [e1, chainFil_eq_of_le hW0 hj₀s, chainFil_eq_of_le hW0 (by omega)]
    omega
  have e2 : 2 * s + 1 - j₀ + 1 = 2 * s + 1 - (j₀ - 1) := by omega
  have hd1 := finrank_orthogonalBilin_eq hσ hB (W j₀)
  have hd2 := finrank_orthogonalBilin_eq hσ hB (W (j₀ - 1))
  have hle := Submodule.finrank_le (W j₀)
  have h2 : finrank K (chainFil B s W (2 * s + 1 - j₀ + 1)) -
      finrank K (chainFil B s W (2 * s + 1 - j₀)) = 2 := by
    rw [e2, chainFil_eq_dual hW0 (by omega : j₀ - 1 ≤ s), chainFil_eq_dual hW0 hj₀s, hd1, hd2]
    omega
  omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
