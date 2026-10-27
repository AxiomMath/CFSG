module

public import CFSG.GH74.L5U5.IdentOdd
public import CFSG.ClassicalInvolution.WeakCT.Amalgam
public import CFSG.ClassicalInvolution.WeakCT.Coherent

public section

namespace CFSG.GH74.L5U5

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Adjust

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_adjust_ge_three (hK : 3 ≤ Nat.card K) {θ θ₀ : SL(3, K) →* X}
    {V₀ V₁ V₂ : Subgroup X} (hθ : θ.ker ≤ Subgroup.center SL(3, K))
    (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, K)) (h0 : (B12 K).map θ = V₀)
    (h1 : (B23 K).map θ = V₁) (h1' : (B12 K).map θ₀ = V₁) (h2 : (B23 K).map θ₀ = V₂)
    (hcomm : ∀ x ∈ V₀, ∀ y ∈ V₂, x * y = y * x) :
    ∃ θ' : SL(3, K) →* X, θ'.ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map θ' = V₁ ∧
      (B23 K).map θ' = V₂ ∧
      θ'.comp (blockSL K 3 2 0 (by omega)) = θ.comp (blockSL K 3 2 1 (by omega)) := by
  by_cases h4 : 4 ≤ Nat.card K
  · exact exists_adjust h4 hθ hθ₀ h0 h1 h1' h2 hcomm
  · have h3 : Nat.card K = 3 := by omega
    refine exists_adjust_odd ?_ hθ hθ₀ h0 h1 h1' h2 hcomm
    intro h20
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
    have h3' : p ^ (n : ℕ) = 3 := by rw [← hcard, Fintype.card_eq_nat_card, h3]
    have hp3 : p = 3 := by
      have : p ∣ 3 := by rw [← h3']; exact dvd_pow_self p n.ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
    subst hp3
    have := (CharP.cast_eq_zero_iff K 3 2).mp (by exact_mod_cast h20)
    omega

end Adjust

section Chain

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_chain_ge_three (hK : 3 ≤ Nat.card K) (N : ℕ) (V : ℕ → Subgroup X)
    (θ₀ : ℕ → SL(3, K) →* X)
    (h₀ : ∀ i < N, (θ₀ i).ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map (θ₀ i) = V i ∧
      (B23 K).map (θ₀ i) = V (i + 1))
    (hcomm : ∀ i, i + 2 ≤ N → ∀ x ∈ V i, ∀ y ∈ V (i + 2), x * y = y * x) :
    ∃ θ : ℕ → SL(3, K) →* X, ∀ i < N, ChainGood V θ i := by
  have key : ∀ k, k ≤ N → ∃ θ : ℕ → SL(3, K) →* X, ∀ i < k, ChainGood V θ i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => 1, fun i hi => absurd hi (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨θ, hθ⟩ := ih (by omega)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · obtain ⟨a, b, c⟩ := h₀ 0 (by omega)
        refine ⟨Function.update θ 0 (θ₀ 0), fun i hi => ?_⟩
        obtain rfl : i = 0 := by omega
        exact ⟨by simpa using a, by simpa using b, by simpa using c, fun j hj => by omega⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        obtain ⟨hk1, hk2, hk3, -⟩ := hθ j (by omega)
        obtain ⟨a, b, c⟩ := h₀ (j + 1) (by omega)
        obtain ⟨θ', h1, h2, h3, h4⟩ := exists_adjust_ge_three hK hk1 a hk2 hk3 b c
          (hcomm j (by omega))
        refine ⟨Function.update θ (j + 1) θ', fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (hθ i hlt).update hlt θ'
        · refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, fun j' hj' => ?_⟩
          have hjj : j' = j := by omega
          subst hjj
          simp only [Function.update_self, Function.update_of_ne (show j' ≠ j' + 1 by omega)]
          exact h4
  exact (key N le_rfl).imp fun θ hθ i hi => hθ i hi

end Chain

section Family

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_ctFamily_of_pairs_ge_three (hK : 3 ≤ Nat.card K) {n : ℕ} (hn : 2 ≤ n)
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j)) :
    ∃ F : CTFamily K X n, ∀ i, (F.ι i).range = U i ∧ Function.Injective (F.ι i) := by
  classical
  let V : ℕ → Subgroup X := fun i => if h : i < n then U ⟨i, h⟩ else ⊥
  have hV : ∀ (i : ℕ) (h : i < n), V i = U ⟨i, h⟩ := fun i h => dite_eq_left h
  have hpair : ∀ i : ℕ, ∃ θ₀ : SL(3, K) →* X, i + 1 < n →
      (θ₀.ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map θ₀ = V i ∧
        (B23 K).map θ₀ = V (i + 1)) := by
    intro i
    by_cases h : i + 1 < n
    · obtain ⟨W, hWpair⟩ := hpair ⟨i, by omega⟩ ⟨i + 1, h⟩ rfl
      obtain ⟨θ₀, -, h1, h2, h3⟩ := pair_normalize hWpair
      exact ⟨θ₀, fun _ => ⟨h1, by rw [hV i (by omega)]; exact h2, by rw [hV _ h]; exact h3⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose θ₀ hθ₀ using hpair
  obtain ⟨θ, hθ⟩ := exists_chain_ge_three hK (n - 1) V θ₀ (fun i hi => hθ₀ i (by omega))
    (fun i hi x hx y hy => by
      rw [hV i (by omega)] at hx
      rw [hV (i + 2) (by omega)] at hy
      exact hcomm ⟨i, by omega⟩ ⟨i + 2, by omega⟩ (by simp) x hx y hy)
  let ι : Fin n → (SL(2, K) →* X) := fun i =>
    if h : (i : ℕ) + 1 < n then (θ i).comp (blockSL K 3 2 0 (by omega))
    else (θ ((i : ℕ) - 1)).comp (blockSL K 3 2 1 (by omega))
  have hι_pos : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ι i = (θ i).comp (blockSL K 3 2 0 (by omega)) := fun i h => dite_eq_left h
  have hι_neg : ∀ (i : Fin n), ¬ (i : ℕ) + 1 < n →
      ι i = (θ ((i : ℕ) - 1)).comp (blockSL K 3 2 1 (by omega)) := fun i h => dite_eq_right h
  have hrange_inj : ∀ i : Fin n, (ι i).range = U i ∧ Function.Injective (ι i) := by
    intro i
    by_cases h : (i : ℕ) + 1 < n
    · obtain ⟨g1, g2, -, -⟩ := hθ i (by omega)
      rw [hι_pos i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B12 K).map (θ i) = U i := by rw [g2, hV i i.2]
      exact this
    · have hi : (i : ℕ) - 1 + 1 = i := by have := i.2; omega
      obtain ⟨g1, -, g3, -⟩ := hθ ((i : ℕ) - 1) (by have := i.2; omega)
      rw [hι_neg i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B23 K).map (θ ((i : ℕ) - 1)) = U i := by
        rw [g3, hi, hV i i.2]
      exact this
  refine ⟨{ ι := ι, θ := fun i => θ i, left := ?_, right := ?_, comm := ?_ }, hrange_inj⟩
  · intro i h
    exact (hι_pos i h).symm
  · intro i h
    by_cases h2 : (i : ℕ) + 2 < n
    · rw [hι_pos ⟨i + 1, h⟩ h2]
      exact ((hθ (i + 1) (by omega)).2.2.2 i rfl).symm
    · rw [hι_neg ⟨i + 1, h⟩ h2]
      simp
  · intro i j hij a b
    have ha : ι i a ∈ U i := (hrange_inj i).1 ▸ ⟨a, rfl⟩
    have hb : ι j b ∈ U j := (hrange_inj j).1 ▸ ⟨b, rfl⟩
    exact hcomm i j hij _ ha _ hb

end Family

section Recognition

theorem weakCT_recognition_of_pairs_ge_three (K : Type) [Field K] [Finite K] (p f : ℕ)
    (hp : p.Prime) (hK : Nat.card K = p ^ f) (hq : 3 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type}
    [Group X] {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f := by
  have hK3 : 3 ≤ Nat.card K := hK ▸ hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs_ge_three hK3 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_unit_ne_one hK3
    refine ⟨⟨0, by omega⟩, torusHom K s, fun h => hs ?_⟩
    apply torusHom_injective
    rw [map_one]
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, -, hsurj, hker, hqs, -, hmodel⟩ := exists_recognition hn hp hf hK F hgen' hnt
  exact ⟨ψ, hsurj, hker, hqs, hmodel⟩

end Recognition

end CFSG.GH74.L5U5
