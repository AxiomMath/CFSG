module

public import CFSG.ClassicalInvolution.Q3.Q3WAdjust
public import CFSG.ClassicalInvolution.WeakCT.Coherent

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {X : Type} [Group X]

theorem exists_chain3 (N : ℕ) (V : ℕ → Subgroup X) (θ₀ : ℕ → SL(3, F3) →* X)
    (h₀ : ∀ i < N, (θ₀ i).ker ≤ Subgroup.center SL(3, F3) ∧ (B12 F3).map (θ₀ i) = V i ∧
      (B23 F3).map (θ₀ i) = V (i + 1))
    (hcomm : ∀ i, i + 2 ≤ N → ∀ x ∈ V i, ∀ y ∈ V (i + 2), x * y = y * x) :
    ∃ θ : ℕ → SL(3, F3) →* X, ∀ i < N, ChainGood V θ i := by
  have key : ∀ k, k ≤ N → ∃ θ : ℕ → SL(3, F3) →* X, ∀ i < k, ChainGood V θ i := by
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
        obtain ⟨θ', h1, h2, h3, h4⟩ := exists_adjust3 hk1 a hk2 hk3 b c
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

theorem exists_ctFamily_of_pairs3 {n : ℕ} (hn : 2 ≤ n) {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F3 W (U i) (U j)) :
    ∃ F : CTFamily F3 X n, ∀ i, (F.ι i).range = U i ∧ Function.Injective (F.ι i) := by
  classical
  let V : ℕ → Subgroup X := fun i => if h : i < n then U ⟨i, h⟩ else ⊥
  have hV : ∀ (i : ℕ) (h : i < n), V i = U ⟨i, h⟩ := fun i h => dite_eq_left h
  have hpair : ∀ i : ℕ, ∃ θ₀ : SL(3, F3) →* X, i + 1 < n →
      (θ₀.ker ≤ Subgroup.center SL(3, F3) ∧ (B12 F3).map θ₀ = V i ∧
        (B23 F3).map θ₀ = V (i + 1)) := by
    intro i
    by_cases h : i + 1 < n
    · obtain ⟨W, hWpair⟩ := hpair ⟨i, by omega⟩ ⟨i + 1, h⟩ rfl
      obtain ⟨θ₀, -, h1, h2, h3⟩ := pair_normalize hWpair
      exact ⟨θ₀, fun _ => ⟨h1, by rw [hV i (by omega)]; exact h2, by rw [hV _ h]; exact h3⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose θ₀ hθ₀ using hpair
  obtain ⟨θ, hθ⟩ := exists_chain3 (n - 1) V θ₀ (fun i hi => hθ₀ i (by omega))
    (fun i hi x hx y hy => by
      rw [hV i (by omega)] at hx
      rw [hV (i + 2) (by omega)] at hy
      exact hcomm ⟨i, by omega⟩ ⟨i + 2, by omega⟩ (by simp) x hx y hy)
  let ι : Fin n → (SL(2, F3) →* X) := fun i =>
    if h : (i : ℕ) + 1 < n then (θ i).comp (blockSL F3 3 2 0 (by omega))
    else (θ ((i : ℕ) - 1)).comp (blockSL F3 3 2 1 (by omega))
  have hι_pos : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ι i = (θ i).comp (blockSL F3 3 2 0 (by omega)) := fun i h => dite_eq_left h
  have hι_neg : ∀ (i : Fin n), ¬ (i : ℕ) + 1 < n →
      ι i = (θ ((i : ℕ) - 1)).comp (blockSL F3 3 2 1 (by omega)) := fun i h => dite_eq_right h
  have hrange_inj : ∀ i : Fin n, (ι i).range = U i ∧ Function.Injective (ι i) := by
    intro i
    by_cases h : (i : ℕ) + 1 < n
    · obtain ⟨g1, g2, -, -⟩ := hθ i (by omega)
      rw [hι_pos i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B12 F3).map (θ i) = U i := by rw [g2, hV i i.2]
      exact this
    · have hi : (i : ℕ) - 1 + 1 = i := by have := i.2; omega
      obtain ⟨g1, -, g3, -⟩ := hθ ((i : ℕ) - 1) (by have := i.2; omega)
      rw [hι_neg i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B23 F3).map (θ ((i : ℕ) - 1)) = U i := by
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

end CFSG.ClassicalInvolution.Q3.Q3W
