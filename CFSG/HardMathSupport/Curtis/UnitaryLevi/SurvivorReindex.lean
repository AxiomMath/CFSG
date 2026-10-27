module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorCombin
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FixedSpacePieces
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def reindexChain (a : ℕ → ℕ) (s : ℕ) (W : ℕ → Submodule K V) (k : ℕ) :
    Submodule K V :=
  open Classical in if k = 0 then ⊥ else W (a (min k s))

theorem reindexChain_zero (a : ℕ → ℕ) (s : ℕ) (W : ℕ → Submodule K V) :
    reindexChain a s W 0 = ⊥ := by simp [reindexChain]

theorem reindexChain_of_le (a : ℕ → ℕ) {s : ℕ} (W : ℕ → Submodule K V) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ s) : reindexChain a s W k = W (a k) := by
  simp [reindexChain, show k ≠ 0 by omega, min_eq_left h2]

variable {S : Finset ℕ} {a : ℕ → ℕ} {W : ℕ → Submodule K V}

theorem reindexChain_mono (ha : Enumeration S a)
    (hmono : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → W i ≤ W j) (j : ℕ) :
    reindexChain a S.card W j ≤ reindexChain a S.card W (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [reindexChain_zero]
    exact bot_le
  by_cases hjs : j < S.card
  · rw [reindexChain_of_le a W hj hjs.le, reindexChain_of_le a W (by omega) (by omega)]
    exact hmono _ (ha.mem j hj hjs.le) _ (ha.mem (j + 1) (by omega) (by omega))
      (ha.lt j hjs).le
  · have h1 : reindexChain a S.card W j = W (a S.card) := by
      simp [reindexChain, show j ≠ 0 by omega, min_eq_right (not_lt.mp hjs)]
    have h2 : reindexChain a S.card W (j + 1) = W (a S.card) := by
      simp [reindexChain, min_eq_right (show S.card ≤ j + 1 by omega)]
    rw [h1, h2]

theorem finrank_reindexChain [FiniteDimensional K V] (ha : Enumeration S a)
    (hdim : ∀ i ∈ S, finrank K (W i) = i) {k : ℕ} (hk : k ≤ S.card) :
    finrank K (reindexChain a S.card W k) = a k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [reindexChain_zero, finrank_bot, ha.zero]
  · rw [reindexChain_of_le a W hk0 hk]
    exact hdim _ (ha.mem k hk0 hk)

theorem finrank_pieceQ_reindexChain [FiniteDimensional K V] (ha : Enumeration S a)
    (hmono : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → W i ≤ W j) (hdim : ∀ i ∈ S, finrank K (W i) = i) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ S.card) :
    finrank K (PieceQ (reindexChain a S.card W (k - 1)) (reindexChain a S.card W k)) =
      a k - a (k - 1) := by
  have h := finrank_pieceQ_add (K := K)
    (reindexChain_mono ha hmono (k - 1) |>.trans_eq (by rw [Nat.sub_add_cancel hk1]) :
      reindexChain a S.card W (k - 1) ≤ reindexChain a S.card W k)
  rw [finrank_reindexChain ha hdim hk2, finrank_reindexChain ha hdim (by omega)] at h
  omega

theorem finrank_tail_reindexChain [FiniteDimensional K V] {σ : K →+* K}
    (hσ : Function.Surjective σ) {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.SeparatingLeft)
    (ha : Enumeration S a) (hS : S.Nonempty) (hdim : ∀ i ∈ S, finrank K (W i) = i)
    (hiso : ∀ i ∈ S, ∀ v ∈ W i, ∀ w ∈ W i, B v w = 0) :
    finrank K (PieceQ (reindexChain a S.card W S.card)
      ((reindexChain a S.card W S.card).orthogonalBilin B)) = finrank K V - 2 * a S.card := by
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hS
  have hle : reindexChain a S.card W S.card ≤
      (reindexChain a S.card W S.card).orthogonalBilin B := by
    rw [reindexChain_of_le a W hs le_rfl]
    intro v hv
    rw [Submodule.mem_orthogonalBilin]
    exact fun w hw => hiso _ (ha.last_mem hS) w hw v hv
  have := finrank_perpQuot_eq hσ hB _ hle
  rw [finrank_reindexChain ha hdim le_rfl] at this
  exact this

end CFSG.HardMathSupport.Curtis.UnitaryLevi
