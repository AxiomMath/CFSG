module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup

variable {K : Type*} [Field K] {n : ℕ}

theorem bot_lt_and_lt_top_of_finrank {W : Submodule K (Fin n → K)} (h1 : 1 ≤ finrank K W)
    (hn : finrank K W < n) : ⊥ < W ∧ W < ⊤ := by
  refine ⟨bot_lt_iff_ne_bot.mpr fun h => ?_, lt_top_iff_ne_top.mpr fun h => ?_⟩
  · rw [h, finrank_bot] at h1
    omega
  · rw [h, finrank_top, finrank_fin_fun] at hn
    omega

theorem index_projStabilizer [Finite K] (W : Submodule K (Fin n → K)) :
    ((projStabilizer W).index : ℚ) = gaussianCoeff n (finrank K W) (Nat.card K) :=
  (subspace_index (by simpa using Submodule.finrank_le W)).2 W rfl

theorem intrinsic_extremal_parabolics [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hn : 3 ≤ n) :
    extremalParabolics (projectiveSL n K) p =
      projStabilizer '' {L : Submodule K (Fin n → K) | finrank K L = 1} ∪
        projStabilizer '' {H : Submodule K (Fin n → K) | finrank K H = n - 1} ∧
    Disjoint (projStabilizer '' {L : Submodule K (Fin n → K) | finrank K L = 1})
      (projStabilizer '' {H : Submodule K (Fin n → K) | finrank K H = n - 1}) ∧
    (∀ M ∈ extremalParabolics (projectiveSL n K) p,
      (M.index : ℚ) = ((Nat.card K : ℚ) ^ n - 1) / ((Nat.card K : ℚ) - 1)) ∧
    (maximalParabolics (projectiveSL n K) p).Nonempty ∧
    (extremalParabolics (projectiveSL n K) p).Nonempty := by
  classical
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hM, hinj, -⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ n)
  have hL₀ : finrank K (flagSpace n K 1) = 1 := finrank_flagSpace (by omega)
  have hL₀M : projStabilizer (flagSpace n K 1) ∈ maximalParabolics (projectiveSL n K) p := by
    rw [hM]
    exact ⟨_, bot_lt_and_lt_top_of_finrank (by omega) (by omega), rfl⟩
  have hmin : ∀ M' ∈ maximalParabolics (projectiveSL n K) p,
      gaussianCoeff n 1 (Nat.card K) ≤ (M'.index : ℚ) := by
    intro M' hM'
    rw [hM] at hM'
    obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hM'
    obtain ⟨hk1, hkn⟩ := one_le_finrank_and_lt h0 htop
    rw [index_projStabilizer]
    exact (gaussian_minimum hq hn hk1 hkn).2.1
  have hext : ∀ W : Submodule K (Fin n → K), ⊥ < W → W < ⊤ →
      (projStabilizer W ∈ extremalParabolics (projectiveSL n K) p ↔
        finrank K W = 1 ∨ finrank K W = n - 1) := by
    intro W h0 htop
    obtain ⟨hk1, hkn⟩ := one_le_finrank_and_lt h0 htop
    have hmem : projStabilizer W ∈ maximalParabolics (projectiveSL n K) p := by
      rw [hM]
      exact ⟨W, ⟨h0, htop⟩, rfl⟩
    rw [mem_extremalParabolics, ← (gaussian_minimum hq hn hk1 hkn).2.2]
    constructor
    · rintro ⟨-, hle⟩
      have h2 : ((projStabilizer W).index : ℚ) ≤ ((projStabilizer (flagSpace n K 1)).index : ℚ) :=
        by exact_mod_cast hle _ hL₀M
      rw [index_projStabilizer, index_projStabilizer, hL₀] at h2
      exact le_antisymm h2 (gaussian_minimum hq hn hk1 hkn).2.1
    · intro heq
      refine ⟨hmem, fun M' hM' => ?_⟩
      have := hmin M' hM'
      rw [← heq, ← index_projStabilizer] at this
      exact_mod_cast this
  have hset : extremalParabolics (projectiveSL n K) p =
      projStabilizer '' {L : Submodule K (Fin n → K) | finrank K L = 1} ∪
        projStabilizer '' {H : Submodule K (Fin n → K) | finrank K H = n - 1} := by
    ext M
    constructor
    · intro hMe
      have hMM := hMe.1
      rw [hM] at hMM
      obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hMM
      rcases (hext W h0 htop).mp hMe with h | h
      · exact Or.inl ⟨W, h, rfl⟩
      · exact Or.inr ⟨W, h, rfl⟩
    · rintro (⟨W, hW, rfl⟩ | ⟨W, hW, rfl⟩)
      · have hW' : finrank K W = 1 := hW
        obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (K := K) (W := W) (by omega) (by omega)
        exact (hext W h0 htop).mpr (Or.inl hW')
      · have hW' : finrank K W = n - 1 := hW
        obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (K := K) (W := W) (by omega) (by omega)
        exact (hext W h0 htop).mpr (Or.inr hW')
  refine ⟨hset, ?_, fun M hMe => ?_, ⟨_, hL₀M⟩, ⟨projStabilizer (flagSpace n K 1), ?_⟩⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨L, hL, rfl⟩ ⟨H, hH, hHL⟩
    have hL' : finrank K L = 1 := hL
    have hH' : finrank K H = n - 1 := hH
    obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (K := K) (W := L) (by omega) (by omega)
    obtain ⟨h0', htop'⟩ := bot_lt_and_lt_top_of_finrank (K := K) (W := H) (by omega) (by omega)
    have := hinj ⟨h0', htop'⟩ ⟨h0, htop⟩ hHL
    rw [this] at hH'
    omega
  · have hMM := hMe.1
    rw [hM] at hMM
    obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hMM
    obtain ⟨hk1, hkn⟩ := one_le_finrank_and_lt h0 htop
    have h := (hext W h0 htop).mp hMe
    rw [index_projStabilizer, (gaussian_minimum hq hn hk1 hkn).2.2.mpr h,
      (gaussian_minimum hq hn hk1 hkn).1]
  · obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (K := K) (W := flagSpace n K 1)
      (by omega) (by omega)
    exact (hext _ h0 htop).mpr (Or.inl hL₀)

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
