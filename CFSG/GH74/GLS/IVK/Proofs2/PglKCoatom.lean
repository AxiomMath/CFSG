module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem card_dvd_factorial_index_of_simple {K : Type*} [Group K] [Finite K]
    (hs : IsSimpleGroup K) {M : Subgroup K} (hM : M ≠ ⊤) :
    Nat.card K ∣ M.index.factorial := by
  have hcore : M.normalCore = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ M.normalCore_le)) hM
  have h := M.index_normalCore_dvd_factorial_index
  rwa [hcore, Subgroup.index_bot] at h

theorem isCoatom_of_card_24 {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hK : Nat.card K = 168 ∨ Nat.card K = 360) (Γ : Subgroup K) (hΓ : Nat.card ↥Γ = 24) :
    IsCoatom Γ := by
  refine ⟨?_, fun M hΓM => ?_⟩
  · rintro rfl
    rw [Subgroup.card_top] at hΓ
    omega
  · by_contra hM
    have h24 : 24 ∣ Nat.card M := hΓ ▸ Subgroup.card_dvd_of_le hΓM.le
    have hne : Nat.card M ≠ 24 := by
      intro h
      exact hΓM.ne (Subgroup.eq_of_le_of_card_ge hΓM.le (by rw [hΓ, h]))
    have hmul : M.index * Nat.card M = Nat.card K := M.index_mul_card
    have hfac := card_dvd_factorial_index_of_simple hs hM
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hidx : 1 < M.index := Subgroup.one_lt_index_of_ne_top hM
    obtain ⟨c, hc⟩ := h24
    have hc2 : 2 ≤ c := by omega
    have hnc : M.index * c * 24 = Nat.card K := by rw [← hmul, hc]; ring
    have hle : M.index * 2 ≤ M.index * c := Nat.mul_le_mul_left _ hc2
    have hn7 : M.index ≤ 7 := by
      rcases hK with hK | hK <;> omega
    generalize M.index = n at *
    interval_cases n <;> rcases hK with hK | hK <;> rw [hK] at hfac <;>
      simp [Nat.factorial] at hfac <;> omega

end CFSG.GH74.GLS.IVK.Proofs2
