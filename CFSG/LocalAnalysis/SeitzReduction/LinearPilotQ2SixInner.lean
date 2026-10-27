module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallestGraph
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Group

variable {G : Type*} [Group G] {L : Subgroup G} {t : G}

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self (ht2 : t * t = 1) {c : G}
    (hc : c ∈ zpowers t) : c = 1 ∨ c = t := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hc
  have ht2' : t ^ (2 : ℕ) = 1 := by rw [sq]; exact ht2
  rw [zpow_eq_zpow_emod' m ht2']
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]

theorem mem_or_mul_mem_of_commute_of_forall {H : Type*} [Group H] [Finite H] {t : H}
    (ht : t * t = 1) {D : Subgroup (H ⧸ CFSG.oddCore H)}
    (hC : ∀ h : H, h * t = t * h →
      (h : H ⧸ CFSG.oddCore H) ∈ D ∨ (h : H ⧸ CFSG.oddCore H) * (t : H ⧸ CFSG.oddCore H) ∈ D)
    {k : H ⧸ CFSG.oddCore H}
    (hkt : k * (t : H ⧸ CFSG.oddCore H) = (t : H ⧸ CFSG.oddCore H) * k) :
    k ∈ D ∨ k * (t : H ⧸ CFSG.oddCore H) ∈ D := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  have hx : x⁻¹ * t * x * t ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.eq_one_iff]
    have htt : (t : H ⧸ CFSG.oddCore H) * t = 1 := by rw [← QuotientGroup.mk_mul, ht]; rfl
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (x : H ⧸ CFSG.oddCore H)⁻¹ * t * x * t = (x : H ⧸ CFSG.oddCore H)⁻¹ * (t * x) * t := by
          group
      _ = (x : H ⧸ CFSG.oddCore H)⁻¹ * (x * t) * t := by rw [hkt]
      _ = (x : H ⧸ CFSG.oddCore H)⁻¹ * x * (t * t) := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨z, hz, hxz⟩ := exists_commute_lift_of_odd
    (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore H) ht hx
  have hmk : ((x * z : H) : H ⧸ CFSG.oddCore H) = x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]
  have h := hC (x * z) hxz
  rwa [hmk] at h

end Group

@[expose] def SporadicFixedSLFourInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], NativeSporadic.SporadicRep S →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (K : Type) [Field K], Nat.card K = 2 →
    ∀ D : Subgroup S, (∀ x ∈ D, σ x = x) → Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 4) K) →
      ∃ k : S, σ k = k ∧ k ∉ D ∧ ∀ s : S, MulAut.conj s = σ → k * s ∉ D

end CFSG.SeitzReduction.LinearPilot
