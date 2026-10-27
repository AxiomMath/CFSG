module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open
  CFSG.HardMathSupport.Foote.ModuleExclusions

variable {F : Type} [Field F] [Finite F]

theorem mem_zpowers_of_pow_three_eq_one (σ τ : F ≃+* F) (hσ : orderOf σ = 3) (hτ : τ ^ 3 = 1) :
    τ ∈ Subgroup.zpowers σ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcyc : IsCyclic (RingAut F) :=
    (card_ringAut_and_isCyclic hp F (by rw [Nat.card_eq_fintype_card]; exact hn)).2
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hτ) with h | h
  · rw [orderOf_eq_one_iff.1 h]; exact Subgroup.one_mem _
  · have : Subgroup.zpowers τ = Subgroup.zpowers σ :=
      (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, h, hσ])
    rw [← this]; exact Subgroup.mem_zpowers τ

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
