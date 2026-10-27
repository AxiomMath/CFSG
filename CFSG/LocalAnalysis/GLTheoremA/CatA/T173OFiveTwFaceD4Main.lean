module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4X
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4X2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


theorem exists_central_witness_D4 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ z : Γ₂ F, z ≠ 1 ∧
      z ∈ Subgroup.centralizer
        (graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 : Set (Γ₂ F)) ∧
      (∀ E : Subgroup (Γ₂ F),
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → 3 ^ 4 ≤ Nat.card E → z ∈ E) ∧
      ∃ X : Subgroup (Γ₂ F), X ≤ twistedE6RootGroup F σ ∧
        X ≤ Subgroup.centralizer ({z} : Set (Γ₂ F)) ∧ ⁅X, X⁆ = X ∧
        ¬ X ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 := by
  have h3' : 3 ∣ Nat.card Fˣ := by
    have hmod : 2 ^ n % 3 = 2 := by
      have h := Nat.mod_eq_zero_of_dvd h3
      omega
    rw [Nat.card_units, hF]
    refine (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 (2 ^ n) (by positivity))).1 ?_
    change 1 % 3 = (2 ^ n) ^ 2 % 3
    rw [Nat.pow_mod, hmod]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3'
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  obtain ⟨hz1, hzT, hz3, hzC⟩ := d4Witness_facts hF σ hσ h3 hω3 hω1
  exact ⟨d4Witness ω, hz1, hzC, fun E hE hEel hE4 =>
    mem_of_le_levi_sup_diag_D4_of_card hF σ hσ h3 hzT hz3 hzC hE hEel hE4,
    exists_perfect_le_centralizer_d4Witness hF σ hσ⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
