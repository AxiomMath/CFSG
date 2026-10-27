module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenTwo
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem three_thousand_six_hundred_dvd {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P₁ P₂ : Subgroup S} (h₁ : CatLeaf.ProperFixedComponent σ P₁)
    (h₂ : CatLeaf.ProperFixedComponent σ P₂) (hne : P₁ ≠ P₂)
    (hZ₁ : Open.fusionZStar ↥P₁ = pPrimeCore 2 ↥P₁)
    (hZ₂ : Open.fusionZStar ↥P₂ = pPrimeCore 2 ↥P₂)
    (e₁ : Nonempty (↥P₁ ⧸ Open.fusionZStar ↥P₁ ≃* alternatingGroup (Fin 5)))
    (e₂ : Nonempty (↥P₂ ⧸ Open.fusionZStar ↥P₂ ≃* alternatingGroup (Fin 5))) :
    3600 ∣ Nat.card (fixedSubgroup σ) := by
  have eA : Nonempty (↥P₁ ⧸ pPrimeCore 2 ↥P₁ ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := e₁
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ₁.symm).trans e⟩
  have eB : Nonempty (↥P₂ ⧸ pPrimeCore 2 ↥P₂ ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := e₂
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ₂.symm).trans e⟩
  exact Even.dvd_card_of_two_layers h₁.2.1 h₁.2.2.1 h₂.2.1 h₂.2.2.1 hne eA eB

theorem fiveTwoLayerSpor_J1 : FiveTwoLayerSporClause .J1 := by
  intro S _ _ _ hna ⟨e⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ _
  have h := three_thousand_six_hundred_dvd h₁ h₂ hne hZ₁ hZ₂ e₁ e₂
  have hS : 3600 ∣ Nat.card S := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (NativeSporadic.Carrier .J1) = Nat.card NativeSporadic.J1 from rfl,
    Sporadic.J1.card_J1] at hS
  exact absurd hS (by decide)

theorem fiveTwoLayerSpor_M12 : FiveTwoLayerSporClause .M12 := by
  intro S _ _ _ hna ⟨e⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ _
  have h := three_thousand_six_hundred_dvd h₁ h₂ hne hZ₁ hZ₂ e₁ e₂
  have hS : 3600 ∣ Nat.card S := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
    Sporadic.Mathieu.card_M12] at hS
  exact absurd hS (by decide)

theorem fiveTwoLayerSpor_J2 :
    FiveTwoLayerSporClause .J2 := by
  intro S _ _ _ hna ⟨e⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ _
  have h := three_thousand_six_hundred_dvd h₁ h₂ hne hZ₁ hZ₂ e₁ e₂
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hσ1 := h₁.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  let eK := e.trans (ComponentClassification.J2Cover.nativeEquivP : NativeSporadic.Carrier .J2 ≃* _)
  rw [card_fixedSubgroup_congr eK σ] at h
  have hord : orderOf (MulAut.congr eK σ) = 2 := by
    rw [Sporadic.HeldB.orderOf_congr, hσ2]
  rcases GH74.GLS.IVK.Proofs2.j2_fixed_card_aut _ hord with h' | h' | h' <;> rw [h'] at h <;>
    exact absurd h (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
