module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem spTwoAToralAt_of_two_le {N j : ℕ} (hj : 2 ≤ j) (hjN : 2 * j < N) : SpTwoAToralAt N j := by
  intro K _ _ _ hK hN H _ Φ₁ Φ₂ hΦ₁ hΦ₂ _ hodd₁ _
  set X : Subgroup (StatedSp N K) := nsTorusSp K (⟨N - 1, by omega⟩ : Fin N) with hX
  have hXC : X ≤ centralizer ({spARep N j} : Set (StatedSp N K)) :=
    nsTorusSp_le_centralizer_spARep (by simp only; omega)
  have hXodd : ∀ ξ ∈ X, Odd (orderOf ξ) := by
    intro ξ hξ
    have h1 : orderOf (⟨ξ, hξ⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hX, card_nsTorusSp] at h1
    exact Odd.of_dvd_nat (by decide) h1
  have hXrange : X.map Φ₁ ≤ Φ₂.range := by
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨y, -, hy⟩ := hodd₁ ξ (hXC hξ) (hXodd ξ hξ)
    exact ⟨y, hy⟩
  set S : Subgroup (StatedSp N K) := (X.map Φ₁).comap Φ₂ with hS
  have hSC : S ≤ centralizer ({spARep N j} : Set (StatedSp N K)) := by
    intro y hy
    obtain ⟨ξ, hξ, hξy⟩ := (hy : Φ₂ y ∈ X.map Φ₁)
    obtain ⟨y', hy', hy'eq⟩ := hodd₁ ξ (hXC hξ) (hXodd ξ hξ)
    have : y' = y := hΦ₂ (hy'eq.trans hξy)
    rw [← this]
    exact hy'
  have hScard : Nat.card S = 3 := by
    have hmap : S.map Φ₂ = X.map Φ₁ := by
      rw [hS, Subgroup.map_comap_eq, inf_eq_right.2 hXrange]
    have h3 : Nat.card (S.map Φ₂) = Nat.card S := Subgroup.card_map_of_injective hΦ₂
    rw [hmap, Subgroup.card_map_of_injective hΦ₁, hX, card_nsTorusSp] at h3
    exact h3.symm
  exact spATwoTorusInput_holds N j K hK hj hjN.le S hSC hScard

theorem spTwoAToralAt_holds_of_four_le :
    ∀ N j : ℕ, 4 ≤ N → 1 ≤ j → 2 * j < N → SpTwoAToralAt N j := by
  intro N j hN hj hjN
  rcases eq_or_lt_of_le hj with rfl | hj2
  · exact spTwoAToralAt_one_of_four_le hN
  · exact spTwoAToralAt_of_two_le hj2 hjN

end CFSG.SeitzReduction.SymplecticPilot
