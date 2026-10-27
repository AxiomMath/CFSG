module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Q8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_hq (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2) := by
  intro M hM P hP
  have hq := Sec6Gen.isQuatSub_of_mem_RSet hyp.std.1.stand.hyp (mem_RSet_of_isSylow2In hM hP)
  obtain ⟨k, hk, ⟨e⟩⟩ := hq
  have h8 : Nat.card ↥P = 8 := hyp.std.1.stand.card8 M hM P hP
  have hcard : Nat.card ↥P = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hk1 : 2 ^ k = 2 := by omega
  have hk' : k = 1 := by
    have : 2 ^ k = 2 ^ 1 := by simpa using hk1
    exact Nat.pow_right_injective (le_refl 2) this
  subst hk'
  exact ⟨e⟩

theorem layer_q8Section (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) :
    Q8Section (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) (secFam Ω a) :=
  q8Section_secFam hyp.std.1.stand.hyp
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2)
    hyp.std.1.quot2 (layer_hq hyp) hyp.std.1.stand.aEmpty

end Q8

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
