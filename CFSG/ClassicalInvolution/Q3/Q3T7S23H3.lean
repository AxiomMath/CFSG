module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic

theorem not_three_dvd_card_center_of_oddCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hY : classicalInvolutionOddCore Y = ⊥) : ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Y)) 3 h3
  have hgY : (g : Y) ∈ Subgroup.center Y := g.2
  have hg3 : orderOf (g : Y) = 3 := by rw [← hg]; exact Subgroup.orderOf_coe g
  have hN : (Subgroup.zpowers (g : Y)).Normal := ⟨fun n hn x => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute x (g : Y) := Subgroup.mem_center_iff.mp hgY x
    rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers (g : Y))) := by
    rw [Nat.card_zpowers, hg3]
    decide
  have hle : Subgroup.zpowers (g : Y) ≤ classicalInvolutionOddCore Y := le_sSup ⟨hN, hodd⟩
  rw [hY, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hg3
  omega

variable {G : Type} [Group G] [Finite G]

theorem phanH3_23 {E U₀ U₁ U₁' : Subgroup G} (hle : U₀ ⊔ U₁ ⊔ U₁' ≤ E)
    (hgen : E ≤ (U₀ ⊔ U₁ ⊔ U₁') ⊔ oddCoreOf E)
    (hO : classicalInvolutionOddCore ↥E = ⊥) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(U₀ ⊔ U₁ ⊔ U₁')) := by
  have hbot : oddCoreOf E = ⊥ := by
    rw [oddCoreOf, hO, Subgroup.map_bot]
  rw [hbot, sup_bot_eq] at hgen
  have heq : U₀ ⊔ U₁ ⊔ U₁' = E := le_antisymm hle hgen
  rw [heq]
  exact not_three_dvd_card_center_of_oddCore_eq_bot hO

theorem phanH3_clause {E K J₁ J₁' U₂ : Subgroup G} {w : G} (hw : w ∈ U₂)
    (hconj : conjSub w J₁ = J₁') (hcomm : Commutes J₁ J₁') (hKE : K ≤ E) (hJ₁E : J₁ ≤ E)
    (hJ₁'E : J₁' ≤ E) (hgen : E ≤ (K ⊔ J₁ ⊔ J₁') ⊔ oddCoreOf E)
    (hO : classicalInvolutionOddCore ↥E = ⊥) :
    ∃ w ∈ U₂, Commutes J₁ (conjSub w J₁) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center ↥(K ⊔ J₁ ⊔ conjSub w J₁)) :=
  ⟨w, hw, hconj ▸ hcomm, by
    rw [hconj]
    exact phanH3_23 (sup_le (sup_le hKE hJ₁E) hJ₁'E) hgen hO⟩

end CFSG.ClassicalInvolution.Q3.Q3T7S23
