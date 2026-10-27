module

public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
public import CFSG.LocalAnalysis.OddStandard.Glue
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndPerm
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.OddStandard.ChildHe

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Blueprint

theorem smallAltFive_of_unbalanced
    (hU : KProperSimpleUnbalancedUOutcome)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin 5))
    (hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    AltOutcome G ∨ OddLieType G := by
  have := hS.simple
  have hUO := hU G hS.nonab hS.kProper hz
  have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
    ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
  let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
    ComponentClassification.GSLit.generalizedFittingEquivOfSimple
  rcases hUO with hlie | ⟨n, hodd, h7, ⟨θ'⟩, hlt⟩ | ⟨-, hlt⟩
  · exact Or.inr ((CFSG.ClassicalInvolution.oddLieType_congr e).1 hlie)
  · have hn4 : n % 4 ≠ 1 := fun h => (hlt h).ne htop
    by_cases h9 : 9 ≤ n
    · exact Or.inl ⟨n, h9, ⟨e.symm.trans θ'⟩⟩
    · exfalso
      obtain ⟨m, hm⟩ := hodd
      obtain rfl : n = 7 := by omega
      obtain ⟨t, htC, ht⟩ := exists_involution_of_standard hS.standard
      have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
      have h1 : Nat.card L ≤ Nat.card (centralizer ({t} : Set G)) := Subgroup.card_le_of_le hLt
      have h2 := card_centralizer_dvd_forty_eight_of_alternating_seven (e.symm.trans θ') ht
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 := sixty_le_card_of_quotient_alternating (le_refl 5) θ
      omega
  · exact absurd htop hlt.ne

end CFSG.OddStandard
