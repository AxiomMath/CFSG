module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.ElevenSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ElevenP

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

section Cert


theorem suborbitFacts_eleven_one_class :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ x y : H, orderOf x = 11 → orderOf y = 11 → IsConj x y := by
  intro H _ E h x y hx hy
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_p1408_of_isF5Centralizer h
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hC : ∀ t : ↥P1408, orderOf t = 11 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥P1408)) = 22 := by
    intro t ht
    obtain ⟨e⟩ := table_eleven_P hP t ht
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod]
  exact TwoHSData.isConj_of_map_mulEquiv Ψ
    (Section3Model.isConj_of_orderOf_eleven hP hC (by rw [MulEquiv.orderOf_eq, hx])
      (by rw [MulEquiv.orderOf_eq, hy]))

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
