module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ElevenP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog Subgroup

section Cert

theorem pA_mem_center' : pA ∈ center ↥P1408 := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (elemA_comm g.2).symm

theorem natCard_centralizer_pA :
    Nat.card ↥(centralizer ({pA} : Set ↥P1408)) = Nat.card ↥P1408 := by
  have h : centralizer ({pA} : Set ↥P1408) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by
      rintro _ rfl
      exact pA_mem_center')
  rw [h, Subgroup.card_top]

theorem natCard_centralizer_pZ (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(centralizer ({pZ} : Set ↥P1408)) = 30720 :=
  card_centralizer_of_classSpec (t := pZ) rfl (invClasses_classSpec hP).1

theorem natCard_centralizer_pAZ (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(centralizer ({pA * pZ} : Set ↥P1408)) = 30720 :=
  card_centralizer_of_classSpec (t := pA * pZ) rfl (invClasses_classSpec hP).2.1

theorem natCard_centralizer_pB (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(centralizer ({pB} : Set ↥P1408)) = 80640 :=
  card_centralizer_of_classSpec (t := pB) rfl (invClasses_classSpec hP).2.2.1

theorem natCard_centralizer_pZ₁ (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(centralizer ({pZ₁} : Set ↥P1408)) = 3840 :=
  card_centralizer_of_classSpec (t := pZ₁) rfl (invClasses_classSpec hP).2.2.2

theorem isConj_pB_of_natCard (hP : Nat.card ↥P1408 = 177408000) {e : ↥P1408}
    (he : orderOf e = 2) (hc : Nat.card ↥(centralizer ({e} : Set ↥P1408)) = 80640) :
    IsConj pB e := by
  obtain ⟨i, hi⟩ := involution_cover_inv hP e he
  fin_cases i
  · change IsConj pA e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pA, hP] at hc
    omega
  · change IsConj pZ e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pZ hP] at hc
    omega
  · change IsConj (pA * pZ) e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pAZ hP] at hc
    omega
  · exact hi
  · change IsConj pZ₁ e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pZ₁ hP] at hc
    omega

theorem isConj_pZ₁_of_natCard (hP : Nat.card ↥P1408 = 177408000) {e : ↥P1408}
    (he : orderOf e = 2) (hc : Nat.card ↥(centralizer ({e} : Set ↥P1408)) = 3840) :
    IsConj pZ₁ e := by
  obtain ⟨i, hi⟩ := involution_cover_inv hP e he
  fin_cases i
  · change IsConj pA e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pA, hP] at hc
    omega
  · change IsConj pZ e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pZ hP] at hc
    omega
  · change IsConj (pA * pZ) e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pAZ hP] at hc
    omega
  · change IsConj pB e at hi
    rw [card_centralizer_eq_of_isConj hi, natCard_centralizer_pB hP] at hc
    omega
  · exact hi

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
