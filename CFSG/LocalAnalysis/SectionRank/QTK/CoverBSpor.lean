module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBBasic
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBON
import CFSG.RankThree.PartOne.KP.BExclusion
import CFSG.RankThree.PartOne.KP.MSectionMonster
import CFSG.RankThree.ThetaFree.Sporadic
import CFSG.RankThree.PartOne.S11c.Co1Cover
import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverResidual
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Assembly.RankThreeEven (localRank)

theorem mem_qtkSporadicNames_of_cover
    {G : Type} [Group G] [Finite G]
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} (hq : CFSG.IsQuasisimple ↥Y)
    {s : TauCeti.SporadicName} (e : ↥Y ⧸ center ↥Y ≃* CFSG.Blueprint.NativeSporadic.Carrier s) :
    s ∈ qtkSporadicNames := by
  have hE4 : 4 ≤ CFSG.Assembly.evenRank G → False := fun h => by
    have h' : CFSG.Open.evenRank G = CFSG.Assembly.evenRank G := rfl
    omega
  have hY4 : 4 ≤ CFSG.twoLocalOddRank ↥Y → False := fun h => by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank] at h
    exact hE4 (h.trans (CFSG.RankThree.PartTwo.evenRank_subgroup_le Y))
  have hfin : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  cases s with
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J3 | J4 | HS | He | Ru | McL =>
    simp [qtkSporadicNames]
  | Fi22 => exact (hE4 (CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22 G Y (center ↥Y)
      ⟨e⟩)).elim
  | Fi23 => exact (hE4 (CFSG.RankThree.ThetaFree.sectionsForceEvenRankFour_fi23_fi24prime'.1 G Y
      (center ↥Y) ⟨e⟩)).elim
  | Fi24Prime => exact (hE4 (CFSG.RankThree.ThetaFree.sectionsForceEvenRankFour_fi23_fi24prime'.2
      G Y (center ↥Y) ⟨e⟩)).elim
  | B => exact (hE4 (CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B G Y (center ↥Y) ⟨e⟩)).elim
  | M =>
    have : IsSimpleGroup (↥Y ⧸ center ↥Y) := hq.2.1
    exact (hE4 (CFSG.RankThree.PartOne.simplePresentationM_sections_of_B_section
      CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B
      CFSG.RankThree.PartOne.simplePresentationMHasBSection_holds G Y (center ↥Y)
      (↥Y ⧸ center ↥Y) hq.2.2 ⟨MulEquiv.refl _⟩ ⟨e⟩)).elim
  | Co1 =>
    have h := CFSG.RankThree.PartOne.co1ActualArbitraryCentralCoversForceTwoLocalRankFour G Y
      (↥Y ⧸ center ↥Y) (QuotientGroup.mk' (center ↥Y)) (QuotientGroup.mk'_surjective _) ⟨e⟩
      (QuotientGroup.ker_mk' _).le
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank] at h
    exact (hE4 h).elim
  | Co2 =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Co2 := e
    have : Finite NativeSporadic.Co2 := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSporadicResidual.co2 ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.Co2 Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeCo2
  | Co3 =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Co3 := e
    have : Finite NativeSporadic.Co3 := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSporadicResidual.co3 ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.Co3 Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeCo3
  | Ly =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Ly := e
    have : Finite NativeSporadic.Ly := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSporadicResidual.ly ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.Ly Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeLy
  | HN =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.HN := e
    have : Finite NativeSporadic.HN := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSporadicResidual.hn ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.HN Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeHN
  | Th =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Th := e
    have : Finite NativeSporadic.Th := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSporadicResidual.th ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.Th Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeTh
  | Suz =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Suz := e
    have : Finite NativeSporadic.Suz := Finite.of_equiv _ e'.toEquiv
    by_cases h3 : 3 ∣ Nat.card (center ↥Y)
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
      exact hY4 (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverSuzRankFour ↥Y
        ⟨hq, h3, ⟨e'.trans b⟩⟩)
    · exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.Suz Units.instGroup _ e' 3
        Nat.prime_three (by norm_num) h3 CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeSuz
  | ONan =>
    exfalso
    let e' : ↥Y ⧸ center ↥Y ≃* NativeSporadic.ON := e
    have : Finite NativeSporadic.ON := Finite.of_equiv _ e'.toEquiv
    exact @false_of_three_le_localRank G _ _ he Y NativeSporadic.ON Units.instGroup _ e' 3
      Nat.prime_three (by norm_num) (not_three_dvd_card_center_of_ON he e')
      CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeON

end CFSG.SectionRank.QTK.CoverB
