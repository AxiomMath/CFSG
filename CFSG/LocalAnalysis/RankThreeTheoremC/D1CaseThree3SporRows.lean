module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporRank
public import CFSG.Sporadic.Bridge.Catalogue
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverWeakGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeHN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLy
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeMathieu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeTh
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding (SporadicCaseThreeData SporadicCaseThreeDataJ3
  exists_surjective_ker_eq_center j3CoverWeakGenThree primeDataToKFact
  sporadicCaseThreeDataJ3_of_coverWeakGen sporadicCaseThreeData_Co1 sporadicCaseThreeData_Co2
  sporadicCaseThreeData_Co3 sporadicCaseThreeData_He sporadicCaseThreeData_HS
  sporadicCaseThreeData_J1 sporadicCaseThreeData_J2 sporadicCaseThreeData_J4
  sporadicCaseThreeData_M11 sporadicCaseThreeData_M12 sporadicCaseThreeData_M22
  sporadicCaseThreeData_M23 sporadicCaseThreeData_M24 sporadicCaseThreeData_McL
  sporadicCaseThreeData_ON sporadicCaseThreeData_Ru sporadicCaseThreeData_Suz
  sporadicCaseThreeData_Th sporadicCaseThreeData_HN sporadicCaseThreeData_Ly)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sporCaseThreeKFactsRank3E3_of_data
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hdata : ∀ s : TauCeti.SporadicName, s ≠ .J3 →
      s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
      SporadicCaseThreeData (Carrier s))
    (hJ3 : SporadicCaseThreeDataJ3 (Carrier .J3)) : SporCaseThreeKFactsRank3E3 := by
  intro K _ _ hK s hs ⟨e⟩ p _ hp2 hZp hZc hJ _
  obtain ⟨b⟩ := hbr s
  by_cases hsJ : s = .J3
  · subst hsJ
    obtain ⟨hcard, hJdata⟩ := hJ3
    have hfin : Finite (Carrier .J3) := Nat.finite_of_card_ne_zero hcard
    obtain ⟨hprime, hcover⟩ := @hJdata hfin
    by_cases hp3 : p = 3
    · subst hp3
      have hZ : Subgroup.center K ≠ ⊥ := fun hZ => hJ ⟨rfl, rfl, hZ⟩
      obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center (e.trans b.symm)
      intro T
      exact Or.inl (hcover K π hπ hker ⟨hK.1⟩ hZ hZp hZc T)
    · exact primeDataToKFact _ p hp2 (hprime p hp2 hp3) K hK ⟨e.trans b.symm⟩ hZp hZc
  · obtain ⟨hcard, hX⟩ := hdata s hsJ hs
    have : Finite (Carrier s) := Nat.finite_of_card_ne_zero hcard
    exact primeDataToKFact _ p hp2 (hX p hp2) K hK ⟨e.trans b.symm⟩ hZp hZc

section RowCertificates


theorem sporadicCaseThreeData_of_rows3 :
    ∀ s : TauCeti.SporadicName, s ≠ .J3 →
      s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
      SporadicCaseThreeData (Carrier s) := by
  intro s h1 h2
  cases s
  case J3 => exact absurd rfl h1
  case Fi22 | Fi23 | Fi24Prime | B | M => exact absurd (by decide) h2
  case M11 => exact sporadicCaseThreeData_M11
  case M12 => exact sporadicCaseThreeData_M12
  case M22 => exact sporadicCaseThreeData_M22
  case M23 => exact sporadicCaseThreeData_M23
  case M24 => exact sporadicCaseThreeData_M24
  case J1 => exact sporadicCaseThreeData_J1
  case J2 => exact sporadicCaseThreeData_J2
  case J4 => exact sporadicCaseThreeData_J4
  case HS => exact sporadicCaseThreeData_HS
  case McL => exact sporadicCaseThreeData_McL
  case He => exact sporadicCaseThreeData_He
  case Ru => exact sporadicCaseThreeData_Ru
  case Suz => exact sporadicCaseThreeData_Suz
  case ONan => exact sporadicCaseThreeData_ON
  case Co1 => exact sporadicCaseThreeData_Co1
  case Co2 => exact sporadicCaseThreeData_Co2
  case Co3 => exact sporadicCaseThreeData_Co3
  case Th => exact sporadicCaseThreeData_Th
  case HN => exact sporadicCaseThreeData_HN
  case Ly => exact sporadicCaseThreeData_Ly

end RowCertificates

section Rows


theorem sporCaseThreeKFactsRank3E3_of_rows : SporCaseThreeKFactsRank3E3 :=
  sporCaseThreeKFactsRank3E3_of_data CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    sporadicCaseThreeData_of_rows3
    (sporadicCaseThreeDataJ3_of_coverWeakGen j3CoverWeakGenThree)

end Rows

end CFSG.LocalAnalysis.RankThreeTheoremC
