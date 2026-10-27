module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.Schreier.J4SNoComp

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporOddComps_HN
    : SporOddComps .HN :=
  fun S _ _ _ _ e t ht B hB _ => by
    rw [RestrictedStd.Spor.hnLocalComponentsInput_holds S e t ht B hB]
    exact not_oddLieOrder_HS

theorem sporOddComps_Ly
    : SporOddComps .Ly :=
  fun S _ _ _ _ e t ht B hB _ => by
    obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t ht
    have hcard : Nat.card (centralizer ({t} : Set S) ⧸ center (centralizer ({t} : Set S))) =
        19958400 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    have h := RestrictedStd.Spor.compsSatisfy_of_isQuasisimple hq
      (RestrictedStd.Spor.isoInvariant_card_quotient_center {19958400}) hcard B hB
    rw [Set.mem_singleton_iff.1 h]
    exact not_oddLieOrder_A11

theorem sporOddComps_Th
    : SporOddComps .Th :=
  fun S _ _ _ _ e t ht B hB _ =>
    RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 S
        ⟨e⟩).1 t ht).1 (fun Y _ => ¬ OddLieOrder (Nat.card (Y ⧸ center Y))) B hB

theorem sporOddComps_J4
    : SporOddComps .J4 :=
  fun S _ _ _ _ e t ht B hB _ =>
    absurd hB (RestrictedStd.Spor.j4NoComponentsInput S ⟨e⟩ t ht B)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
