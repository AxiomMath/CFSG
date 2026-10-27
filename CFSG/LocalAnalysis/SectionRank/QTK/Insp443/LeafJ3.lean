module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.J3Ref
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.J3Cover
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentThree
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverCert

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin

theorem conclK_J3
    {L V MK : Subgroup (NativeSporadic.Carrier .J3)}
    (h : KConfig (NativeSporadic.Carrier .J3) L V MK) :
    ConclK (NativeSporadic.Carrier .J3) L V MK := by
  let φ : NativeSporadic.Carrier .J3 ≃* CFSG.Sporadic.Schreier.j3P :=
    CFSG.Sporadic.Schreier.j3PermEquiv
  haveI : Finite (NativeSporadic.Carrier .J3) := Finite.of_injective (⇑φ) φ.injective
  exact ConclK.of_map_mulEquiv φ h.elemAbelian h.le_normalizer
    (J3Cls.conclK_K0 (h.map_mulEquiv φ))

theorem forK_J3 :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J3)) := by
  let φ : NativeSporadic.Carrier .J3 ≃* CFSG.Sporadic.Schreier.j3P :=
    CFSG.Sporadic.Schreier.j3PermEquiv
  haveI : Finite (NativeSporadic.Carrier .J3) := Finite.of_injective (⇑φ) φ.injective
  exact forK_of_kConfig_three
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover.nativeRow_J3
    (fun _ _ _ _ _ _ hK e hZ => KConf.false_of_threeJ3 hK e hZ) (fun _ _ _ h => conclK_J3 h)

theorem for_J3
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J3)) :=
  For.of_forK h37 h38 h39 forK_J3

end CFSG.SectionRank.QTK.Insp443

end
