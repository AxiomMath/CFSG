module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.McLRef
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.McLCover
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentThree
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin

theorem conclK_McL
    {L V MK : Subgroup (NativeSporadic.Carrier .McL)}
    (h : KConfig (NativeSporadic.Carrier .McL) L V MK) :
    ConclK (NativeSporadic.Carrier .McL) L V MK := by
  let φ : NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  haveI : Finite (NativeSporadic.Carrier .McL) := Finite.of_injective (⇑φ) φ.injective
  exact ConclK.of_map_mulEquiv φ h.elemAbelian h.le_normalizer
    (McLCls.conclK_K0 (h.map_mulEquiv φ))

theorem forK_McL :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .McL)) := by
  let φ : NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  haveI : Finite (NativeSporadic.Carrier .McL) := Finite.of_injective (⇑φ) φ.injective
  exact forK_of_kConfig_three
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_McL
    (fun _ _ _ _ _ _ hK e hZ => KConf.false_of_threeMcL hK e hZ) (fun _ _ _ h => conclK_McL h)

theorem for_McL
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .McL)) :=
  For.of_forK h37 h38 h39 forK_McL

end CFSG.SectionRank.QTK.Insp443

end
