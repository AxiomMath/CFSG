module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetType
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetFF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem asB113Det_of
    (hbr : B113KDet.CatalogBridge)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hD : CFSG.QuasithinUnique.Bridge.AsB42DichotomyNat) :
    AsB113Det CFSG.SectionRank.IsKGroupCat := by
  unfold AsB113Det
  intro V _ _ hV G A L hGK hO2 hA hL hLA
  exact B113KDet.isLieAltType_of_ffConclusion hD hV hO2 hA hL hLA
    (B113KDet.ffConclusion_of_mulAut hbr hFF hV hGK hO2 hA hL hLA)

theorem b_1_13_of_ff
    (hbr : B113KDet.CatalogBridge)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hD : CFSG.QuasithinUnique.Bridge.AsB42DichotomyNat)
    (hLie : AsLieTwoOvergroups) (hAut : AsLieTwoSylowAut) : CFSG.ASVolI.B_1_13 :=
  b_1_13_of_lie (asB113Det_of hbr hFF hD) hLie hAut

theorem theoremC127_of_ff
    (hbr : B113KDet.CatalogBridge)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hD : CFSG.QuasithinUnique.Bridge.AsB42DichotomyNat)
    (hLie : AsLieTwoOvergroups) (hAut : AsLieTwoSylowAut) (hblock : C127KBlockType) :
    TheoremC127 :=
  theoremC127_of_lie (asB113Det_of hbr hFF hD) hLie hAut hblock

end CFSG.Quasithin
