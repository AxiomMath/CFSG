module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4M1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4Perf

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem gnImg_thompsonJ_le_sup_centralizer_of_B2_cert113
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤) (d : TauCeti.ValidLieTypeIndex)
    (Q : TauCeti.PrimePower) (hd : d.1 = .B 2 Q) (hQ : Q.p = 2)
    (hLd : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
  gnImg_thompsonJ_le_sup_centralizer_of_B2 k54NatQuotSp4_proof k54PerfStabSp4_proof hX hL d Q hd hQ
    hLd

end CFSG.LocalAnalysis.RankThreeUC.S15

end
