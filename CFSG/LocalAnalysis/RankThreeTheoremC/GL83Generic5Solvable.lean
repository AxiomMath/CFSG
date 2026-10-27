module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericStructureParts
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5BorelSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5OddSolv2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Solvable0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem gl83GenericSolvable_of_kfacts {G : Type} [Group G] [Finite G] (hG : Gen5Global G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (Sch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hK : GL83Generic5KFacts) (hEv : KFactCoprimeAutEvenCentralizer)
    (hExcl : NoExcludedSection3 G) : GL83GenericSolvable G := by
  intro p hp P M hM hfail hIH x hgen
  have hl : Gen5Local G p P M x := ⟨hp, hM, hfail, hIH, hgen⟩
  exact gen5_isSolvable hG hl (gen5_primeCore_solvable hG hl hEv)
    (gen5_solvable_inf_normalizer hG hl) (gen5_layer_eq_bot hG K1 Sch hK hExcl hl)

end CFSG.LocalAnalysis.RankThreeTheoremC
