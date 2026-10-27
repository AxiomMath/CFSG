module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericUniquePlaneRank2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9B
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Cover
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9L2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Struct2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Struct3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem genericUniquePlaneRank2_of_k49 (hG : Gen5Global G) (hStr : GL83GenericStructure G)
    (KL : KFactL2UnipotentCoprime) (hK : GL83Generic5KFacts) :
    GL83GenericUniquePlaneRank2 G := by
  intro p hp P M hM hfail hIH x hgen R hRP hRe hRc hxR H hH hRH _
  have hl : Gen5Local G p P M x := ⟨hp, hM, hfail, hIH, hgen⟩
  have hp5 := gen5_five_le hG hl
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨Y, hY1, hY2, rfl⟩ := hH
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hG.setting hp hM
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  exact gen49_endgame (p := p) (by omega) (gen49_isPGroup_T hl) (gen49_normalizer_T hl)
    (hRP.trans hPM) hRe hRc hxR hx1 (gen49_fpf hG hStr hl)
    (fun Y' h2 hYM hRY y hy => gen49_comm hG hStr hl Y' h2 hYM (hRY hxR) y hy)
    (fun F hF hRF => gen49_invariant_le hG hl KL hRP hRe hRc hxR hF hRF)
    (gen49_rank3 hG hl hRP hRe hRc hxR) (gen49_proper hG)
    (gen49_cover hG hl gl83Generic4_9B_holds hK.innerAction hK.weakClosure hRP hRe hRc hxR)
    Y hY1 hY2 hRH

theorem genericUniquePlaneRank2_of_k5facts (hG : Gen5Global G) (hStr : GL83GenericStructure G)
    (hK : GL83Generic5KFacts) : GL83GenericUniquePlaneRank2 G :=
  genericUniquePlaneRank2_of_k49 hG hStr kFactL2UnipotentCoprime hK

end CFSG.LocalAnalysis.RankThreeTheoremC
