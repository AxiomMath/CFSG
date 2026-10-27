module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O82
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneK
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneL

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem row1520One_of_ctxGen
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK7145 : K7145) (hKOut : KOut)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMAlt : KSMAlt)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (h12 : Row1512 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h19 : Row1519 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) : Row1520One G M T T₁ T₂ := by
  intro p hp hp5 Ls L hLs hL
  by_cases hLn : L.Normal
  · have hpp : p.Prime := sigmaA_prime p hp.1
    obtain ⟨hlist, hU5⟩ := h12 Ls L hLs hL
    have hU5' : IsUFiveFour ↥Ls → p ≠ 5 := fun h hp5' => hU5 h (hp5' ▸ hp)
    have hZ := not_dvd_centre_barO2_of_row1512 hKSMOdd hKSMU4 hKSML3 hKSMAlt ctx.gn hLs.1 hL hpp
      hp5 hlist hU5'
    have hXK : CFSG.Open.IsKGroup ↥M := ctx.cstar.kProper.isKGroup M (ctx.strong p hp).1
    have hno : ∀ N : Subgroup ↥M, N.Normal → N.index ≠ p := fun N hN => by
      haveI := hN
      exact no_normal_index_p_of_ctx_gen ctx hp N
    have hrk := two_le_pRank_cMBar_gen hK7145 hKOut hXK hpp hp5 hL.1 (ctx.three_le p hp)
      (h19 p hp Ls L hLs hL) hZ hno (h15 Ls L hLs hL _ rfl)
    exact exists_pComponent_of_normal hSz ctx h19 hLifts hp hp5 hrk
  · exact row1520One_of_not_normal ctx hLifts h19 hp hL.1 hLn

theorem row1520One_of_ctx2
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK7145 : K7145) (hKOut : KOut)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMAlt : KSMAlt)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (h12 : Row1512 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h19 : Row1519 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) : Row1520One G M T T₁ T₂ :=
  row1520One_of_ctxGen hSz hK7145 hKOut hKSMOdd hKSMU4 hKSML3 hKSMAlt (S15CtxGen.of_ctx2 ctx) h12
    h15 h19 hLifts

end CFSG.LocalAnalysis.RankThreeUC.S15
