module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3ConfU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Cited

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

theorem d2L34NonExtremalL34_of_allEsc
    (h : ∀ (P : Sylow 3 G) (M : Subgroup G), Setting G → TheoremD1 G →
      rankThreeIsMaxTwoLocal M → D2FullCoreAt G M → D2ThreeClauseAt G M →
      3 ∈ rankThreeSigmaA G → IsCoreMaxLocal 3 P M → D2L34AllEscResidue3 P M) :
    D2L34NonExtremalL34 G := by
  intro d P M A H R Rbar K ctx _ _ T _ E N hesc _ Ebar K' hEbar hK'
  exact (h P M ctx.setting ctx.d1 ctx.maxLocal ctx.fullCore ctx.threeClause ctx.sigma
    ctx.core).onlyL34At3U E N E hesc Ebar K' hEbar hK'

theorem d2L34NonExtremalL34_of_residueU (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem)
    (hK4 : KFactSylowThreeAbelian) (hE9 : KFactBlockE9Transitive) (hA : D2PairA6Residue3U G) :
    D2L34NonExtremalL34 G :=
  d2L34NonExtremalL34_of_allEsc fun _ _ hS hD1 hM ha hb hp hMP =>
    d2L34AllEscResidue3_of_residueU hK hrows hT3 hM11 hM11I hO hI hNO hOut hK3 hK4 hE9 hA hS hD1
      hM ha hb hp hMP

theorem d2L34BetaMSolvableR9_of_residueU
    (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem)
    (hK4 : KFactSylowThreeAbelian) (hE9 : KFactBlockE9Transitive) (hA : D2PairA6Residue3U G) :
    D2L34BetaMSolvableR9 G :=
  d2L34BetaMSolvableR9_of_inputs hK.noXBlock3
    (d2L34NonExtremalL34_of_residueU hK hrows hT3 hM11 hM11I hO hI hNO hOut hK3 hK4 hE9 hA)

theorem d2L34BetaMSolvableR9_of_cited
    (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem)
    (hK4 : KFactSylowThreeAbelian) (hE9 : KFactBlockE9Transitive)
    (hAut : KFactStrongThreeAutomizer)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne) (hLF : LargeFieldParabolic)
    (hT : CitedBlockTransvectionPLType) (hIrr : KFactBlockOneImageIrr3) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → D2L34BetaMSolvableR9 G := by
  intro G _ _ _
  exact d2L34BetaMSolvableR9_of_residueU hK hrows hT3 hM11 hM11I hO hI hNO hOut hK3 hK4 hE9
    (d2PairA6Residue3U_of_cited hK hAut hgl hGN hCov hLF hT hIrr)

end CFSG.LocalAnalysis.RankThreeTheoremC
