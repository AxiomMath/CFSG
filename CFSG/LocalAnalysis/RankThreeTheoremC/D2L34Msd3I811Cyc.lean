module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Leaves15
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TwoLocalI811
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3LayerCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNCore
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.AltOddCentre
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OddCentreE9
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactE9U33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylowFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3AutImage
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3InvTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Leaves14

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.McLaughlin
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaTwoLocalSylowCyclic3_of_I811Cyc
    (hFF : CitedFFL34BestOffender) (h811 : AGL81I811Cyc) :
    D2L34BetaTwoLocalSylowCyclic3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax T hT N hN hTN hNM hcyc hns
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOnly := ctx.allResidue.onlyL34At
  have hbound : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card T := by
    obtain ⟨T0, -, hT0⟩ := exists_isSylowTwoOf_of_le (bot_le : (⊥ : Subgroup G) ≤ H ⊓ M)
      IsPGroup.of_bot
    obtain ⟨hT0M, -⟩ := D2L34BetaConf3.isSylowTwoOf_of_cover hFF hc hstr hOnly hT0
    obtain ⟨U, hT0U, hU⟩ := exists_isSylowTwoOf_of_le (hT0.1.trans inf_le_left) hT0.2.1
    obtain ⟨hUtop, hUcard⟩ :=
      D2L34BetaConf3.isSylowTwoOf_top_and_card hFF hc hstr hOnly hT0 hU hT0U
    have hTT0 : Nat.card T0 = Nat.card T := hT0M.card_eq.trans hT.card_eq.symm
    intro S hS
    obtain ⟨V, hSV, hV⟩ := exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS
    have hVU : Nat.card V = Nat.card U := hV.card_eq.trans hUtop.card_eq.symm
    calc Nat.card S ≤ Nat.card V := Subgroup.card_le_of_le hSV
      _ = Nat.card U := hVU
      _ = 8 * Nat.card T := by rw [hUcard, hTT0]
  have := (D2Amb3.glob (G := G)).simple
  have hNtop : N ≠ ⊤ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocal_ne_top (D2Amb3.glob (G := G)).nonab N hN
  have hTNM : IsSylowTwoOf T (N ⊓ M) :=
    CFSG.QuasithinUnique.Lin2.isSylowTwoOf_of_le_of_le hT (le_inf hTN hT.1) inf_le_right
  exact h811 G (D2Amb3.glob (G := G)).kProper M hstr N hNtop hcyc hns T hTNM
    (fun S _ hS => hbound S hS)

theorem d2L34BetaMSideNonConstrainedInput3_of_frontier_cyc
    
    (hcore : AGL81II1320Core) (hI811 : AGL81I811Cyc) (hFF : CitedFFL34BestOffender)
    (hSch : KFactCatalogSchreier) (hX : D1NoXBlock3 G) :
    D2L34BetaMSideNonConstrainedInput3 G :=
  have hN : D2L34BetaNormalizerSolvable3 G :=
    d2L34BetaNormalizerSolvable3_of_cyclic hSch hFF
      (d2L34BetaTwoLocalSylowCyclic3_of_I811Cyc hFF hI811)
  d2L34BetaMSideNonConstrainedInput3_of_layer hFF kFactRankTwoE9 kFactRankTwoSylowPermute
    (d2L34BetaLayerExists3_of_core hcore hFF hN hX)
    (d2L34BetaLayerSylow3_of d2L34BetaInvariantTwoInCore3_proved
      (d2L34BetaLayerCentralized3_of hFF kFactRankTwoE9) invariantSylowStmt)
    (d2L34BetaLayerAutImage3_proved hN hX)

theorem D2Leaves3SX.toLeaves3SW_of_cited_cyc
    
    (hK : D2KFactLeaves) (hGN : GlaubermanNilesInput) (hFFT : FFModuleTheorem)
    (hGF : GF2EightFive) (hRT : KFactParabolicCoverRankTwo) (hI811 : AGL81I811Cyc)
    (hFF : CitedFFL34BestOffender) (h : D2Leaves3SX G) : D2Leaves3SW G :=
  ⟨h.l34MSolvable, d2L34BetaMSideNonConstrainedInput3_of_frontier_cyc
    (agl81II1320Core_of_gn' hGN hFFT (agl81I56_of_gf2EightFive' hGF) hRT kFactOddCentreE9) hI811
    hFF hK.catalogSchreier hK.noXBlock3⟩

theorem D2Leaves3SX.toLeaves3S_of_cited_cyc
    
    (hK : D2KFactLeaves) (hAut : KFactStrongThreeAutomizer)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne) (hLF : LargeFieldParabolic)
    (hT : CitedBlockTransvectionPLType) (hIrr : KFactBlockOneImageIrr3)
    (hFFT : FFModuleTheorem) (hGF : GF2EightFive) (hRT : KFactParabolicCoverRankTwo)
    (hI811 : AGL81I811Cyc) (hFF : CitedFFL34BestOffender) (h : D2Leaves3SX G) : D2Leaves3S G :=
  (h.toLeaves3SW_of_cited_cyc hK hGN hFFT hGF hRT hI811 hFF).toLeaves3S_of_cited hK hAut hgl hGN
    hCov hLF hT hIrr

end CFSG.LocalAnalysis.RankThreeTheoremC
