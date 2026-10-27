module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.TwoLocalN1

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem d2L34BetaTwoLocalSylowCyclic_of_I811Cyc
    (hFF : CitedFFL34BestOffender) (h811 : AGL81I811Cyc) :
    D2L34BetaTwoLocalSylowCyclic := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax T hT N hN hTN hNM hcyc hns
  have hOnly := hAll.onlyL34At
  have hbound : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card T := by
    obtain ⟨T0, -, hT0⟩ := exists_isSylowTwoOf_of_le (bot_le : (⊥ : Subgroup G) ≤ H ⊓ M)
      IsPGroup.of_bot
    obtain ⟨hT0M, -⟩ :=
      D2L34BetaConf.isSylowTwoOf_of_cover (d2L34BetaPushUpCoverSyl hFF) hc hstr hOnly hT0
    obtain ⟨U, hT0U, hU⟩ := exists_isSylowTwoOf_of_le (hT0.1.trans inf_le_left) hT0.2.1
    obtain ⟨hUtop, hUcard⟩ := D2L34BetaConf.isSylowTwoOf_top_and_card hFF hc hstr hOnly hT0 hU hT0U
    have hTT0 : Nat.card T0 = Nat.card T := hT0M.card_eq.trans hT.card_eq.symm
    intro S hS
    obtain ⟨V, hSV, hV⟩ := exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS
    have hVU : Nat.card V = Nat.card U := hV.card_eq.trans hUtop.card_eq.symm
    calc Nat.card S ≤ Nat.card V := Subgroup.card_le_of_le hSV
      _ = Nat.card U := hVU
      _ = 8 * Nat.card T := by rw [hUcard, hTT0]
  have := hc.glob.simple
  have hNtop : N ≠ ⊤ := CFSG.RankThreeEvenClassification.Helpers.twoLocal_ne_top hc.glob.nonab N hN
  have hTNM : IsSylowTwoOf T (N ⊓ M) :=
    CFSG.QuasithinUnique.Lin2.isSylowTwoOf_of_le_of_le hT (le_inf hTN hT.1) inf_le_right
  exact h811 G hc.glob.kProper M hstr N hNtop hcyc hns T hTNM (fun S _ hS => hbound S hS)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
