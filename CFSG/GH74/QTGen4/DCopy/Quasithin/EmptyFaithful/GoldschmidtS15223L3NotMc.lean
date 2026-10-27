module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3NotMc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P2Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P2Pieces

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace S15223

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem reduction15223P2NotMc_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4)
    (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4)
    (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4)
    (hOrb : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], A3Orbits G) : Reduction15223P2NotMc_F4 := by
  intro hP1 G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar hno X R hX hcharX hq hXM hKX hRS hRX hC27
    hC27g hF
  have hctx := ctx15223_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hs hH hB₀ hI
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hF
  have hperf : ⁅X, X⁆ = X := perfect_of_mem_cComp hX
  have hne : ⁅omegaOneCenterOf (pCoreOf 2 (X ⊔ R)), X⁆ ≠ ⊥ :=
    S151TC.commutator_ne_bot_of_caseG (K := X) (R := R) (M := M ⊓ I) hC27g
  obtain ⟨-, hgen, hns, hV2⟩ := l3_facts hperf hq hRX hC27g.2.2 hne hFc e
  have hSMc : sOf152 T Mc M B₀ ≤ Mc := fun s hs' =>
    hctx.mc_of_cent s fun z hz => ((hctx.zS_mem z hz).2.2 s hs').symm
  exact not_le_of_perfect (hOrb G) hctx.sqtk hctx.sylow hX hSMc
    (fun Y h1 h2 h3 h4 h5' => hP1 G T Mc M hs H hH B₀ hB₀ I hI.1 Y h1 h2 h3 h4 h5')
    hctx.K_solvable hgen hns hV2

end S15223

end CFSG.Quasithin
