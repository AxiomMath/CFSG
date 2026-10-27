module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4CMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223Steps
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

theorem reduction15223P4_of_F4
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hcover : AsA36NoOddCover) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (kR : Input21Rank) (kL : ThreeRankBlocks) (kP : Input21ProperRank)
    (kB : SolvOvergroupsInBorel) (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4)
    (h1521 : StageLemma15221W_F4) (h22 : StageLemma15222Canon_F4) : Reduction15223P4_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar hno hnotMc hii
  obtain ⟨X, c⟩ := S15223P4.p4Ctx_exists_F4 hC129 h37 h38 hC27 h5 h159 h8 h11 h13 h14 hN h16 h17 h18
    hs hH hB₀ hI hchar hno hii
  have hθ : ThetaEqComponent := thetaEqComponent_of_a318 hF318 h36 h38 hK
  have h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I := fun H₁ H₂ hP =>
    h1521 G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI.1
  by_cases hg : SBc17.C27SL3 I (S15223P4.P4R M I) (M ⊓ I) X (S15223P4.P4V M I X)
  · obtain ⟨⟨n, F, hFf, hFfin, hn, hFn, e⟩, hpar, hMS⟩ := id hg
    by_cases hn1 : n = 1
    · subst hn1
      have hF2 : Fintype.card F = 2 := by simpa using hFn
      have hnot : ¬ X ≤ Mc := hnotMc X (S15223P4.P4R M I) c.comp c.charTwoX c.quasi c.not_le
        c.K_norm c.R_le_S c.R_norm c.c27 hg ⟨F, hFf, hFfin, hF2, e⟩
      exact S15223P4.D1.false_of_caseG_one_F4 hcover h37 h38 h12 h21 h22 c hF2 e hpar hnot
    · exact S15223P4.G.false_of_caseG_gt_one hcover c n F
        (Nat.lt_of_le_of_ne hn (Ne.symm hn1)) hFn e hpar hMS
  · have hLn := S15223P4.B.lnQuot_of_not_caseG hθ hcover kR kL kP kB c hg
    exact S15223P4.C.false_of_lnQuot_F4 hF318 h36 h38 hK h51 hI16 hA8 h12 h1521 c hLn

end S15223

end CFSG.Quasithin
