module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401OmegaSix
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

theorem glbCore_three_of_catGroup
    {L : Type} [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex)
    (hch : 3 ≠ d.1.characteristic) (hLin : ¬ CFSG.AGLEmbedding.IsLinThreeFourIndex d)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) (T : Sylow 3 L) :
    CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  have hs : IsSimpleGroup L := e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
  exact CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwoInnerEx_holds L hs
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.exists_not_comm_of_two_le_pRank hs
      Nat.prime_three h3)
    d ⟨e⟩ 3 Nat.prime_three (by norm_num) hch T
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.not_isCyclic_of_two_le_pRank h3 T)
    (fun h => hLin h.2) (fun h => absurd h.1 (by norm_num))

theorem glbCore_three_omega_plus
    {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L] [Finite L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo true n L) (T : Sylow 3 L) :
    CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  obtain ⟨eP⟩ := nonempty_statedProj_of_isOmegaTwo_true h
  obtain ⟨eD⟩ := nonempty_D_of_isOmegaTwo_true hn h
  exact glbCore_three_of_catGroup ⟨.D n twoPP, valid_D_of_four_le hn twoPP⟩
    (by simp [TauCeti.LieTypeIndex.characteristic_D, twoPP])
    (by rintro ⟨q, -, -, hq⟩; simp at hq) eD (two_le_pRank_three_of_plus hn eP) T

theorem glbCore_three_omega_minus
    {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L] [Finite L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo false n L) (T : Sylow 3 L) :
    CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  obtain ⟨eP⟩ := nonempty_statedProj_of_isOmegaTwo_false h
  obtain ⟨eD⟩ := nonempty_twistedD_of_isOmegaTwo_false hn h
  exact glbCore_three_of_catGroup ⟨.twistedD n twoPP, valid_twistedD_of_four_le hn twoPP⟩
    (by simp [TauCeti.LieTypeIndex.characteristic_twistedD, twoPP])
    (by rintro ⟨q, -, -, hq⟩; simp at hq) eD (two_le_pRank_three_of_minus hn eP) T

theorem glbCore_three_omega_minus_three
    {L : Type} [Group L] [Finite L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo false 3 L) (T : Sylow 3 L) :
    CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  obtain ⟨e⟩ := nonempty_twistedA_of_isOmegaTwo_false_three h
  exact glbCore_three_of_catGroup ⟨.twistedA 3 twoPP, valid_twistedA_three_two⟩
    (by simp [TauCeti.LieTypeIndex.characteristic_twistedA, twoPP])
    (by rintro ⟨q, -, -, hq⟩; simp at hq) e
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_twistedA3
      valid_twistedA_three_two e (by norm_num [twoPP])) T

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Omega2401 (glbCore_three_omega_minus_three glbCore_three_omega_minus
  glbCore_three_omega_plus nonempty_alt_eight_of_isOmegaTwo_true_three)

theorem kFact2401ThreeOmega_holds
    : KFact2401ThreeOmega := by
  intro A _ _ L E ε n hn hLω hE J hJ
  obtain ⟨Q, hQ⟩ := hE
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    cases ε
    · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401.le_of_glbCore_eq_top hQ hJ
        (glbCore_three_omega_minus_three hLω Q)
    · obtain ⟨eA⟩ := nonempty_alt_eight_of_isOmegaTwo_true_three hLω
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Alt2401.le_of_alt (n := 8)
        (by norm_num) eA hQ hJ
  · cases ε
    · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401.le_of_glbCore_eq_top hQ hJ
        (glbCore_three_omega_minus h4 hLω Q)
    · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401.le_of_glbCore_eq_top hQ hJ
        (glbCore_three_omega_plus h4 hLω Q)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
