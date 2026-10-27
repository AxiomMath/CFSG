module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Parts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem kd264X1OmPlusPart_of_core (hcore : KD264OmPlusCore) : KD264X1OmPlusPart := by
  intro d n q hd inst
  obtain ⟨x, hv⟩ := d
  dsimp only at hd
  subst hd
  unfold KD264X1At
  intro h1 h2 h3 h4 h5 h6
  unfold KD264X1Concl
  intro A hA hrank
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  obtain ⟨hp2, hf1⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq
  have hMod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv hp2
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group)
  have hsimp := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
    _ n q.p q.exponent hMod).2
  obtain ⟨⟨-, -, hn4⟩, K, hKfield, hKfin, hKcard, ⟨φ⟩⟩ := hMod
  have hn5 : 5 ≤ n := by
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · have h4n : n = 4 := by omega
      subst h4n
      exact (h2 (show (3 : ℕ) = 3 ∧ q.card = 2 from ⟨rfl, hq⟩)).elim
    · exact hge
  have hK2 : Nat.card K = 2 := by
    rw [hKcard, hp2, hf1]
    norm_num
  haveI : CharP K 2 := om_charP_two_of_card_two K hK2
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group := hsimp
  have hrk2 : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group) := by
    have hTG : CFSG.Open.pRank 3
        (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ
    rw [hTG]
    exact le_trans (by norm_num)
      (CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := K) hn4)
  have hZS := om_center_eq_bot_of_simple_pRank hrk2
  have hinner := CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeD_two
    hv hq hn5 (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group)
  exact good_of_core_transport φ hZS hinner (hcore n hn5 K hK2) A hA hrank

theorem kd264X1OmMinusPart_of_core (hcore : KD264OmMinusCore) : KD264X1OmMinusPart := by
  intro d n q hd inst
  obtain ⟨x, hv⟩ := d
  dsimp only at hd
  subst hd
  unfold KD264X1At
  intro h1 h2 h3 h4 h5 h6
  unfold KD264X1Concl
  intro A hA hrank
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  obtain ⟨hp2, hf1⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq
  have hMod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hp2
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group)
  have hsimp := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
    _ n q.p q.exponent hMod).2
  obtain ⟨⟨-, -, hn4⟩, K, hKfield, hKfin, hKcard, b, c, hirr, ⟨φ⟩⟩ := hMod
  have hK2 : Nat.card K = 2 := by
    rw [hKcard, hp2, hf1]
    norm_num
  haveI : CharP K 2 := om_charP_two_of_card_two K hK2
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group :=
    hsimp
  have hrk2 : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group) := by
    have hTG : CFSG.Open.pRank 3
        (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group) =
        CFSG.Open.pRank 3
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ
    rw [hTG]
    exact le_trans (by norm_num)
      (CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := K) hn4 b c)
  have hZS := om_center_eq_bot_of_simple_pRank hrk2
  have hinner :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeTwistedD_two hv hq
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group)
  exact good_of_core_transport φ hZS hinner (hcore n hn4 K hK2 b c hirr) A hA hrank

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
