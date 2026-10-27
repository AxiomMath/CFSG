module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsExcRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem KD264Y1ClsExc_holds :
    KD264Y1ClsExc := by
  intro d hfin hns hk2 hk3 hrk hexc
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => exact (hexc : False).elim
  | twistedA r q => exact (hexc : False).elim
  | B r q => exact (hexc : False).elim
  | C r q => exact (hexc : False).elim
  | D r q => exact (hexc : False).elim
  | twistedD r q => exact (hexc : False).elim
  | E6 q =>
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      ⟨.E6 q, hv⟩ trivial (MulEquiv.refl _)
    omega
  | E7 q =>
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      ⟨.E7 q, hv⟩ trivial (MulEquiv.refl _)
    omega
  | E8 q =>
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      ⟨.E8 q, hv⟩ trivial (MulEquiv.refl _)
    omega
  | F4 q =>
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      ⟨.F4 q, hv⟩ trivial (MulEquiv.refl _)
    omega
  | G2 q =>
    by_cases hp : q.p = 3
    · exact (hns (isChevSimple_three_of_char ⟨.G2 q, hv⟩
        (by simpa [TauCeti.LieTypeIndex.characteristic_G2] using hp))).elim
    · by_cases hq8 : q.p ^ q.exponent = 8
      · exact (hk2 (by simp [k2Lie, hq8])).elim
      · have h3 : 3 ≠ q.p := fun h => hp h.symm
        have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) ≤ 2 :=
          pRank_three_top_le_two_of_rankLE2 (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2
            q hv h3)
        omega
  | twistedE6 q =>
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      ⟨.twistedE6 q, hv⟩ trivial (MulEquiv.refl _)
    omega
  | trialityD4 q =>
    by_cases hp : q.p = 3
    · exact (hns (isChevSimple_three_of_char ⟨.trialityD4 q, hv⟩
        (by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hp))).elim
    · have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) ≤ 2 :=
        pRank_three_top_le_two_of_rankLE2
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv hp)
      omega
  | suzuki m =>
    obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
    have hndvd : ¬ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK'
    have hle := pRank_three_top_le_zero_of_not_dvd hndvd
    omega
  | reeG2 m =>
    exact (hns (isChevSimple_three_of_char ⟨.reeG2 m, hv⟩ (by simp))).elim
  | reeF4 m =>
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) ≤ 2 :=
      pRank_three_top_le_two_of_rankLE2
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)
    omega
  | tits => exact (hk2 (by simp [k2Lie])).elim

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
