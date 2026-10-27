module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSOBase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Models CFSG.Yardstones.Md0ec50421ce4

theorem orthPlus_index_fam (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hns : ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3)
    (hP : KD264Y1IsOrthPlus d.1) : KD264Y1Fam d.1 := by
  obtain ⟨d1, hv⟩ := d
  have hq3 := characteristic_ne_three_of_not_chev ⟨d1, hv⟩ hns
  change KD264Y1IsOrthPlus d1 at hP
  change d1.characteristic ≠ 3 at hq3
  obtain ⟨n, q, rfl⟩ := hP
  have hq : q.p ≠ 3 := by rwa [TauCeti.LieTypeIndex.characteristic_D] at hq3
  have hn : 4 ≤ n :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
  exfalso
  have h4 := four_le_pRank_of_D
    (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hv⟩).Group)
    n q hn hv (MulEquiv.refl _) hq
  omega

theorem orthMinus_index_fam (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hns : ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3)
    (hP : KD264Y1IsOrthMinus d.1) : KD264Y1Fam d.1 := by
  obtain ⟨d1, hv⟩ := d
  have hq3 := characteristic_ne_three_of_not_chev ⟨d1, hv⟩ hns
  change KD264Y1IsOrthMinus d1 at hP
  change d1.characteristic ≠ 3 at hq3
  obtain ⟨n, q, rfl⟩ := hP
  have hq : q.p ≠ 3 := by rwa [TauCeti.LieTypeIndex.characteristic_twistedD] at hq3
  have hn : 4 ≤ n :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · exact fam_of_D4 ⟨q, rfl⟩
  · exfalso
    have h4 := four_le_pRank_of_twistedD
      (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩).Group)
      n q hn5 hv (MulEquiv.refl _) hq
    omega

theorem KD264Y1ClsOrthPlus_holds : KD264Y1ClsOrthPlus := by
  intro d hfin hns _ _ hrk hP
  exact orthPlus_index_fam d hns hrk hP

theorem KD264Y1ClsOrthMinus_holds : KD264Y1ClsOrthMinus := by
  intro d hfin hns _ _ hrk hP
  exact orthMinus_index_fam d hns hrk hP

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
