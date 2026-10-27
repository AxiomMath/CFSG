module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSOBase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Models CFSG.Yardstones.Md0ec50421ce4

theorem sym_index_fam (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hns : ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3)
    (hP : KD264Y1IsSym d.1) : KD264Y1Fam d.1 := by
  obtain ⟨d1, hv⟩ := d
  have hq3 := characteristic_ne_three_of_not_chev ⟨d1, hv⟩ hns
  change KD264Y1IsSym d1 at hP
  change d1.characteristic ≠ 3 at hq3
  rcases hP with ⟨n, q, rfl⟩ | ⟨n, q, rfl⟩
  ·
    have hq : q.p ≠ 3 := by rwa [TauCeti.LieTypeIndex.characteristic_B] at hq3
    have hr : 2 ≤ n :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
    · exfalso
      have h2 := pRank_le_two_of_B2
        (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group)
        q hv (MulEquiv.refl _) hq
      omega
    · exact fam_of_B3 ⟨q, rfl⟩
    · exfalso
      have h4 := four_le_pRank_of_B
        (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group)
        n q hn4 hv (MulEquiv.refl _) hq
      omega
  ·
    have hr : 3 ≤ n :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · exact fam_of_C3 ⟨q, rfl⟩
    · exfalso
      have h4 := four_le_pRank_of_C
        (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.C n q, hv⟩).Group)
        n q hn4 hv (MulEquiv.refl _)
      omega

theorem KD264Y1ClsSym_holds : KD264Y1ClsSym := by
  intro d hfin hns _ _ hrk hP
  exact sym_index_fam d hns hrk hP

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
