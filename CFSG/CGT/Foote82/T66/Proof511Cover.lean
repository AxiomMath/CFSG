module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.CoverGriess
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.CGT.Foote82.Proof511


theorem center_eq_bot_of_psp43 {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hZ : Odd (Nat.card (Subgroup.center J)))
    (hS : CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSp 2 3 1) :
    Subgroup.center J = ⊥ := by
  have hK : CFSG.GH74.GLS.IVK.IsPSp4 (J ⧸ Subgroup.center J) 3 := by
    rcases hS with ⟨-, -, K, iK, fK, hcard, he⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨K, iK, fK, by simpa using hcard, he⟩
    all_goals exact absurd h0 (by norm_num)
  have h := CFSG.GH74.GLS.Stage2.Final.Thm4.psp4_oddCover_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds J
    (J ⧸ Subgroup.center J) (QuotientGroup.mk' (Subgroup.center J))
    (QuotientGroup.mk'_surjective _) hJ.1 (by rw [QuotientGroup.ker_mk'])
    (by rwa [QuotientGroup.ker_mk']) 3 (by decide) hK
  rwa [QuotientGroup.ker_mk'] at h

end CFSG.CGT.Foote82.Proof511
