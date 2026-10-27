module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveTwoDDefs
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.Monster.B.Final.SeedUnit
public import Certificates.Certificate101702

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Monster.B


theorem babyTwoDFiveAFact_holds : BabyTwoDFiveAFact := by
  obtain ⟨T, Y, mT, mY, hTT, hT1, hY5, hY1, hTY, hrT, hrY⟩ :=
    Certificates.certificate101702
  set t := seedUnit mT two_ne_zero (by rw [sq]; exact hTT)
  set y := seedUnit mY (by norm_num) hY5
  have vt : bMat t = T := bMat_seedUnit _ _ _
  have vy : bMat y = Y := bMat_seedUnit _ _ _
  have hT2 : orderOf t = 2 :=
    orderOf_of_bMat Nat.prime_two (by rw [vt, sq]; exact hTT) (by rw [vt]; exact hT1)
  have hW₃ := CFSG.Monster.Existence.babyInv_two_of_rank_2168 hT2 (by
    change Matrix.rank (bMat t - 1) = 2168
    rw [vt]
    exact hrT)
  exact ⟨t, y, hW₃,
    orderOf_of_bMat Nat.prime_five (by rw [vy]; exact hY5) (by rw [vy]; exact hY1),
    (comm_of_bMat (by rw [vt, vy]; exact hTY)).symm, by rw [vy]; exact hrY⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017
