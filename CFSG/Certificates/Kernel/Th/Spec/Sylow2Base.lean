
module

public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Th.Spec.SylowOrbitBase
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.Th.Max3S.BasicBase
import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TcS
import CFSG.Certificates.Kernel.Fam.Lin
import CFSG.Certificates.Kernel.Th.Gen.Max3
import CFSG.Open.Defs
import CFSG.Sporadic.Th.Max3.AllConjBase
import CFSG.Sporadic.Th.Max3.AllConjInputsBase
import CFSG.Sporadic.Th.Max3.CoreBase
import CFSG.Sporadic.Th.Max3.InvolutionsBase
import CFSG.Sporadic.Th.Max3.QuotientBase
import CFSG.Sporadic.Th.Max3.RelationsBase

@[expose] public section

namespace CFSG.KC.Th.Spec.Sylow2

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Gen CFSG.KC.Th.Max3S CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.SylowOrbit CFSG.KC.Th.Spec.FwdRel CFSG.KC.Th.Spec.FwdSlp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

private theorem marked_iff (m r : ℕ) : marked m r = true ↔ m.testBit r = true := by
  unfold marked
  rw [Nat.blt_eq]
  have e : Nat.land m (Nat.shiftLeft 1 r) = (m.testBit r).toNat * 2 ^ r := by
    rw [show Nat.land m (Nat.shiftLeft 1 r) = m &&& (1 <<< r) from rfl, Nat.one_shiftLeft,
      Nat.and_two_pow]
  rw [e]
  cases m.testBit r <;> simp [Nat.two_pow_pos]

private theorem allMarked_of {L n m : ℕ} (h : allMarked L n m = true) {k : ℕ} (hk : k < n) :
    marked m (regAt L k) = true := by
  unfold allMarked at h
  exact (CFSG.KC.Th.Spec.Dce.allB_iff (fun k => marked m (regAt L k)) n).1 h k hk

private theorem uniOK_of {RB : ℕ → ℕ} {c rm up dg Cm Ci Gens m : ℕ}
    (h : uniOK RB c rm up dg Cm Ci Gens m = true) {k : ℕ} (hk : k < m) :
    chkUni up dg (mulB c rm (mulB c rm Cm (RB (regAt Gens k))) Ci) = true := by
  unfold uniOK at h
  exact (CFSG.KC.Th.Spec.Dce.allB_iff (fun k => chkUni up dg
    (mulB c rm (mulB c rm Cm (RB (regAt Gens k))) Ci)) m).1 h k hk

private theorem constsOK_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  exact andB_left (andB_left (andB_left (andB_right (andB_right (andB_left (hg))))))

private theorem seeds_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    SeedS.decOK D.ThSeed_SA D.ThSeed_LA = true ∧
      SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true ∧
      mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA = D.ThS_ONE ∧
      mulB D.ThS_c D.ThS_rm (mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB =
        D.ThS_ONE ∧
      D.ThS_RBf 1 = D.ThSeed_SA ∧ D.ThS_RBf 2 = D.ThSeed_SB := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hdA := andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (hg))))))
  have hdB := andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (hg))))))
  have hA2 := eq_of_eqN
    (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left (hg)))))))
  have hB3 := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (hg)))))))
  have hrbf1 := eq_of_eqN
    (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (hg))))))))
  have hrbf2 := eq_of_eqN
    (andB_left (andB_left (andB_left (andB_left (andB_left (andB_right (hg)))))))
  exact ⟨hdA, hdB, hA2, hB3, hrbf1, hrbf2⟩

private theorem slp_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 = D.sf1 ∧
      regsIn D.ThS_PR2 D.ThS_n2 D.sf1 = true ∧ regsIn D.ThS_GL2 11 D.sf1 = true ∧
      D.ThS_RBp2 1 = D.ThS_RBf 1 ∧ D.ThS_RBp2 2 = D.ThS_RBf 2 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hslp1 := eq_of_eqN
    (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (hg)))))))
  have hpr2 :=
    andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (hg)))))))
  have hprGL :=
    andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (hg)))))))
  have hrbp1 := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (hg)))))))
  have hrbp2 := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (hg)))))))
  exact ⟨hslp1, hpr2, hprGL, hrbp1, hrbp2⟩

private theorem mark_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    runMarked D.l0 9922901054488310019520462851 =
        356811923176489960380431918284599405230162057 ∧
      allMarked D.ThS_PR2 15 174224571863520488467007772599902053335040 = true := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrmark := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (hg)))))))
  have hall := andB_left (andB_left (andB_right (andB_left (andB_left (andB_right (hg))))))
  exact ⟨hrmark, hall⟩

private theorem uni_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    mulB D.ThS_c D.ThS_rm D.ThS_Cm2 D.ThS_Ci2 = D.ThS_ONE ∧
      uniOK D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_up D.ThS_dg D.ThS_Cm2 D.ThS_Ci2
        D.ThS_GL2 11 = true := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hcc := eq_of_eqN
    (andB_left (andB_left (andB_left (andB_right (andB_left (andB_right (hg)))))))
  have huni := andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (hg))))))
  exact ⟨hcc, huni⟩

private theorem blocks_of (D : Sylow2Data) (h : sylow2Chk D = true) :
    blocksOK D.ThS_BL2 D.ThS_nb2 D.ThS_n2 = true := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  exact
    andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (hg)))))))

private theorem blockOK_of {RB PT : ℕ → ℕ} {rm PR BL b sfT SS : ℕ} {TC SC : List ℕ}
    (hpt : PT 0 < 2 ^ 248) (hbf : baseFixed RB rm PR (PT 0) (blkTo BL b) 15 = true)
    (hrt : runTree RB PT rm PR (blkFr BL b) (blkTo BL b) TC 2 = sfT)
    (hsf : sfT = Nat.succ (Nat.pow 2 (Nat.sub (blkTo BL b) (blkFr BL b))))
    (hrs : DceS.runSorted PT 11 (2 ^ (blkTo BL b - blkFr BL b)) SC 1 = SS)
    (hcnt : DceS.sortedCount SS = 2 ^ (blkTo BL b - blkFr BL b)) :
    BlockOK RB rm PR 15 2 BL b := by
  refine ⟨PT, TC, SC, SS, hpt, hbf, ?_, hrs, hcnt⟩
  rw [hrt, hsf]
  rfl

private theorem blockOK_0 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf2 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 5 5) (bitsN D.ThS_BL2 0 5))))
    (hpt : D.ThS_PT2_0 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 0 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (hg)))))))
  have hbf := andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_1 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf4 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 15 5) (bitsN D.ThS_BL2 10 5))))
    (hpt : D.ThS_PT2_1 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 1 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (hg)))))))
  have hbf := andB_left (andB_left (andB_right (andB_right (andB_left (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_2 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf6 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 25 5) (bitsN D.ThS_BL2 20 5))))
    (hpt : D.ThS_PT2_2 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 2 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (hg)))))))
  have hbf := andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (hg))))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_3 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf8 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 35 5) (bitsN D.ThS_BL2 30 5))))
    (hpt : D.ThS_PT2_3 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 3 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (hg)))))))
  have hbf :=
    andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (hg)))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_left (andB_left (andB_left (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_4 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf10 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 45 5) (bitsN D.ThS_BL2 40 5))))
    (hpt : D.ThS_PT2_4 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 4 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (hg)))))))
  have hbf := andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_right (andB_left (andB_left (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_5 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf12 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 55 5) (bitsN D.ThS_BL2 50 5))))
    (hpt : D.ThS_PT2_5 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 5 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (hg)))))))
  have hbf := andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_left (andB_right (andB_left (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_6 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf14 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 65 5) (bitsN D.ThS_BL2 60 5))))
    (hpt : D.ThS_PT2_6 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 6 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (hg))))))))
  have hbf := andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_7 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf16 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 75 5) (bitsN D.ThS_BL2 70 5))))
    (hpt : D.ThS_PT2_7 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 7 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (hg))))))))
  have hrs := eq_of_eqN
    (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left (hg)))))))
  have hbf :=
    andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (hg)))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (hg))))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_8 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf18 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 85 5) (bitsN D.ThS_BL2 80 5))))
    (hpt : D.ThS_PT2_8 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 8 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left (hg)))))))
  have hbf := andB_left (andB_left (andB_left (andB_right (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_9 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf20 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 95 5) (bitsN D.ThS_BL2 90 5))))
    (hpt : D.ThS_PT2_9 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 9 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (hg)))))))
  have hbf := andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_10 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf22 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 105 5) (bitsN D.ThS_BL2 100 5))))
    (hpt : D.ThS_PT2_10 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 10 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (hg)))))))
  have hrs := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (hg)))))))
  have hbf := andB_left (andB_left (andB_right (andB_right (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (hg)))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem blockOK_11 (D : Sylow2Data) (h : sylow2Chk D = true)
    (hsf : D.sf24 = Nat.succ (Nat.pow 2 (Nat.sub (bitsN D.ThS_BL2 115 5) (bitsN D.ThS_BL2 110 5))))
    (hpt : D.ThS_PT2_11 0 < 2 ^ 248) :
    BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 11 := by
  unfold sylow2Chk at h
  have hg := andB_left h
  unfold sylow2ChkGen at hg
  have hrt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (hg))))))))
  have hrs := eq_of_eqN
    (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (hg))))))))
  have hbf := andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (hg))))))
  have hcnt := eq_of_eqN
    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (hg))))))))
  exact blockOK_of hpt hbf hrt hsf hrs hcnt

private theorem isPGroup_closure (D : Sylow2Data)
    (hk : constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (hcc : mulB D.ThS_c D.ThS_rm D.ThS_Cm2 D.ThS_Ci2 = D.ThS_ONE)
    (huni : uniOK D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_up D.ThS_dg D.ThS_Cm2 D.ThS_Ci2
      D.ThS_GL2 11 = true) :
    IsPGroup 2 (Subgroup.closure {g : J | ∃ j < 11,
      𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hcm : pkMat D.ThS_Cm2 * pkMat D.ThS_Ci2 = 1 := by
    rw [← pkMat_mulB hk, hcc]
    exact pkMat_one hk
  let c : GL (Fin 248) (ZMod 2) :=
    ⟨pkMat D.ThS_Cm2, pkMat D.ThS_Ci2, hcm, mul_eq_one_comm.mp hcm⟩
  let S : Set J := {g | ∃ j < 11, 𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}
  let U' : Subgroup J := ((CFSG.KS.J4Hub.luSub 2 248).comap
    (MulAut.conj c).toMonoidHom).comap J.subtype
  have hUle : Subgroup.closure S ≤ U' := by
    refine (Subgroup.closure_le U').2 ?_
    rintro g ⟨j, hj, eg⟩
    have hchk := uniOK_of huni hj
    have hLU : CFSG.KS.J4Hub.LowerUni
        (pkMat (mulB D.ThS_c D.ThS_rm (mulB D.ThS_c D.ThS_rm D.ThS_Cm2
          (D.ThS_RBp2 (regAt D.ThS_GL2 j))) D.ThS_Ci2)) :=
      chkUni_spec hk hchk
    have hv : ((c * (g : GL (Fin 248) (ZMod 2)) * c⁻¹ : GL (Fin 248) (ZMod 2)) :
        Matrix (Fin 248) (Fin 248) (ZMod 2)) =
        pkMat D.ThS_Cm2 * pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j)) * pkMat D.ThS_Ci2 := by
      rw [Units.val_mul, Units.val_mul, eg]
      rfl
    change CFSG.KS.J4Hub.LowerUni
      ((c * (g : GL (Fin 248) (ZMod 2)) * c⁻¹ : GL (Fin 248) (ZMod 2)) :
        Matrix (Fin 248) (Fin 248) (ZMod 2))
    rw [hv]
    simp only [pkMat_mulB hk] at hLU
    exact hLU
  intro g
  have hgU := hUle g.2
  change CFSG.KS.J4Hub.LowerUni
    ((c * (g : GL (Fin 248) (ZMod 2)) * c⁻¹ : GL (Fin 248) (ZMod 2)) :
      Matrix (Fin 248) (Fin 248) (ZMod 2)) at hgU
  refine ⟨248, Subtype.ext (Subtype.ext ?_)⟩
  have h1 : (c * (g : GL (Fin 248) (ZMod 2)) * c⁻¹) ^ (2 ^ 248) = 1 :=
    Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hgU.pow_eq_one)
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
  simpa using h1

private theorem pinHead (D : Sylow2Data) (h : sylow2Chk D = true) :
    D.l0 = D.cs1 ∧ D.sf1 < 2048 ∧
      D.ThS_GL2 = 106488374662378949350121827748335640 ∧
      D.ThS_n2 = 15 ∧ D.ThS_nb2 = 12 := by
  have hp := andB_right h
  unfold sylow2Pins at hp
  have hl0 := of_decide_eq_true (andB_left hp)
  have hp := andB_right hp
  have hsf1lt := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hGL2 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hn2 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hnb2 := eq_of_eqN (andB_left hp)
  exact ⟨hl0, hsf1lt, hGL2, hn2, hnb2⟩

private theorem pins_blocks_lo (D : Sylow2Data) (h : sylow2Chk D = true) :
    ∀ b < 6, BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 b := by
  have hp := andB_right h
  unfold sylow2Pins at hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hsf0 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf1 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf2 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf3 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf4 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf5 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hpt0 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt1 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt2 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt3 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt4 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt5 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  intro b hb
  interval_cases b
  · exact blockOK_0 D h hsf0 hpt0
  · exact blockOK_1 D h hsf1 hpt1
  · exact blockOK_2 D h hsf2 hpt2
  · exact blockOK_3 D h hsf3 hpt3
  · exact blockOK_4 D h hsf4 hpt4
  · exact blockOK_5 D h hsf5 hpt5

private theorem pins_blocks_hi (D : Sylow2Data) (h : sylow2Chk D = true) :
    ∀ b, 6 ≤ b → b < 12 → BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 b := by
  have hp := andB_right h
  unfold sylow2Pins at hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hsf6 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf7 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf8 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf9 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf10 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hsf11 := eq_of_eqN (andB_left hp)
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hp := andB_right hp
  have hpt6 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt7 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt8 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt9 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt10 := lt_of_ltN (andB_left hp)
  have hp := andB_right hp
  have hpt11 := lt_of_ltN hp
  intro b hlb hub
  interval_cases b
  · exact blockOK_6 D h hsf6 hpt6
  · exact blockOK_7 D h hsf7 hpt7
  · exact blockOK_8 D h hsf8 hpt8
  · exact blockOK_9 D h hsf9 hpt9
  · exact blockOK_10 D h hsf10 hpt10
  · exact blockOK_11 D h hsf11 hpt11

private theorem marked_GL2 : ∀ k < 83,
    Nat.testBit 4845166530511870126718976 k = true →
      ∃ j < 11, k = regAt 106488374662378949350121827748335640 j := by decide +kernel

end CFSG.KC.Th.Spec.Sylow2

end
