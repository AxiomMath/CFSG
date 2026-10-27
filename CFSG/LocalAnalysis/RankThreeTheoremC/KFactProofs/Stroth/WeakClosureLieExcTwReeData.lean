module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWords
public import CFSG.RankThree.PartOne.KLR.SectorTori
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwReeLift
public import CFSG.RankThree.PartOne.K128.TorusShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K128
  CFSG.RankThree.Lattice
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false

section Check


@[expose] def reeBl : List (List ℤ) := [[0, 0, 0, 1], [0, 0, 1, 0], [0, 2, 0, 0], [2, 0, 0, 0]]

theorem reeB_eq : reeB = toMat ReeTag.F4.tag.rank reeBl := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem ree_comm_of_check (lw lu lu' : List (Fin ReeTag.F4.tag.rank))
    (hlu' : lu.map ReeTag.F4.perm = lu')
    (h : lmul ReeTag.F4.tag.rank
        (lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (lw.map Fin.val))
        (lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (lu'.map Fin.val)) =
      lmul ReeTag.F4.tag.rank
        (lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (lu.map Fin.val))
        (lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (lw.map Fin.val))) :
    (coxeterSystem ReeTag.F4.tag).wordProd lw *
        ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd lu) =
      (coxeterSystem ReeTag.F4.tag).wordProd lu * (coxeterSystem ReeTag.F4.tag).wordProd lw := by
  rw [ReeTag.weylPerm_wordProd, hlu']
  have h' := congrArg (toMat ReeTag.F4.tag.rank) h
  rw [toMat_lmul, toMat_lmul, toMat_lword _ (toMat_cartanList _) lw,
    toMat_lword _ (toMat_cartanList _) lu', toMat_lword _ (toMat_cartanList _) lu] at h'
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin ReeTag.F4.tag.rank → ℤ) fun x => ?_
  rw [mul_smul, mul_smul, wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec,
    wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h']

theorem ree_commWord_neg_of_check (la lb : List (Fin ReeTag.F4.tag.rank))
    (h : lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) ((twCommWord lb la).map Fin.val) =
      lsmul ReeTag.F4.tag.rank (-1) (lid ReeTag.F4.tag.rank)) (x : Fin ReeTag.F4.tag.rank → ℤ) :
    ⁅(coxeterSystem ReeTag.F4.tag).wordProd la, (coxeterSystem ReeTag.F4.tag).wordProd lb⁆⁻¹ • x =
      -x := by
  rw [tw_commWord_smul, ← toMat_lword _ (toMat_cartanList _), h, toMat_lsmul, toMat_lid,
    Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]

theorem weylMat_inv_wordProd (l : List (Fin ReeTag.F4.tag.rank)) :
    weylMat ((coxeterSystem ReeTag.F4.tag).wordProd l)⁻¹ = wordMat ReeTag.F4.tag l.reverse := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [weylMat_mulVec, ← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_wordMat_mulVec]

theorem ree_det_of_check (lw : List (Fin ReeTag.F4.tag.rank)) {n : ℕ} {c : ℤ} (hn : n ≠ 0)
    (hc : 2 ≤ c.natAbs)
    (h : lpow ReeTag.F4.tag.rank (lmul ReeTag.F4.tag.rank reeBl
        (lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (lw.reverse.map Fin.val))) n =
      lsmul ReeTag.F4.tag.rank c (lid ReeTag.F4.tag.rank)) (a : ℕ) :
    (1 - (2 ^ a : ℤ) • (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd lw)⁻¹)).det ≠
      0 := by
  have hY : (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd lw)⁻¹) ^ n =
      c • (1 : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ) := by
    have h' := congrArg (toMat ReeTag.F4.tag.rank) h
    rw [toMat_lpow, toMat_lmul, toMat_lword _ (toMat_cartanList _) lw.reverse, toMat_lsmul,
      toMat_lid, ← reeB_eq] at h'
    rw [weylMat_inv_wordProd]
    exact h'
  refine det_one_sub_smul_ne_zero_of_pow_eq_smul _ hn hY ?_
  intro h1
  have h2 := congrArg Int.natAbs h1
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at h2
  rw [Int.natAbs_one] at h2
  have hpos : 0 < ((2 : ℤ).natAbs ^ a) ^ n := by positivity
  have h3 : ((2 : ℤ).natAbs ^ a) ^ n * 2 ≤ ((2 : ℤ).natAbs ^ a) ^ n * c.natAbs :=
    Nat.mul_le_mul_left _ hc
  linarith

end Check

section Data


@[expose] def reeOneW : List (Fin ReeTag.F4.tag.rank) := []
@[expose] def reeOneA : List (Fin ReeTag.F4.tag.rank) := [3, 0]
@[expose] def reeOneB : List (Fin ReeTag.F4.tag.rank) := [2, 1, 2, 3, 1, 2, 0, 1, 2, 1]
@[expose] def reeOneA' : List (Fin ReeTag.F4.tag.rank) := [0, 3]
@[expose] def reeOneB' : List (Fin ReeTag.F4.tag.rank) := [1, 2, 1, 0, 2, 1, 3, 2, 1, 2]

theorem reeOneA_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeOneW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeOneA) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeOneA *
      (coxeterSystem ReeTag.F4.tag).wordProd reeOneW :=
  ree_comm_of_check _ _ reeOneA' (by decide) (by decide +kernel)

theorem reeOneB_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeOneW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeOneB) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeOneB *
      (coxeterSystem ReeTag.F4.tag).wordProd reeOneW :=
  ree_comm_of_check _ _ reeOneB' (by decide) (by decide +kernel)

theorem reeOne_neg : ∀ x : Fin ReeTag.F4.tag.rank → ℤ,
    ⁅(coxeterSystem ReeTag.F4.tag).wordProd reeOneA,
      (coxeterSystem ReeTag.F4.tag).wordProd reeOneB⁆⁻¹ • x = -x :=
  ree_commWord_neg_of_check _ _ (by decide +kernel)

theorem reeOne_det (a : ℕ) :
    (1 - (2 ^ a : ℤ) • (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd reeOneW)⁻¹)).det ≠ 0 :=
  ree_det_of_check _ (n := 2) (c := 2) (by norm_num) (by norm_num) (by decide +kernel) a

theorem reeOne_data (a : ℕ) :
    ∃ u₁ u₂ : WeylGroup ReeTag.F4.tag,
      wPhi1 * ReeTag.F4.weylPerm u₁ = u₁ * wPhi1 ∧
      wPhi1 * ReeTag.F4.weylPerm u₂ = u₂ * wPhi1 ∧
      (∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) ∧
      (1 - (2 ^ a : ℤ) • (reeB * weylMat wPhi1⁻¹)).det ≠ 0 :=
  ⟨(coxeterSystem ReeTag.F4.tag).wordProd reeOneA,
    (coxeterSystem ReeTag.F4.tag).wordProd reeOneB, reeOneA_comm, reeOneB_comm,
    reeOne_neg, reeOne_det a⟩


@[expose] def reeTwoW : List (Fin ReeTag.F4.tag.rank) := [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0]
@[expose] def reeTwoA : List (Fin ReeTag.F4.tag.rank) := [2, 0]
@[expose] def reeTwoB : List (Fin ReeTag.F4.tag.rank) := [3, 1, 2, 0, 1, 2, 3, 2, 0, 1]
@[expose] def reeTwoA' : List (Fin ReeTag.F4.tag.rank) := [1, 3]
@[expose] def reeTwoB' : List (Fin ReeTag.F4.tag.rank) := [0, 2, 1, 3, 2, 1, 0, 1, 3, 2]

theorem reeTwoA_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeTwoW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeTwoA) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeTwoA *
      (coxeterSystem ReeTag.F4.tag).wordProd reeTwoW :=
  ree_comm_of_check _ _ reeTwoA' (by decide) (by decide +kernel)

theorem reeTwoB_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeTwoW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeTwoB) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeTwoB *
      (coxeterSystem ReeTag.F4.tag).wordProd reeTwoW :=
  ree_comm_of_check _ _ reeTwoB' (by decide) (by decide +kernel)

theorem reeTwo_neg : ∀ x : Fin ReeTag.F4.tag.rank → ℤ,
    ⁅(coxeterSystem ReeTag.F4.tag).wordProd reeTwoA,
      (coxeterSystem ReeTag.F4.tag).wordProd reeTwoB⁆⁻¹ • x = -x :=
  ree_commWord_neg_of_check _ _ (by decide +kernel)

theorem reeTwo_det (a : ℕ) :
    (1 - (2 ^ a : ℤ) • (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd reeTwoW)⁻¹)).det ≠ 0 :=
  ree_det_of_check _ (n := 2) (c := -2) (by norm_num) (by norm_num) (by decide +kernel) a

theorem reeTwo_data (a : ℕ) :
    ∃ u₁ u₂ : WeylGroup ReeTag.F4.tag,
      wPhi2 * ReeTag.F4.weylPerm u₁ = u₁ * wPhi2 ∧
      wPhi2 * ReeTag.F4.weylPerm u₂ = u₂ * wPhi2 ∧
      (∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) ∧
      (1 - (2 ^ a : ℤ) • (reeB * weylMat wPhi2⁻¹)).det ≠ 0 :=
  ⟨(coxeterSystem ReeTag.F4.tag).wordProd reeTwoA,
    (coxeterSystem ReeTag.F4.tag).wordProd reeTwoB, reeTwoA_comm, reeTwoB_comm,
    reeTwo_neg, reeTwo_det a⟩


@[expose] def reeFourMW : List (Fin ReeTag.F4.tag.rank) := [0, 1, 0, 2, 1, 0]
@[expose] def reeFourMA : List (Fin ReeTag.F4.tag.rank) := [2, 1, 2, 1]
@[expose] def reeFourMB : List (Fin ReeTag.F4.tag.rank) := [3, 2, 0, 1, 2, 3, 2, 0, 1, 0]
@[expose] def reeFourMA' : List (Fin ReeTag.F4.tag.rank) := [1, 2, 1, 2]
@[expose] def reeFourMB' : List (Fin ReeTag.F4.tag.rank) := [0, 1, 3, 2, 1, 0, 1, 3, 2, 3]

theorem reeFourMA_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeFourMW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeFourMA) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourMA *
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourMW :=
  ree_comm_of_check _ _ reeFourMA' (by decide) (by decide +kernel)

theorem reeFourMB_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeFourMW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeFourMB) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourMB *
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourMW :=
  ree_comm_of_check _ _ reeFourMB' (by decide) (by decide +kernel)

theorem reeFourM_neg : ∀ x : Fin ReeTag.F4.tag.rank → ℤ,
    ⁅(coxeterSystem ReeTag.F4.tag).wordProd reeFourMA,
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourMB⁆⁻¹ • x = -x :=
  ree_commWord_neg_of_check _ _ (by decide +kernel)

theorem reeFourM_det (a : ℕ) :
    (1 - (2 ^ a : ℤ) • (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd reeFourMW)⁻¹)).det ≠ 0 :=
  ree_det_of_check _ (n := 4) (c := -4) (by norm_num) (by norm_num) (by decide +kernel) a

theorem reeFourM_data (a : ℕ) :
    ∃ u₁ u₂ : WeylGroup ReeTag.F4.tag,
      wPhi4m * ReeTag.F4.weylPerm u₁ = u₁ * wPhi4m ∧
      wPhi4m * ReeTag.F4.weylPerm u₂ = u₂ * wPhi4m ∧
      (∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) ∧
      (1 - (2 ^ a : ℤ) • (reeB * weylMat wPhi4m⁻¹)).det ≠ 0 :=
  ⟨(coxeterSystem ReeTag.F4.tag).wordProd reeFourMA,
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourMB, reeFourMA_comm, reeFourMB_comm,
    reeFourM_neg, reeFourM_det a⟩


@[expose] def reeFourPW : List (Fin ReeTag.F4.tag.rank) := [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]
@[expose] def reeFourPA : List (Fin ReeTag.F4.tag.rank) := [2, 1, 2, 1]
@[expose] def reeFourPB : List (Fin ReeTag.F4.tag.rank) := [3, 2, 0, 1, 2, 3, 2, 0, 1, 0]
@[expose] def reeFourPA' : List (Fin ReeTag.F4.tag.rank) := [1, 2, 1, 2]
@[expose] def reeFourPB' : List (Fin ReeTag.F4.tag.rank) := [0, 1, 3, 2, 1, 0, 1, 3, 2, 3]

theorem reeFourPA_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeFourPW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeFourPA) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourPA *
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourPW :=
  ree_comm_of_check _ _ reeFourPA' (by decide) (by decide +kernel)

theorem reeFourPB_comm : (coxeterSystem ReeTag.F4.tag).wordProd reeFourPW *
    ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd reeFourPB) =
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourPB *
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourPW :=
  ree_comm_of_check _ _ reeFourPB' (by decide) (by decide +kernel)

theorem reeFourP_neg : ∀ x : Fin ReeTag.F4.tag.rank → ℤ,
    ⁅(coxeterSystem ReeTag.F4.tag).wordProd reeFourPA,
      (coxeterSystem ReeTag.F4.tag).wordProd reeFourPB⁆⁻¹ • x = -x :=
  ree_commWord_neg_of_check _ _ (by decide +kernel)

theorem reeFourP_det (a : ℕ) :
    (1 - (2 ^ a : ℤ) • (reeB * weylMat ((coxeterSystem ReeTag.F4.tag).wordProd reeFourPW)⁻¹)).det ≠ 0 :=
  ree_det_of_check _ (n := 4) (c := -4) (by norm_num) (by norm_num) (by decide +kernel) a

theorem reeFourP_data (a : ℕ) :
    ∃ u₁ u₂ : WeylGroup ReeTag.F4.tag,
      wPhi4p * ReeTag.F4.weylPerm u₁ = u₁ * wPhi4p ∧
      wPhi4p * ReeTag.F4.weylPerm u₂ = u₂ * wPhi4p ∧
      (∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) ∧
      (1 - (2 ^ a : ℤ) • (reeB * weylMat wPhi4p⁻¹)).det ≠ 0 :=
  ⟨(coxeterSystem ReeTag.F4.tag).wordProd reeFourPA,
    (coxeterSystem ReeTag.F4.tag).wordProd reeFourPB, reeFourPA_comm, reeFourPB_comm,
    reeFourP_neg, reeFourP_det a⟩

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
