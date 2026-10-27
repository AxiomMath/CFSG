
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import CFSG.Sporadic.HNSchreier.Order
public import Certificates.Certificate13607
public import Mathlib.GroupTheory.Perm.Centralizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

theorem eleven_parts :
    plettersOK 17 elevenWord = true ∧
    fixedSet hnsData.n #[pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) elevenWord] =
      elevenFix ∧
    natOK natStrongArr (pinvs 12 natStrongArr) elevenWord (natArr cyc11) = true := by
  obtain ⟨h1, h2⟩ := Certificates.certificate13607
  unfold elevenChecksO elevenChecksR at h1
  rw [← hRegs_eq, ← hStrongArr_eq] at h1
  unfold elevenChecksH at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  unfold elevenNatCheck at h2
  rw [← natStrongArr_eq] at h2
  exact ⟨h1.1, h1.2, h2⟩

theorem natWord_eleven :
    natWord elevenWord = sigma11 :=
  natWord_of_natOK prep_sigma11 eleven_parts.2.2

theorem thetaHom_eleven :
    thetaHom ⟨elevenJ, elevenJ_mem⟩ = sigma11 := by
  rw [thetaHom_apply, ← natWord_eleven]
  exact thetaJ_hWordH elevenWord

theorem orderOf_elevenJ :
    orderOf elevenJ = 11 := by
  have h1 := orderOf_injective thetaHom thetaHom_inj ⟨elevenJ, elevenJ_mem⟩
  rw [thetaHom_eleven, sigma11_isCycle.orderOf, sigma11_support_card, Subgroup.orderOf_mk] at h1
  exact h1.symm

theorem fix_eleven
    {x : X} (h : elevenJ • x = x) : x.val ∈ elevenFix := by
  have hmem : x.val ∈ fixedSet hnsData.n
      #[pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) elevenWord] := by
    unfold fixedSet
    rw [List.mem_filter, List.mem_range]
    refine ⟨x.isLt, Array.all_eq_true_iff_forall_mem.2 fun g hg => ?_⟩
    rw [Array.mem_singleton] at hg
    rw [hg, beq_iff_eq, prep_hWord eleven_parts.1 x]
    exact congrArg Fin.val h
  rwa [eleven_parts.2.1] at hmem

theorem ncard_fix_le :
    {x : X | elevenJ • x = x}.ncard ≤ 4 := by
  classical
  have hsub : {x : X | elevenJ • x = x} ⊆ ((elevenFix.toFinset.image fun i =>
      (⟨i % hnsData.n, Nat.mod_lt _ (by rw [hns_n]; norm_num)⟩ : X)) : Set X) := by
    intro x hx
    have hm := fix_eleven hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    exact ⟨x.val, hm, Fin.ext (Nat.mod_eq_of_lt x.isLt)⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by decide)

theorem not_commute_elevenJ
    {y : JH} (hy : orderOf y = 5) : y * elevenJ ≠ elevenJ * y := by
  intro hc
  have hyx : y • x0 = x0 := smul_eq_of_commute_of_ncard_lt Nat.prime_five hy hc
    ((mem_HJ_iff_fix _).1 elevenJ_mem) (Set.toFinite _) (ncard_fix_le.trans_lt (by norm_num))
  refine not_commute_of_card_centralizer thetaHom thetaHom_inj elevenJ_mem
    ((mem_HJ_iff_fix y).2 hyx) hy ?_ hc
  rw [thetaHom_eleven, card_centralizer_sigma11]
  norm_num

theorem not_eleven_dvd_card_centralizer
    {x : JH} (hx : orderOf x = 5) :
    ¬ 11 ∣ Nat.card (centralizer ({x} : Set JH)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact not_dvd_card_centralizer_of_not_commute (by rw [card_JH]; norm_num) orderOf_elevenJ
    fun y hy => not_commute_elevenJ (hy.trans hx)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
