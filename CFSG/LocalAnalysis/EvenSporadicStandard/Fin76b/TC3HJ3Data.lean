module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HModel
public import Certificates.Certificate26101
public import Certificates.Certificate26103
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import Certificates.Certificate24605

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.Fin76b.TC3H
open CFSG.EvenSporadicStandard.HypOne (zOK)

theorem no_outer_involution :
    ∀ d : ↥j3P, (d : Equiv.Perm (Fin 6156)) * tp 6156 (j3BetaTbl 7) =
        tp 6156 (j3BetaTbl 7) * d →
      (d : Equiv.Perm (Fin 6156)) * tp 6156 (j3Tbl 0) *
        ((d : Equiv.Perm (Fin 6156)) * tp 6156 (j3Tbl 0)) ≠ 1 := by
  classical
  have hperm := (betaHomCheck_permOK Certificates.certificate24603.1).2.2
  have hpermx : permOK 6156 (j3Tbl 0) = true := by
    have h := Certificates.certificate26101.1
    simp only [j3OuterOK, zOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 6156) [natArr (j3BetaTbl 7)]
      [tp 6156 (j3BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hx : CFSG.Monster.B.Co2.Rep 6156 (natArr (j3Tbl 0)) (tp 6156 (j3Tbl 0)) :=
    co2Rep_natArr_iff.2 (rep_tp hpermx)
  have hcount := card_eq_countW (f := commSqxW 6156 (natArr (j3BetaTbl 7)) (natArr (j3Tbl 0)))
    (Pr := fun g => g * tp 6156 (j3BetaTbl 7) = tp 6156 (j3BetaTbl 7) * g ∧
      g * tp 6156 (j3Tbl 0) * (g * tp 6156 (j3Tbl 0)) = 1)
    j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_groups (fun w g hw _ => by
      rw [commSqxW, Bool.and_eq_true, commW_iff hgs hw, sqxW_iff hx hw]
      simp)
  have hcnt : PairJ3.parCount (commSqxW 6156 (natArr (j3BetaTbl 7)) (natArr (j3Tbl 0)))
      PairJ3.blocks = 0 := Certificates.certificate26101.2
  rw [show blocksOf 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups =
    PairJ3.blocks from rfl, ← PairJ3.parCount_eq, hcnt, ← j3P_eq_original] at hcount
  intro d hd h
  have hemp := Nat.card_eq_zero.1 hcount
  rcases hemp with hemp | hinf
  · exact hemp.false ⟨d, hd, h⟩
  · exact (not_infinite_iff_finite.2 inferInstance) hinf

theorem outerBetaFor_j3P
    (hb : tp 6156 (j3BetaTbl 7) ∈ j3P) :
    OuterBetaFor ↥j3P ⟨tp 6156 (j3BetaTbl 7), hb⟩ := by
  obtain ⟨hU2, -, -, hmap, -, -, -, -, hRcard, -⟩ :=
    ctuc_j3_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  have hu : Rep 6156 j3OuterTbl j3u := ctuc_j3_involution_centralizer_data.1 0 (by norm_num)
  have hperm := (betaHomCheck_permOK Certificates.certificate24603.1).2.2
  exact outerBetaFor_of_zOK (R := j3R) j3_groupData hu hU2 hUn rfl he
    (by rw [hRcard, card_j3P]) hperm hb Certificates.certificate26101.1 no_outer_involution

theorem betaDataSqBO_j3P :
    BetaDataSqBO ↥j3P := by
  have hD := j3_groupData
  have hn : 6156 < 2 ^ 32 := by norm_num
  obtain ⟨ht0, hb7, hcomm, hβ⟩ := betaFor_j3P
  obtain ⟨hchk3, hmem3⟩ := Certificates.certificate24603
  obtain ⟨h8p, -, h7p⟩ := betaHomCheck_permOK hchk3
  simp only [j3MemOK, Bool.and_eq_true] at hmem3
  obtain ⟨-, h8c⟩ := hmem3
  obtain ⟨hchk, hmem⟩ := Certificates.certificate24605
  obtain ⟨hap, hbp, htp⟩ := a5HomCheck_permOK hchk
  simp only [j3A5MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hsa, hsb⟩, h67⟩, h08⟩ := hmem
  have haX := (hD.sift _ _ (rep_tp hap)).1 hsa
  have hbX := (hD.sift _ _ (rep_tp hbp)).1 hsb
  obtain ⟨B₀, hBX, hBt, haB, hbB, ⟨eB⟩⟩ :=
    a5_of_check hn (X := j3P) (pg := piA5J3) piA5J3_even hchk haX hbX
  have hrep9 := ctuc_j3_involution_centralizer_data.1 9 (by norm_num)
  have ht08 : tp 6156 (j3BetaTbl 0) = tp 6156 (j3BetaTbl 8) :=
    (tblEq_iff_eq (rep_tp htp) (rep_tp h8p)).1 h08
  have ht89 : tp 6156 (j3BetaTbl 8) = tp 6156 (j3CentTbl 9) :=
    (tblEq_iff_eq (rep_tp h8p) hrep9).1 h8c
  have hb67 : tp 6156 (j3BetaTbl 6) = tp 6156 (j3BetaTbl 7) :=
    (tblEq_iff_eq (rep_tp hbp) (rep_tp h7p)).1 h67
  refine BetaDataSqBO.of_class ⟨tp 6156 (j3CentTbl 9), ht0⟩ ⟨tp 6156 (j3BetaTbl 7), hb7⟩
    (B₀.subgroupOf j3P) (fun t ht2 _ => exists_conj_t0 ht0 t ht2) ?_
    ⟨(subgroupOfEquivOfLe hBX).trans eB⟩ ?_ hβ (outerBetaFor_j3P hb7)
  · intro b hb
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hBt (mem_subgroupOf.1 hb))
    rw [ht08, ht89] at h1
    exact Subtype.ext h1
  · rw [mem_subgroupOf]
    show tp 6156 (j3BetaTbl 7) ∈ B₀
    rw [← hb67]
    exact hbB

theorem outerInvData_j3P :
    OuterInvData ↥j3P := by
  obtain ⟨hP0, -⟩ := HypOne.J3.class_data
  obtain ⟨hU2, -, hUP, hmap, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  have hu : Rep 6156 j3OuterTbl j3u := ctuc_j3_involution_centralizer_data.1 0 (by norm_num)
  have hsqrt := Certificates.certificate26103
  refine OuterInvData.of_model le_sup_left he (mem_sup_right (mem_zpowers j3u)) hUP
    (by rw [← pow_two]; exact hU2) [⟨tp 6156 (j3CentTbl 9), hP0⟩] (fun a ha ha1 => ?_)
    (fun a₀ ha₀ => ?_)
  · have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
    obtain ⟨g, hg⟩ := exists_conj_t0 hP0 a ha2
    exact ⟨g, _, List.mem_cons_self, hg⟩
  · rw [List.mem_singleton] at ha₀
    subst ha₀
    exact sqrtOK_spec j3_groupData hu hU2 hUn (ctuc_j3_involution_centralizer_data.1 9
      (by norm_num)) hsqrt

end CFSG.EvenSporadicStandard.Fin76b.J3
