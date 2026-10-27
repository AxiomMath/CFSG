module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import Certificates.Certificate24605
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta

theorem betaDataSqB_j3P :
    BetaDataSqB ↥j3P := by
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
  refine BetaDataSqB.of_class ⟨tp 6156 (j3CentTbl 9), ht0⟩ ⟨tp 6156 (j3BetaTbl 7), hb7⟩
    (B₀.subgroupOf j3P) (fun t ht2 _ => exists_conj_t0 ht0 t ht2) ?_
    ⟨(subgroupOfEquivOfLe hBX).trans eB⟩ ?_ hβ
  · intro b hb
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hBt (mem_subgroupOf.1 hb))
    rw [ht08, ht89] at h1
    exact Subtype.ext h1
  · rw [mem_subgroupOf]
    show tp 6156 (j3BetaTbl 7) ∈ B₀
    rw [← hb67]
    exact hbB

end CFSG.EvenSporadicStandard.Fin76b.J3
