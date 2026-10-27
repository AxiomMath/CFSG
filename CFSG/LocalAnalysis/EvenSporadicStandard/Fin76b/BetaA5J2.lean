module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import Certificates.Certificate24604
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta

theorem betaDataSqB_j2P :
    BetaDataSqB ↥j2P := by
  have hD := j2_groupData
  have hn : 315 < 2 ^ 32 := by norm_num
  obtain ⟨ht0, hb7, hcomm, hβ⟩ := betaFor_j2P
  obtain ⟨hchk3, hmem3⟩ := Certificates.certificate24601
  obtain ⟨h8p, -, h7p⟩ := betaHomCheck_permOK hchk3
  simp only [j2MemOK, Bool.and_eq_true] at hmem3
  obtain ⟨-, h8c⟩ := hmem3
  obtain ⟨hchk, hmem⟩ := Certificates.certificate24604
  obtain ⟨hap, hbp, htp⟩ := a5HomCheck_permOK hchk
  simp only [j2A5MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hsa, hsb⟩, h67⟩, h08⟩ := hmem
  have haX := (hD.sift _ _ (rep_tp hap)).1 hsa
  have hbX := (hD.sift _ _ (rep_tp hbp)).1 hsb
  obtain ⟨B₀, hBX, hBt, haB, hbB, ⟨eB⟩⟩ :=
    a5_of_check hn (X := j2P) (pg := piA5J2) piA5J2_even hchk haX hbX
  have hrep31 := ctuc_j2_involution_centralizer_data.1 31 (by norm_num)
  have ht08 : tp 315 (j2BetaTbl 0) = tp 315 (j2BetaTbl 8) :=
    (tblEq_iff_eq (rep_tp htp) (rep_tp h8p)).1 h08
  have ht89 : tp 315 (j2BetaTbl 8) = tp 315 (j2CentTbl 31) :=
    (tblEq_iff_eq (rep_tp h8p) hrep31).1 h8c
  have hb67 : tp 315 (j2BetaTbl 6) = tp 315 (j2BetaTbl 7) :=
    (tblEq_iff_eq (rep_tp hbp) (rep_tp h7p)).1 h67
  refine BetaDataSqB.of_class ⟨tp 315 (j2CentTbl 31), ht0⟩ ⟨tp 315 (j2BetaTbl 7), hb7⟩
    (B₀.subgroupOf j2P) (fun t ht2 hs => exists_conj_t0 ht0 t ht2 hs) ?_
    ⟨(subgroupOfEquivOfLe hBX).trans eB⟩ ?_ hβ
  · intro b hb
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hBt (mem_subgroupOf.1 hb))
    rw [ht08, ht89] at h1
    exact Subtype.ext h1
  · rw [mem_subgroupOf]
    show tp 315 (j2BetaTbl 7) ∈ B₀
    rw [← hb67]
    exact hbB

end CFSG.EvenSporadicStandard.Fin76b.J2
