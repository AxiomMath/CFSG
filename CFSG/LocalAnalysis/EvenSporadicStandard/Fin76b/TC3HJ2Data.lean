module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HModel
public import Certificates.Certificate26100
public import Certificates.Certificate26102
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import Certificates.Certificate24604

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.Fin76b.TC3H
open CFSG.EvenSporadicStandard.HypOne (zOK)

theorem no_outer_involution :
    ∀ d : ↥j2P, (d : Equiv.Perm (Fin 315)) * tp 315 (j2BetaTbl 7) =
        tp 315 (j2BetaTbl 7) * d →
      (d : Equiv.Perm (Fin 315)) * tp 315 (j2Tbl 0) *
        ((d : Equiv.Perm (Fin 315)) * tp 315 (j2Tbl 0)) ≠ 1 := by
  classical
  have hperm := (betaHomCheck_permOK Certificates.certificate24601.1).2.2
  have hpermx : permOK 315 (j2Tbl 0) = true := by
    have h := Certificates.certificate26100.1
    simp only [j2OuterOK, zOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 315) [natArr (j2BetaTbl 7)]
      [tp 315 (j2BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hx : CFSG.Monster.B.Co2.Rep 315 (natArr (j2Tbl 0)) (tp 315 (j2Tbl 0)) :=
    co2Rep_natArr_iff.2 (rep_tp hpermx)
  have hcount := card_eq_countW (f := commSqxW 315 (natArr (j2BetaTbl 7)) (natArr (j2Tbl 0)))
    (Pr := fun g => g * tp 315 (j2BetaTbl 7) = tp 315 (j2BetaTbl 7) * g ∧
      g * tp 315 (j2Tbl 0) * (g * tp 315 (j2Tbl 0)) = 1)
    j2ChainArrays (by norm_num) PairJ2.chain_check.1 j2_groups (fun w g hw _ => by
      rw [commSqxW, Bool.and_eq_true, commW_iff hgs hw, sqxW_iff hx hw]
      simp)
  have hcnt : countW (commSqxW 315 (natArr (j2BetaTbl 7)) (natArr (j2Tbl 0))) PairJ2.blocks [] =
      0 := Certificates.certificate26100.2
  rw [show blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr) PairJ2.groups =
    PairJ2.blocks from rfl, hcnt, ← j2P_eq_original] at hcount
  intro d hd h
  have hemp := Nat.card_eq_zero.1 hcount
  rcases hemp with hemp | hinf
  · exact hemp.false ⟨d, hd, h⟩
  · exact (not_infinite_iff_finite.2 inferInstance) hinf

theorem outerBetaFor_j2P
    (hb : tp 315 (j2BetaTbl 7) ∈ j2P) :
    OuterBetaFor ↥j2P ⟨tp 315 (j2BetaTbl 7), hb⟩ := by
  obtain ⟨hU2, -, -, hmap, -, -, -, -, hRcard, -⟩ :=
    ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  have hu : Rep 315 j2OuterTbl j2u := ctuc_j2_involution_centralizer_data.1 0 (by norm_num)
  have hperm := (betaHomCheck_permOK Certificates.certificate24601.1).2.2
  exact outerBetaFor_of_zOK (R := j2R) j2_groupData hu hU2 hUn rfl he
    (by rw [hRcard, card_j2P]) hperm hb Certificates.certificate26100.1 no_outer_involution

theorem betaDataSqBO_j2P :
    BetaDataSqBO ↥j2P := by
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
  refine BetaDataSqBO.of_class ⟨tp 315 (j2CentTbl 31), ht0⟩ ⟨tp 315 (j2BetaTbl 7), hb7⟩
    (B₀.subgroupOf j2P) (fun t ht2 hs => exists_conj_t0 ht0 t ht2 hs) ?_
    ⟨(subgroupOfEquivOfLe hBX).trans eB⟩ ?_ hβ (outerBetaFor_j2P hb7)
  · intro b hb
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hBt (mem_subgroupOf.1 hb))
    rw [ht08, ht89] at h1
    exact Subtype.ext h1
  · rw [mem_subgroupOf]
    show tp 315 (j2BetaTbl 7) ∈ B₀
    rw [← hb67]
    exact hbB

theorem involution_cover :
    tp 315 (j2CentTbl 31) ∈ j2P ∧ tp 315 (j2CentTbl 17) ∈ j2P ∧
      ∀ t ∈ j2P, orderOf t = 2 → ∃ g ∈ j2P,
        t = g * tp 315 (j2CentTbl 31) * g⁻¹ ∨ t = g * tp 315 (j2CentTbl 17) * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨-, -, h1, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨-, -, h2, -⟩ := hrows _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  dsimp only at h1 h2
  have hP17 : tp 315 (j2CentTbl 17) ∈ j2P := by
    by_contra h
    exact Bool.false_ne_true (h1.2 h)
  have hP31 : tp 315 (j2CentTbl 31) ∈ j2P := by
    by_contra h
    exact Bool.false_ne_true (h2.2 h)
  refine ⟨hP31, hP17, fun t ht ht2 => ?_⟩
  obtain ⟨r, hr, g, hg, hv⟩ := hcover t (mem_sup_left ht) ht2
  have hrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) ht) hg
    rwa [show g⁻¹ * t * g = tp 315 r.rep by rw [hv]; group] at this
  have hr0 := hr
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr
  · exfalso
    have hout : r.outer = true := by rw [hr]
    exact (hrows r hr0).2.2.1.1 hout hrP
  · have hrep : r.rep = j2CentTbl 17 := by rw [hr]
    rw [hrep] at hv
    exact ⟨g, hg, Or.inr hv⟩
  · have hrep : r.rep = j2CentTbl 31 := by rw [hr]
    rw [hrep] at hv
    exact ⟨g, hg, Or.inl hv⟩

theorem outerInvData_j2P :
    OuterInvData ↥j2P := by
  obtain ⟨hP31, hP17, hcls⟩ := involution_cover
  obtain ⟨hU2, -, hUP, hmap, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  have hu : Rep 315 j2OuterTbl j2u := ctuc_j2_involution_centralizer_data.1 0 (by norm_num)
  have hsqrt := Certificates.certificate26102
  simp only [j2SqrtOK, Bool.and_eq_true] at hsqrt
  refine OuterInvData.of_model le_sup_left he (mem_sup_right (mem_zpowers j2u)) hUP
    (by rw [← pow_two]; exact hU2) [⟨tp 315 (j2CentTbl 31), hP31⟩, ⟨tp 315 (j2CentTbl 17), hP17⟩]
    (fun a ha ha1 => ?_) (fun a₀ ha₀ => ?_)
  · have ha2 : orderOf (a : Equiv.Perm (Fin 315)) = 2 := by
      refine orderOf_eq_prime ?_ fun h => ha1 (Subtype.ext h)
      rw [pow_two]
      exact congrArg Subtype.val ha
    obtain ⟨g, hg, hv | hv⟩ := hcls a a.2 ha2
    · exact ⟨⟨g, hg⟩, _, List.mem_cons_self, Subtype.ext hv⟩
    · exact ⟨⟨g, hg⟩, _, List.mem_cons_of_mem _ List.mem_cons_self, Subtype.ext hv⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha₀
    rcases ha₀ with rfl | rfl
    · exact sqrtOK_spec j2_groupData hu hU2 hUn (ctuc_j2_involution_centralizer_data.1 31
        (by norm_num)) hsqrt.1
    · exact sqrtOK_spec j2_groupData hu hU2 hUn (ctuc_j2_involution_centralizer_data.1 17
        (by norm_num)) hsqrt.2

end CFSG.EvenSporadicStandard.Fin76b.J2
