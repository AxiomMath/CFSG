module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3
public import CFSG.Sporadic.SmallOddCore.J2CentralizerD
public import Certificates.Certificate24602
public import Certificates.Certificate24603

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta

theorem card_centralizer_beta :
    Nat.card ↥(j3P ⊓ centralizer ({tp 6156 (j3BetaTbl 7)} : Set (Equiv.Perm (Fin 6156)))) =
      1080 := by
  classical
  have hperm := (betaHomCheck_permOK Certificates.certificate24603.1).2.2
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 6156) [natArr (j3BetaTbl 7)]
      [tp 6156 (j3BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hcount := card_eq_countW (f := commW 6156 [natArr (j3BetaTbl 7)])
    (Pr := fun g => ∀ d ∈ [tp 6156 (j3BetaTbl 7)], g * d = d * g) j3ChainArrays (by norm_num)
    PairJ3.chain_check.1 j3_groups (fun w g hw _ => commW_iff hgs hw)
  have hcnt : PairJ3.parCount (commW 6156 [natArr (j3BetaTbl 7)]) PairJ3.blocks = 1080 :=
    Certificates.certificate24602
  rw [show blocksOf 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups =
    PairJ3.blocks from rfl, ← PairJ3.parCount_eq, hcnt, ← j3P_eq_original] at hcount
  rw [← hcount]
  refine Nat.card_congr ⟨fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, ?_⟩,
    fun x => ⟨x.1.1, mem_inf.mpr ⟨x.1.2, ?_⟩⟩, fun _ => rfl, fun _ => rfl⟩
  · intro d hd
    rw [List.mem_singleton.1 hd]
    exact mem_centralizer_singleton_iff.1 (mem_inf.mp x.2).2
  · exact mem_centralizer_singleton_iff.2 (x.2 _ (List.mem_singleton_self _))

theorem betaFor_j3P :
    ∃ (ht : tp 6156 (j3CentTbl 9) ∈ j3P) (hb : tp 6156 (j3BetaTbl 7) ∈ j3P),
      (⟨tp 6156 (j3CentTbl 9), ht⟩ : ↥j3P) * ⟨tp 6156 (j3BetaTbl 7), hb⟩ =
        ⟨tp 6156 (j3BetaTbl 7), hb⟩ * ⟨tp 6156 (j3CentTbl 9), ht⟩ ∧
        BetaFor ↥j3P ⟨tp 6156 (j3BetaTbl 7), hb⟩ := by
  have hD := j3_groupData
  have hn : 6156 < 2 ^ 32 := by norm_num
  obtain ⟨hchk, hmem⟩ := Certificates.certificate24603
  obtain ⟨ht, hd, hb⟩ := betaHomCheck_permOK hchk
  simp only [j3MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hs8, hs9⟩, hs7⟩, heq⟩ := hmem
  have htX := (hD.sift _ _ (rep_tp ht)).1 hs8
  have hdX := (hD.sift _ _ (rep_tp hd)).1 hs9
  have hbX := (hD.sift _ _ (rep_tp hb)).1 hs7
  obtain ⟨hcomm, hβ⟩ := betaFor_of_check hn (X := j3P) (pg := piGens) piGens_even hchk htX hdX hbX
    card_centralizer_beta
  have hrep := ctuc_j3_involution_centralizer_data.1 9 (by norm_num)
  have htt : tp 6156 (j3BetaTbl 8) = tp 6156 (j3CentTbl 9) :=
    (tblEq_iff_eq (rep_tp ht) hrep).1 heq
  rw [← htt]
  exact ⟨htX, hbX, Subtype.ext hcomm, hβ⟩

theorem exists_conj_t0
    (ht0 : tp 6156 (j3CentTbl 9) ∈ j3P) :
    ∀ t : ↥j3P, orderOf t = 2 → ∃ g : ↥j3P, t = g * ⟨tp 6156 (j3CentTbl 9), ht0⟩ * g⁻¹ := by
  intro t ht2
  obtain ⟨hP0, -, -, -, hP1, -, -, hcls⟩ := HypOne.J3.class_data
  obtain ⟨g, hg, hv | hv⟩ := hcls (t : Equiv.Perm (Fin 6156)) (mem_sup_left t.2) (by
    rw [Subgroup.orderOf_coe]; exact ht2)
  · exact ⟨⟨g, hg⟩, Subtype.ext hv⟩
  · exfalso
    apply hP1
    have : tp 6156 HypOne.J3.t1 = g⁻¹ * (t : Equiv.Perm (Fin 6156)) * g := by rw [hv]; group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) t.2) hg

end CFSG.EvenSporadicStandard.Fin76b.J3
