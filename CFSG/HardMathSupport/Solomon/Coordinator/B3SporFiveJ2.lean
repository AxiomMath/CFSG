module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.PartOne.KS.J2
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore


theorem gLAPPrimeCoreOf_j2FiveC_eq_bot (i : Fin 6) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) ⊓ j2R) =
      ⊥ := by
  obtain ⟨⟨hCeq, hQC, hQeq, -⟩, hgood, hbad⟩ := j2Five_record i
  rw [inf_comm, ← hCeq]
  by_cases hg : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
  · obtain ⟨-, hnorm⟩ := hgood hg
    refine gLAPPrimeCoreOf_eq_bot_of_pConstrained Nat.prime_five hQC
      (fun g hg q hq => Subgroup.mem_subgroupOf.1
        (hnorm.conj_mem ⟨q, hQC hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨g, hg⟩))
      j2FiveQ_isPGroup ?_
    rw [inf_comm, hQeq]
  · have hbad' : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
      have := i.2
      omega
    obtain ⟨-, hDC, -, hDn, hDs, hnonab, hDcard, hcent⟩ := hbad hbad'
    have hDq : CFSG.Open.IsQuasisimple ↥(j2FiveD i) := by
      have := hDs
      obtain ⟨g, hg, h, hh, hne⟩ := hnonab
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
        (isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩)
    refine gLAPPrimeCoreOf_eq_bot_of_isQuasisimple Nat.prime_five hDC
      (fun g hg d hd => Subgroup.mem_subgroupOf.1
        (hDn.conj_mem ⟨d, hDC hd⟩ (Subgroup.mem_subgroupOf.2 hd) ⟨g, hg⟩)) hDq
      (by rw [hDcard]; norm_num) ?_
    rw [inf_comm, hcent]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_j2FiveLine, pow_one])

theorem b3Phi_five_j2P :
    ∀ y ∈ j2P, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 315))) ⊓ j2P) := by
  obtain ⟨⟨hQP, -, -, hQcard, -⟩, ⟨hlines, -⟩, -⟩ := R3E_J2_full_five_centralizer_structure
  have hM := j2_autModel
  refine b3Phi_of_lines Nat.prime_five hQP
    (by rw [hQcard, factorization_card_j2P_five]; norm_num) j2FiveLine ?_ fun i => ?_
  · intro H hHQ hHc
    have hmem : H ∈ {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} :=
      ⟨hHQ, hHc⟩
    rw [hlines] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  · exact b3Phi_of_oPrime (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le
      hM.conj_mem (gLAPPrimeCoreOf_j2FiveC_eq_bot i))

theorem b3SporPair_J2_five (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .J2 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥j2P
    ⟨j2PermEquiv.symm.trans (hbr .J2).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five j2P b3Phi_five_j2P)

end CFSG.HardMathSupport.Solomon.Coordinator
