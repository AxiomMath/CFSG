module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.Native.Fi22FiveCentralizers
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Monster.B.Fischer


theorem gLAPPrimeCoreOf_fi22FiveLine_eq_bot (i : Fin 6) :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({fi22FiveLine i} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P) = ⊥ := by
  obtain ⟨-, -, -, hrec⟩ := R3E_Fi22_full_five_centralizers_common_outer_involution
  obtain ⟨-, -, hCP, -, hDP, hDs, hDnab, hDcard, -, -, -, -, -, hcentP⟩ := hrec i
  have hDC : fi22FiveD i ≤ fi22FiveC i := commutator_self_le' _
  rw [← hCP]
  refine gLAPPrimeCoreOf_eq_bot_of_isQuasisimple Nat.prime_five (le_inf hDC hDP)
    (fun g hg d hd => commutator_self_conj_mem (Subgroup.mem_inf.1 hg).1 hd)
    (isQuasisimple_of_simple_subgroup hDs hDnab) (by rw [hDcard]; norm_num) ?_
  rw [inf_comm, hcentP]
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_fi22FiveLine, pow_one])

theorem b3Phi_five_fi22P :
    ∀ y ∈ fi22P, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 3510))) ⊓ fi22P) := by
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) fi22FiveLine
    (lines_of_eq hlines) fun i => b3Phi_of_oPrime (gLAPPrimeCoreOf_fi22FiveLine_eq_bot i)

theorem b3SporPair_Fi22_five
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : B3SporPair .Fi22 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥fi22P
    ⟨fi22PermEquiv.symm.trans (hbr .Fi22).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five fi22P b3Phi_five_fi22P)

end CFSG.HardMathSupport.Solomon.Coordinator
