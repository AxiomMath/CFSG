module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.Sec12b
  CFSG.GH74.GLS.Stage1.Thm6.Glue

variable {G : Type} [Group G] [Finite G] {x : G} {S T P Q Rd F U : Subgroup G}

theorem out12_of_kfacts (hZ : IG_15_3) (hBur : IG_16_2) (hThomp : IG_15_15)
    (hk : KFacts x S T P Q Rd F U) (hIV3 : IV3_12_8c_sylow x S T P)
    (hnonab : ¬ (IsElemAb2 S ∧ Nat.card S = 8)) :
    ∃ V : Subgroup G, V ≤ P ∧ Sec13.Out12 G x T V := by
  obtain ⟨z, hz⟩ := hk.base.exists_HZ hk.P_four
  by_cases hTS : T = S
  · exact (hnonab (lemma_12_7 hZ hBur hThomp hk.base hz hk.outer hk.cent_four hk.P_four
      hk.Rd_factor (hk.P_conj z hz) hk.P_trans hk.cent_Rd hk.cent_P_exp hk.Rd_cyclic hTS)).elim
  · have h127 := after_12_7 hZ hBur hk.base hz hk.outer hk.cent_four hk.P_four hk.Rd_factor
      (hk.P_conj z hz) hk.P_trans hk.cent_Rd hk.cent_P_exp hTS
    exact out12_of_after127 hk.base hz hk.hu h127 hk.P_four hk.f3 (hk.z_V z hz) hk.cent_P_exp
      (hk.P_conj z hz) hk.P_trans (hk.Rd_dihedral h127.Q_eq) (hk.Rd_fuse h127.Q_eq)
      (hk.T_normal z hz h127.Q_eq h127.omega1_le) hIV3 hThomp
      (hk.E8_two h127.Q_eq h127.omega1_le) hk.outer hk.cent_four hk.P_closed

end CFSG.GH74.GLS.Stage1.Thm6
