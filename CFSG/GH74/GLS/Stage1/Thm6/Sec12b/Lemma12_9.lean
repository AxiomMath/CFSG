module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9h
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Out

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

theorem lemma_12_9 :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (S T P Q Rd F : Subgroup G) (z : G),
      HBase G x S T P Q Rd F → HZ T P z → After127 G x z S T P Q Rd F → IP_P_four P →
      IP_f3 x P → IP_z_V z P → IP_cent_P_exp T P Q → IP_P_conj x z P → IP_P_trans P Q Rd →
      IP_Rd_dihedral x Rd → IP_Rd_fuse x P Rd → IP_T_normal x z T P Rd →
      IV3_12_8c_sylow x S T P → IG_15_15 → 2 < T.relIndex S := by
  intro G _ _ x S T P Q Rd F z hbase hz h127 hP4 hf3 hzV hexp hconj htrans hdih hfuse hTn hIV3 hIG
  by_contra hnot
  have hne0 : T.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : T.relIndex S ≠ 1 := by
    intro h1
    apply h127.T_ne_S
    exact le_antisymm hbase.T_le_S (Subgroup.relIndex_eq_one.1 h1)
  have hS2 : T.relIndex S = 2 := by omega
  have H : Hyp129 G x z S T P Q Rd F :=
    ⟨hbase, hz, h127, hP4, hf3, hzV, hexp, hconj, htrans, hdih, hfuse, hTn, hIV3, hIG, hS2⟩
  obtain ⟨a, A⟩ := H.ph0
  obtain ⟨V, P₁, F', B⟩ := H.exists_ph1 A
  by_cases hF : F' = Subgroup.zpowers x
  · exact B.case3a H A hF
  · exact B.case3b H A hF

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F U : Subgroup G}

theorem out12_of_after127 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hu : HU S T U)
    (h127 : After127 G x z S T P Q Rd F) (hP4 : IP_P_four P) (hf3 : IP_f3 x P) (hzV : IP_z_V z P)
    (hexp : IP_cent_P_exp T P Q) (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd)
    (hdih : IP_Rd_dihedral x Rd) (hfuse : IP_Rd_fuse x P Rd) (hTn : IP_T_normal x z T P Rd)
    (hIV3 : IV3_12_8c_sylow x S T P) (hIG : IG_15_15) (hE8 : IP_E8_two T)
    (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hclosed : IP_P_closed x T P) :
    ∃ V : Subgroup G, V ≤ P ∧ Sec13.Out12 G x T V :=
  out12_of_h129 h hz hu h127
    (lemma_12_9 G x S T P Q Rd F z h hz h127 hP4 hf3 hzV hexp hconj htrans hdih hfuse hTn hIV3 hIG)
    hP4 hf3 hzV hexp hE8 hout hcf hclosed

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
