module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_10
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F U : Subgroup G}

theorem out12_of_h129 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hu : HU S T U)
    (h127 : After127 G x z S T P Q Rd F) (h129 : 2 < T.relIndex S) (hP4 : IP_P_four P)
    (hf3 : IP_f3 x P) (hzV : IP_z_V z P) (hexp : IP_cent_P_exp T P Q) (hE8 : IP_E8_two T)
    (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hclosed : IP_P_closed x T P) :
    ∃ V : Subgroup G, V ≤ P ∧ Sec13.Out12 G x T V := by
  obtain ⟨V, hVP, hV, hxV, hVn, hsyl, hEc, hT16, ⟨f, hf3', hfC, hfN, hfc⟩, haut⟩ :=
    lemma_12_10 G x S T P Q Rd F U z h hz hu h127 h129 hP4 hf3 hzV hexp hE8 hout hcf hclosed
  have hTns : ¬ Sec13.Sylow2In T ⊤ := by
    intro hT
    have : S = T := sylow2_eq_of_le (P := T) (H := ⊤) hT h.S_pgroup h.T_le_S le_top
    exact h127.T_ne_S this.symm
  exact ⟨V, hVP, ⟨h.simple, h.nonabelian, h.x_sq, h.x_ne_one, h.rank_le, h.T_sylow, hTns,
    hVP.trans h.P_le_T, hV, hxV, hVn, hEc, hT16, hsyl, ⟨f, hf3', hfC, hfN, hfc⟩, haut, h.nonsolv⟩⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
