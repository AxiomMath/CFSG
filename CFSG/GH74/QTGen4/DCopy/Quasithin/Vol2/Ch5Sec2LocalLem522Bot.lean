module

public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotS331
public import CFSG.Quasithin.EmptyFaithful.S1422Setting
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

theorem stmt5_2_2_bot_of_F4 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) (hLie : Stmt5_2_L2Lie_F4)
    (hDSB : DSBLoc_F4) (hDSC : DSCStatement_F4) (hlist : Stmt5_2_2_bot_list_F4) :
    Stmt5_2_2_bot_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hhyp, hborQ⟩ := hyp.hyp111_F4 hF h311 h510 h331 hR hL2 hLie hO
  obtain ⟨-, -, h3, h5⟩ := hyp.SDp_facts_F4 hF h311 h510 h331 hR hO
  have hqt : IsQuasithinSub (L₂ ⊔ (Dp ⊔ S) ⊔ S) := isQuasithinSub_of_qtke h.qtke _
  have hnorm : (S.subgroupOf (S ⊔ borelOf (Dp ⊔ S) S)).Normal := by
    rw [hborQ, sup_idem, Subgroup.subgroupOf_self]
    infer_instance
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  rcases hyp.p_cases with hp | hp
  · subst hp
    have hS3 := h3 rfl
    obtain ⟨L1', L2', hsw, hcen, hlistB⟩ :=
      dsBLoc_orient_of_F4 hDSB G L₂ (Dp ⊔ S) S hhyp hqt (Or.inr hnorm) hL₂ns hS3
    have hhyp' : Hyp111 L1' L2' S := by
      rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hhyp
      · exact hhyp.symm
    exact hlist G T M L V H B D L₂ Dp n hyp hO hS3 L1' L2' hsw hhyp' hcen hlistB
  · subst hp
    exact hDSC G L₂ (Dp ⊔ S) S hhyp hqt (Or.inr hnorm) hL₂ns (h5 rfl)

end CFSG.Quasithin.H13
