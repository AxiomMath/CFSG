module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526S331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Tr

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Hyp5_2_4

variable {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem alpha_eq_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hbor : Stmt5_2_6_borel_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    RankTwoAmalgam.ofSubgroups (L ⊔ bigB L L₂ (sec52S M H)) (L₂ ⊔ bigB L L₂ (sec52S M H)) =
      sec52Alpha M L H B D L₂ := by
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq_F4 h331 hR (hbor G T M L V H B D L₂ n hyp)
  rw [← hG1, ← hG2]

theorem isAmalgamOfGroup_of_orient_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hbor : Stmt5_2_6_borel_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {L1' L2' : Subgroup G}
    (hor : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1' ⊔ bigB L1' L2' (sec52S M H))
      (L2' ⊔ bigB L1' L2' (sec52S M H))) P) :
    IsAmalgamOfGroup (sec52Alpha M L H B D L₂) P := by
  rw [← hyp.alpha_eq_F4 h331 hR hbor]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst L1' L2'
    exact h
  · subst L1' L2'
    rw [bigB_swap] at h
    exact isAmalgamOfGroup_ofSubgroups_swap h

end Hyp5_2_4

end CFSG.Quasithin.H13
