module

public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem fam_chevalley_exceptional_simplicity
    (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ)
    (h : ChevalleyExceptionalModel G t p f) : Nontrivial G ∧ IsSimpleGroup G := by
  cases t with
  | G2 => exact fam_g2_simplicity G p f h
  | F4 => exact fam_f4_simplicity G p f h
  | E6 => exact fam_e6_simplicity G p f h
  | E7 => exact fam_e7_simplicity G p f h
  | E8 => exact fam_e8_simplicity G p f h
  | twistedE6 => exact fam_2e6_simplicity G p f h
  | trialityD4 => exact fam_3d4_simplicity G p f h
  | _ => exact h.2.elim

theorem fam_exceptional_converse
    (G : Type) [Group G] (h : ExceptionalRep G) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  refine ⟨fam_exceptional_finiteness G h, ?_⟩
  rcases h with ⟨t, p, f, -, h⟩ | ⟨t, p, f, -, h⟩ | ⟨p, f, h⟩
  · exact fam_chevalley_exceptional_simplicity G t p f h
  · exact fam_ree_tits_simplicity G t p f h
  · exact fam_2b2_simplicity G p f h

end CFSG.LieType.Simplicity
