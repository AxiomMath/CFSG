module

public import CFSG.LieType.Chevalley.NativeMonomial
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.LieType.Simplicity

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem fam_chevalley_exceptional_finiteness (G : Type) [Group G]
    (t : StatedLieTag) (p f : ℕ) (h : ChevalleyExceptionalModel G t p f) : Finite G := by
  obtain ⟨-, h⟩ := h
  cases t with
  | G2 | F4 | E6 | E7 | E8 =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  | twistedE6 | trialityD4 =>
    obtain ⟨K, _, _, -, σ, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | twistedB2 | twistedG2 | twistedF4
    | Tits => exact h.elim

theorem fam_ree_tits_finiteness (G : Type) [Group G]
    (t : StatedLieTag) (p f : ℕ) (h : ReeTitsModel G t p f) : Finite G := by
  obtain ⟨-, a, -, h⟩ := h
  cases t with
  | twistedG2 | twistedF4 | Tits =>
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | G2 | F4 | E6 | E7 | E8
    | twistedE6 | trialityD4 | twistedB2 => exact h.elim

theorem fam_exceptional_finiteness (G : Type) [Group G]
    (h : ExceptionalRep G) : Finite G := by
  rcases h with ⟨t, p, f, -, h⟩ | ⟨t, p, f, -, h⟩ | ⟨p, f, h⟩
  · exact fam_chevalley_exceptional_finiteness G t p f h
  · exact fam_ree_tits_finiteness G t p f h
  · exact fam_suzuki_finiteness G p f h

end CFSG.LieType.Simplicity
