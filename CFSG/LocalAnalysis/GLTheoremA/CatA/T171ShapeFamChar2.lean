module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2Ambig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBCD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

theorem innerCompNonShape_of_charTwo
    (h1 : InnerCompNonShape fun i => KD264Lie.isLinearIdx i ∧ i.characteristic = 2)
    (h2 : InnerCompNonShape fun i => KD264Lie.isUnitaryIdx i ∧ i.characteristic = 2)
    (h3 : InnerCompNonShape fun i => KD264Lie.isClassicalBCDIdx i ∧ i.characteristic = 2)
    (h4 : InnerCompNonShape fun i => KD264Lie.isTrialityIdx i ∧ i.characteristic = 2)
    (h5 : InnerCompNonShape fun i => KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2)
    (h6 : InnerCompNonShape fun i => KD264Lie.isExcTwistedIdx i ∧ i.characteristic = 2) :
    InnerCompNonShape fun _ => True := by
  intro G _ _ p L J A d b hS _ hshape hin
  rcases hS.chev2 with hon | hamb
  · obtain ⟨i, hi, ⟨e⟩⟩ := hon
    cases i with
    | lie dd =>
      obtain ⟨idx, hv⟩ := dd
      cases idx with
      | A n q =>
        exact h1 p L J A d b hS ⟨.lie ⟨.A n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | twistedA n q =>
        exact h2 p L J A d b hS ⟨.lie ⟨.twistedA n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | B n q =>
        exact h3 p L J A d b hS ⟨.lie ⟨.B n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | C n q =>
        exact h3 p L J A d b hS ⟨.lie ⟨.C n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | D n q =>
        exact h3 p L J A d b hS ⟨.lie ⟨.D n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | twistedD n q =>
        exact h3 p L J A d b hS ⟨.lie ⟨.twistedD n q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | E6 q =>
        exact h5 p L J A d b hS ⟨.lie ⟨.E6 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | E7 q =>
        exact h5 p L J A d b hS ⟨.lie ⟨.E7 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | E8 q =>
        exact h5 p L J A d b hS ⟨.lie ⟨.E8 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | F4 q =>
        exact h5 p L J A d b hS ⟨.lie ⟨.F4 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | G2 q =>
        exact h5 p L J A d b hS ⟨.lie ⟨.G2 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | twistedE6 q =>
        exact h6 p L J A d b hS ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | trialityD4 q =>
        exact h4 p L J A d b hS ⟨.lie ⟨.trialityD4 q, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | suzuki k =>
        exact h6 p L J A d b hS ⟨.lie ⟨.suzuki k, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | reeG2 k =>
        exact h6 p L J A d b hS ⟨.lie ⟨.reeG2 k, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | reeF4 k =>
        exact h6 p L J A d b hS ⟨.lie ⟨.reeF4 k, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
      | tits =>
        exact h6 p L J A d b hS ⟨.lie ⟨.tits, hv⟩, ⟨trivial, hi⟩, ⟨e⟩⟩ hshape hin
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
  · exact (setup_ambiguousChev_false hS hamb).elim

theorem shape15On_of_charTwo
    (h1 : InnerCompNonShape fun i => KD264Lie.isLinearIdx i ∧ i.characteristic = 2)
    (h2 : InnerCompNonShape fun i => KD264Lie.isUnitaryIdx i ∧ i.characteristic = 2)
    (h3 : InnerCompNonShape fun i => KD264Lie.isClassicalBCDIdx i ∧ i.characteristic = 2)
    (h4 : InnerCompNonShape fun i => KD264Lie.isTrialityIdx i ∧ i.characteristic = 2)
    (h5 : InnerCompNonShape fun i => KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2)
    (h6 : InnerCompNonShape fun i => KD264Lie.isExcTwistedIdx i ∧ i.characteristic = 2) :
    Shape15On fun _ => True :=
  shape15On_of_residuals (innerDiagInnerOrShape_holds fun _ => True)
    (innerCompNonShape_of_charTwo h1 h2 h3 h4 h5 h6)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
