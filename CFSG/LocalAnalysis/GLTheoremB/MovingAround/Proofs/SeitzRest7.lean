module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311k2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311l
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311i2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest7

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration TauCeti
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniSeitzPlanes)

set_option linter.unusedSectionVars false


@[expose] def OddCpfInnerExc : Prop :=
  UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ InnerPlane d p E ∧ ¬ IsTrialityIndex d.1

@[expose] def SeitzThm4Rest9 : Prop :=
  Inputs2311k.D4PlanesRest ∧ OddCpfInnerExc

theorem seitzThm4Rest8_of_rest9 (h : SeitzThm4Rest9) : SeitzRest6.SeitzThm4Rest8 :=
  Inputs2311c.UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
      by_cases hc : ¬ InnerPlane d p E ∨ IsTrialityIndex d.1
      · exact Or.inl ⟨hE, hc⟩
      · push Not at hc
        exact Or.inr ⟨hE, hc.1, hc.2⟩)
    (Inputs2311k.uniSeitzPlanes_oddCpfRest4_d4Families_of_rest h.1) h.2

@[expose] def Input23_11TwoRestExc : Prop :=
  UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
    InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
    ((∃ q : PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 3) ∨
      (∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : PrimePower, d.1 = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
        orderOf ((q.card : ℕ) : ZMod p) = 6)) ∨
      (∃ q : PrimePower, d.1 = .twistedE6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6))

theorem input23_11TwoRest4_of_exc (h : Input23_11TwoRestExc) : Inputs2311i.Input23_11TwoRest4 := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  rcases h6 with h6 | h6 | h6 | h6 | ⟨q, hq, h7⟩ | hR
  · exact h d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, Or.inl h6⟩
  · exact h d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, Or.inr (Or.inl h6)⟩
  · exact h d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, Or.inr (Or.inr (Or.inl h6))⟩
  · exact h d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, Or.inr (Or.inr (Or.inr h6))⟩
  · exact Inputs2311k.uniSeitzPlanes_twoRest4_triality d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, q, hq, h7⟩
  · exact Inputs2311l.uniSeitzPlanes_reeF4_rest4 d p hp hp2 hpd hex E hE hc ⟨h1, h2, h3, h4, h5, hR⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest7

end
