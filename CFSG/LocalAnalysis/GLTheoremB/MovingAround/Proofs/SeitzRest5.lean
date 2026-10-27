module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311g2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge7

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.LieType.Seitz

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest7 : Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311g.OddCpfRest4 ∧ Inputs256i.QGen3ExcInndiagF3 ∧
    Inputs256i.QGen3TwE6InndiagF3 ∧ Inputs256i.QGen3TriD4InnerF3

theorem seitzThm4Rest6_of_rest7 (h : SeitzThm4Rest7) : SeitzRest4.SeitzThm4Rest6 :=
  ⟨Inputs2311g.uniSeitzPlanes_oddCpfRest3_of_rest4 h.1, h.2⟩

@[expose] def TwE6ThreeOpenDiagEven : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => (p = 3 ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2) ∧
    ¬ InnerPlane d p E ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      ∃ e : Cat d ≃* twistedE6RootGroup K σ,
        E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) ∧
    ¬ Inputs2311d.IsTwE6DiagParabolicPlane d E) ∧ d.1.characteristic = 2

theorem twE6ThreeOpenDiag_of_even (h : TwE6ThreeOpenDiagEven) : QuasiHigh5E6Cover.TwE6ThreeOpenDiag := by
  unfold QuasiHigh5E6Cover.TwE6ThreeOpenDiag
  exact Inputs2311c.UniSeitzPlanes.of_cover
    (fun d _ _ _ _ hs => (em (d.1.characteristic = 2)).elim (fun h2 => Or.inr ⟨hs, h2⟩) (fun h2 => Or.inl ⟨hs, h2⟩))
    Inputs2311g.uniSeitzPlanes_twE6ThreeOpenDiag_odd h

@[expose] def SeitzLowRest11 : Prop :=
  TwE6ThreeOpenDiagEven ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual13 ∧ ChevQ.SeitzE6ThreeConn

theorem seitzLowRest10_of_rest11 (h : SeitzLowRest11) : SeitzYS09Bridge7.SeitzLowRest10 :=
  ⟨twE6ThreeOpenDiag_of_even h.1, h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5

end
