module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ}

@[expose] def OSurjCore {Q : QuadraticForm K (Fin d → K)}
    (B : Subgroup (MulAut (StatedProj (matrixDerived Q))))
    (t : MulAut (StatedProj (matrixDerived Q))) : Prop :=
  ∀ y ∈ oddCoreIn B t, ∃ g : similarityPairs Q, y = oκ Q g

theorem OSurj.core {Q : QuadraticForm K (Fin d → K)} (h : OSurj Q)
    (B : Subgroup (MulAut (StatedProj (matrixDerived Q))))
    (t : MulAut (StatedProj (matrixDerived Q))) : OSurjCore B t := fun y _ => h y

@[expose] def OSurjX {Q : QuadraticForm K (Fin d → K)} {X : Type} [Group X]
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)) (t : X) : Prop :=
  ∀ x ∈ oddCentralizerCore t, ∃ g : similarityPairs Q, socleAction θ x = oκ Q g

theorem OSurj.surjX {Q : QuadraticForm K (Fin d → K)} (h : OSurj Q) {X : Type} [Group X]
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)) (t : X) :
    OSurjX θ t := fun _ _ => h _

theorem OSurjX.transport {Q Q' : QuadraticForm K (Fin d → K)} {X : Type} [Group X]
    {θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)} {t : X}
    (h : OSurjX θ t) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    OSurjX (θ.trans (oTransport S ν hS)) t := by
  intro x hx
  obtain ⟨g, hg⟩ := h x hx
  refine ⟨transPair S ν hS g, ?_⟩
  change MulAut.congr (oTransport S ν hS) (socleAction θ x) = _
  rw [hg, oTransport_kappa]

theorem OSurjX.core {Q : QuadraticForm K (Fin d → K)} {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    {θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)} {t : X}
    (h : OSurjX θ t) : OSurjCore (socleAction θ).range (socleAction θ t) := by
  intro y hy
  rw [← map_oddCentralizerCore_of_injective (socleAction_injective hsimple hnab θ)] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨g, hg⟩ := h x hx
  exact ⟨g, hg⟩

theorem OSurjCore.of_eq {Q : QuadraticForm K (Fin d → K)}
    {B : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    {t t' : MulAut (StatedProj (matrixDerived Q))} (h : OSurjCore B t) (e : t = t') :
    OSurjCore B t' := e ▸ h

end CFSG.ComponentClassification.Burgoyne.O
