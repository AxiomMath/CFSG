module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped MatrixGroups Pointwise

section Picture

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)

omit [Finite J] [K.Normal] in
theorem socleAction_trans' {X : Type} [Group X] {T T' : Type*} [Group T] [Group T']
    (θ : GeneralizedFitting.subgroup X ≃* T) (Θ : T ≃* T') (x : X) :
    socleAction (θ.trans Θ) x = MulAut.congr Θ (socleAction θ x) := rfl

omit [Finite J] [K.Normal] in
theorem congr_trans {A B C : Type*} [Group A] [Group B] [Group C] (e₁ : A ≃* B) (e₂ : B ≃* C)
    (f : MulAut A) : MulAut.congr (e₁.trans e₂) f = MulAut.congr e₂ (MulAut.congr e₁ f) := by
  ext x
  rfl

variable (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

end Picture

end CFSG.ComponentClassification.Burgoyne.DX
