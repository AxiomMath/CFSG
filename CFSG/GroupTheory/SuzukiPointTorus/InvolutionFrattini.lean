module

public import CFSG.GroupTheory.SuzukiPointTorus.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.GroupTheory

open scoped SuzukiTorusData

universe u
variable {X : Type u} [Group X] [Finite X]

namespace SuzukiTorusData

variable {q : ℕ} (h : SuzukiTorusData X q)

abbrev FrattiniV (U : Sylow 2 X) :=
  Additive (↥(U : Subgroup X) ⧸ frattini ↥(U : Subgroup X))

scoped instance frattiniVFact (U : Sylow 2 X) : Fact (IsPGroup 2 (U : Subgroup X)) :=
  ⟨Sylow.isPGroup' U⟩

scoped instance frattiniVElementary (U : Sylow 2 X) :
    IsElementaryAbelian 2 (↥(U : Subgroup X) ⧸ frattini ↥(U : Subgroup X)) :=
  isElementaryAbelian_quotient_frattini

scoped instance frattiniVCommGroup (U : Sylow 2 X) :
    CommGroup (↥(U : Subgroup X) ⧸ frattini ↥(U : Subgroup X)) :=
  IsMulCommutative.instCommGroup

@[expose] noncomputable def frattiniLinAct (U : Sylow 2 X) :
    Subgroup.normalizer ((U : Subgroup X) : Set X) →*
      (FrattiniV U ≃ₗ[ZMod 2] FrattiniV U) :=
  let qAct : Subgroup.normalizer ((U : Subgroup X) : Set X) →*
      MulAut (↥(U : Subgroup X) ⧸ frattini ↥(U : Subgroup X)) :=
    (CFSG.Walter.Huppert.frattiniAut ↥(U : Subgroup X)).comp
      ((U : Subgroup X).normalizerMonoidHom)
  { toFun := fun n =>
      (MulEquiv.toAdditive (qAct n)).toLinearEquiv (ZMod.map_smul _)
    map_one' := by
      apply LinearEquiv.ext
      intro x
      change Additive.ofMul (qAct 1 (Additive.toMul x)) = x
      rw [map_one]
      rfl
    map_mul' := fun n m => by
      apply LinearEquiv.ext
      intro x
      change Additive.ofMul (qAct (n * m) (Additive.toMul x)) =
        Additive.ofMul (qAct n (Additive.toMul (Additive.ofMul (qAct m (Additive.toMul x)))))
      rw [map_mul]
      rfl }

scoped instance torusAction (U₁ U₂ : Sylow 2 X) :
    MulDistribMulAction (SuzukiTorusData.torus U₁ U₂) ↥(U₁ : Subgroup X) :=
  MulDistribMulAction.compHom
    (M := ↥(Subgroup.normalizer ((U₁ : Subgroup X) : Set X)))
    (A := ↥(U₁ : Subgroup X))
    (Subgroup.inclusion (SuzukiTorusData.torus_le_normalizer_left))

end SuzukiTorusData

end CFSG.GroupTheory
