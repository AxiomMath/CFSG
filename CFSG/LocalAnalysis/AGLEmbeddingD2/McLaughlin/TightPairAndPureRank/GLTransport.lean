module

public import CFSG.Quasithin.Background.G11Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Quasithin.G11

class ExpTwo (V : Type*) [Group V] : Prop where
  mul_self : ∀ v : V, v * v = 1

variable {V : Type} [CommGroup V] [ExpTwo V]

instance instModuleAdditive : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact (ExpTwo.mul_self (Additive.toMul x) : Additive.toMul x * Additive.toMul x = 1))

@[expose] noncomputable def toGLEquiv (φ : MulAut V) : GLV (Additive V) :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive (φ : V ≃* V)) (fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive (φ : V ≃* V)).toAddMonoidHom c x)

@[expose] noncomputable def toGL : MulAut V →* GLV (Additive V) where
  toFun := toGLEquiv
  map_one' := by
    ext x
    rfl
  map_mul' := fun a b => by
    ext x
    rfl

theorem toGL_apply (φ : MulAut V) (v : V) :
    toGL φ (Additive.ofMul v) = Additive.ofMul (φ v) := rfl

theorem toGL_injective : Function.Injective (toGL : MulAut V →* GLV (Additive V)) := by
  intro a b h
  ext v
  have := congrArg (fun f : GLV (Additive V) => f (Additive.ofMul v)) h
  exact Additive.ofMul.injective this

@[expose] noncomputable def toSubmodule (W : Subgroup V) : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup W)

theorem mem_toSubmodule_iff_toMul {W : Subgroup V} {a : Additive V} :
    a ∈ toSubmodule W ↔ Additive.toMul a ∈ W := Iff.rfl

theorem mem_toSubmodule {W : Subgroup V} {v : V} :
    Additive.ofMul v ∈ toSubmodule W ↔ v ∈ W := Iff.rfl

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
