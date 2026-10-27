module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GroupTheory

open scoped IsMulCommutative
open CFSG.OrderReductions.FrattiniAutomorphisms

def mulAutLinearHom (Q : Type*) [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)] : MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) where
  toFun σ := AddEquiv.toLinearEquiv (MulEquiv.toAdditive σ)
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive σ) c x)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem mulAutLinearHom_injective (Q : Type*) [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)] : Function.Injective (mulAutLinearHom Q) := by
  intro σ τ h
  ext y
  exact DFunLike.congr_fun h (Additive.ofMul y)

@[simp] theorem mulAutLinearHom_apply (Q : Type*) [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)] (σ : MulAut Q) (x : Additive Q) :
    mulAutLinearHom Q σ x = Additive.ofMul (σ x.toMul) := (rfl)

end CFSG.GroupTheory
