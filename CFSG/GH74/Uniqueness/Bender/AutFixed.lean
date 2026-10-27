module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.Uniqueness.Bender

variable {K L : Type*} [Group K] [Group L]

@[expose] def autFixed (α : MulAut K) : Subgroup K where
  carrier := {x | α x = x}
  mul_mem' {x y} hx hy := by
    change α (x * y) = x * y
    rw [map_mul]
    exact congr_arg₂ (· * ·) hx hy
  one_mem' := map_one α
  inv_mem' {x} hx := by
    change α x⁻¹ = x⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) hx

theorem mem_autFixed_iff {α : MulAut K} {x : K} : x ∈ autFixed α ↔ α x = x := Iff.rfl

theorem mem_autFixed_congr_iff (θ : K ≃* L) (α : MulAut K) (y : L) :
    y ∈ autFixed (MulAut.congr θ α) ↔ θ.symm y ∈ autFixed α := by
  rw [mem_autFixed_iff, mem_autFixed_iff]
  change θ (α (θ.symm y)) = y ↔ _
  constructor
  · intro h
    apply θ.injective
    rw [h, MulEquiv.apply_symm_apply]
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

@[expose] def autFixedEquiv (θ : K ≃* L) (α : MulAut K) :
    autFixed α ≃* autFixed (MulAut.congr θ α) where
  toFun x := ⟨θ x, (mem_autFixed_congr_iff θ α _).mpr (by
    rw [MulEquiv.symm_apply_apply]; exact x.2)⟩
  invFun y := ⟨θ.symm y, (mem_autFixed_congr_iff θ α _).mp y.2⟩
  left_inv x := Subtype.ext (θ.symm_apply_apply _)
  right_inv y := Subtype.ext (θ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul θ _ _)

theorem mulAut_congr_sq_eq_one (θ : K ≃* L) {α : MulAut K} (hα : α * α = 1) :
    MulAut.congr θ α * MulAut.congr θ α = 1 := by
  rw [← map_mul, hα, map_one]

theorem not_inner_congr (θ : K ≃* L) {α : MulAut K}
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    ¬ ∃ g : L, ∀ x : L, MulAut.congr θ α x = g * x * g⁻¹ := by
  rintro ⟨g, hg⟩
  apply hout
  refine ⟨θ.symm g, fun x => ?_⟩
  have h1 := hg (θ x)
  change θ (α (θ.symm (θ x))) = g * θ x * g⁻¹ at h1
  rw [MulEquiv.symm_apply_apply] at h1
  apply θ.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.GH74.Uniqueness.Bender
