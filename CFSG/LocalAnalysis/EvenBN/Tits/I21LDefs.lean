module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits

section Vec

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def nu (g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) - LinearMap.id

@[expose] noncomputable def rk (g : V ≃ₗ[ZMod 2] V) : ℕ :=
  finrank (ZMod 2) (LinearMap.range (nu g))

@[expose] def fixSp (g : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V := LinearMap.ker (nu g)

@[expose] def Stable (g : V ≃ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ u ∈ U, g u ∈ U

end Vec

section Hyp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure HypYW {Y : Type*} [Group Y] (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (t u x h : Y) : Prop where
  dim : finrank (ZMod 2) V = 8
  inj : Function.Injective ρ
  sec : SecTwoHyp Y t u
  ord_x : orderOf x = 5
  fix : ∀ v : V, ρ x v = v → v = 0
  tx : t * x = x * t
  ux : u * x * u⁻¹ = x ^ 2 ∨ u * x * u⁻¹ = x ^ 3
  cent : centralizer ({t} : Set Y) = closure {t, u, x}
  fuse : h * t * h⁻¹ = t * u ^ 2

structure HypM {B : Type*} [Group B] (ρ : B →* (V ≃ₗ[ZMod 2] V)) (x t z h : B) : Prop where
  dim : finrank (ZMod 2) V = 8
  ord_x : orderOf (ρ x) = 5
  fix : ∀ v : V, ρ x v = v → v = 0
  t_sq : ρ t * ρ t = 1
  tx : t * x = x * t
  zx : z * x * z⁻¹ = x⁻¹
  ht : h * t * h⁻¹ = t * z

end Hyp

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
