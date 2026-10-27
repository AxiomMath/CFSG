module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup

variable {G : Type} [Group G]

structure PairData (S P₁ P₂ : Subgroup G) (z t : G) (a : ℕ) : Prop where
  z_mem : z ∈ S
  z_ord : orderOf z = 2
  z_cent : ∀ s ∈ S, s * z = z * s
  P₁_le : P₁ ≤ S
  P₂_le : P₂ ≤ S
  P₁_quat : IVK.IsQuaternionTwoGroup ↥P₁ a
  P₂_quat : IVK.IsQuaternionTwoGroup ↥P₂ a
  inter : P₁ ⊓ P₂ = zpowers z
  comm : ∀ p ∈ P₁, ∀ q ∈ P₂, p * q = q * p
  t_mem : t ∈ S
  t_inv : t * t = 1
  t_not : t ∉ P₁ ⊔ P₂
  swap : ∀ p ∈ P₁, t * p * t⁻¹ ∈ P₂

namespace PairData

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

theorem toData (h : PairData S P₁ P₂ z t a) (idx : (P₁ ⊔ P₂).relIndex S = 2) :
    Data S P₁ P₂ z t a :=
  ⟨h.z_mem, h.z_ord, h.z_cent, h.P₁_le, h.P₂_le, h.P₁_quat, h.P₂_quat, h.inter, h.comm, h.t_mem,
    h.t_inv, h.t_not, idx, h.swap⟩

end PairData

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
