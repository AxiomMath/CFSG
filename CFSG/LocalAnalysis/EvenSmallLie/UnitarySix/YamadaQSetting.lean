module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

@[expose] def conjG (B : Subgroup G) : Subgroup G :=
  B.map (MulAut.conj d.w₂₃₂).toMonoidHom

end Data

structure HypQ (d : Data G) : Prop where
  e_mem_Sig : d.e ∈ d.Sig
  j₀_comm_e : d.j₀ * d.e = d.e * d.j₀
  w₂₃₂_sq : d.w₂₃₂ * d.w₂₃₂ = 1
  w₂₃₂_mem_K₁ : d.w₂₃₂ ∈ d.K₁
  w₂₃₂_comm_e : d.w₂₃₂ * d.e = d.e * d.w₂₃₂
  w₂₃₂_comm_j₀ : d.w₂₃₂ * d.j₀ = d.j₀ * d.w₂₃₂
  w₂₃₂_X₈ : ∀ b ∈ d.X₈, d.w₂₃₂ * b * d.w₂₃₂⁻¹ ∈ d.X₁
  Z₂S_inf : d.Z₂S ⊓ d.conjG d.Z₂S ≤ zpowers d.z
  CA₁e : ∀ a ∈ d.A₁, a * d.e = d.e * a → ∃ x ∈ d.X₁, ∃ b ∈ d.Z₂S, a = x * b
  NZ₂S : ∀ c ∈ d.H, c * d.e = d.e * c → c ∈ normalizer (d.Z₂S : Set G) →
    c ∈ normalizer (d.A₄ : Set G)

structure HypNF (d : Data G) : Prop where
  card_le : ∀ P : Subgroup G,
    P ≤ d.H ⊓ centralizer ({d.e} : Set G) ⊓ normalizer (d.A₄ : Set G) →
    IsPGroup 2 P → Nat.card P ≤ 2 ^ 7

structure Hyp416 (d : Data G) : Prop where
  X₁_le_A₁ : d.X₁ ≤ d.A₁
  A₁_le_conj : d.A₁ ≤ closure {g | ∃ a ∈ d.A₃, ∃ x ∈ d.X₁, g = a * x * a⁻¹}
  A₂_closure : ∀ B : Subgroup G, d.A₄ ≤ B → B ≤ d.A₂ →
    d.K₁ ⊓ d.K₂ ≤ normalizer (B : Set G) → B = d.A₂
  CA₁A₂ : d.A₁ ⊓ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) ≤ d.A₂
  A₁A₂_le_comm : d.A₁ ⊓ d.A₂ ≤ ⁅d.A₁, d.A₂⁆
  card_A₁A₂ : Nat.card (d.A₁ ⊓ d.A₂ : Subgroup G) = 2 ^ 5

end CFSG.EvenSmallLie.UnitarySix.YamadaD
