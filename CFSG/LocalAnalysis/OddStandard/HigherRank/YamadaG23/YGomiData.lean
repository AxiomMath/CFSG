module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Gomi6Data (A V C₀ C₁ : Subgroup G) (t u : G) : Prop where
  t_order : orderOf t = 2
  u_order : orderOf u = 4
  V_eq : V = zpowers u
  t_inv : t * u * t⁻¹ = u⁻¹
  C0_eq : C₀ = V ⊔ zpowers t
  C1_eq : C₁ = A ⊔ C₀
  A_card : Nat.card ↥A = 32
  A_comm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ zpowers (u ^ 2)
  A_sq : ∀ a ∈ A, a ^ 2 ∈ zpowers (u ^ 2)
  A_nonab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a
  sq_mem : u ^ 2 ∈ A
  A_inf_C0 : A ⊓ C₀ ≤ zpowers (u ^ 2)
  V_cent_A : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a
  t_cent_A : ∀ a ∈ A, a * t = t * a
  N_C0_le : normalizer (C₀ : Set G) ≤ normalizer (C₁ : Set G)
  N_C1_le : normalizer (C₁ : Set G) ≤ normalizer ((A ⊔ V : Subgroup G) : Set G)
  N_AV_le : normalizer ((A ⊔ V : Subgroup G) : Set G) ≤ normalizer (V : Set G)
  four1 : IsQuotIso (normalizer ((A ⊔ V : Subgroup G) : Set G)) (centralizerSection (A ⊔ V) V)
    (Equiv.Perm (Fin 6))
  four2a : IsSylowIn 2 (centralizerSection (A ⊔ V) V) C₁
  four2b : normalizer ((A ⊔ V : Subgroup G) : Set G) =
    normalizer (C₁ : Set G) ⊔ centralizerSection (A ⊔ V) V
  four3 : IsQuotIso (normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)
    (centralizerSection (A ⊔ V) V) ↥blockStab
  four4 : Even ((normalizer ((A ⊔ V : Subgroup G) : Set G)).relIndex (normalizer (V : Set G)))

end CFSG.OddStandard.HigherRank.YamadaG23
