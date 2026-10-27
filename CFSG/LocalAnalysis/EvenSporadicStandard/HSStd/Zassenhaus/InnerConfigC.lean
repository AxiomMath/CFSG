module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerConfig

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup

variable {G : Type*} [Group G]

structure InnerD8ConfigC (L : Subgroup G) (t : G) extends InnerD8Config L t where
  K₁ : Subgroup G
  eK₁ : ↥K₁ ≃* alternatingGroup (Fin 5)
  K₁_comm_x : ∀ a ∈ K₁, a * x = x * a
  K₁_comm_xt : ∀ a ∈ K₁, a * (t * x * t⁻¹) = (t * x * t⁻¹) * a
  K₁_comm_K₁t : ∀ a ∈ K₁, ∀ b ∈ K₁, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a
  u₁_norm_K₁ : u₁ ∈ normalizer (K₁ : Set G)
  u₁_S₅ : Nonempty (↥(K₁ ⊔ zpowers u₁) ≃* Equiv.Perm (Fin 5))
  u₁_comm_K₁t : ∀ b ∈ K₁, u₁ * (t * b * t⁻¹) = (t * b * t⁻¹) * u₁
  centralizer_x_xt : centralizer ({x} : Set G) ⊓ centralizer ({t * x * t⁻¹} : Set G) =
    (zpowers x ⊔ zpowers (t * x * t⁻¹)) ⊔ (K₁ ⊔ zpowers u₁) ⊔ conjSub t (K₁ ⊔ zpowers u₁)
  c₃ : G
  c₃_mem_K₁ : c₃ ∈ K₁
  c₃_mem_L₁ : c₃ ∈ L₁
  c₃_ord : orderOf c₃ = 3
  c₃_comm_x : c₃ * x = x * c₃
  c₃_not_mem : c₃ ∉ zpowers x
  k : G
  k_mem : k ∈ K₁
  k_ord : orderOf k = 2
  k_comm_u : k * u = u * k
  k_norm : k ∈ normalizer (L₁ : Set G)
  k_outer : ∀ l : ↥L₁, conjAutOf L₁ k_norm ≠ MulAut.conj l
  k_comm_L₁t : ∀ l ∈ L₁, k * (t * l * t⁻¹) = (t * l * t⁻¹) * k

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
