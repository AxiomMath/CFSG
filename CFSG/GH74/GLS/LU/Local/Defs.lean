module

public import CFSG.GH74.GLS.LU.Local.CenAb
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

abbrev Cz {G : Type} [Group G] (z : G) : Subgroup G := centralizer ({z} : Set G)

abbrev A0 {G : Type} [Group G] (z : G) : Subgroup G := pPrimeCoreOf 2 (Cz z)

structure LUComps (G : Type) [Group G] (q : ℕ) (z : G) (K₁ K₂ : Subgroup G) : Prop where
  comp₁ : IsCompIn (Cz z) K₁
  comp₂ : IsCompIn (Cz z) K₂
  ne : K₁ ≠ K₂
  only : ∀ L : Subgroup G, IsPCompIn 2 (Cz z) L → L = K₁ ∨ L = K₂
  sl₁ : HasSL2Model ↥K₁ (fun r => r = q)
  sl₂ : HasSL2Model ↥K₂ (fun r => r = q)
  cen₁ : (center ↥K₁).map K₁.subtype = zpowers z
  cen₂ : (center ↥K₂).map K₂.subtype = zpowers z

structure LUSyl (G : Type) [Group G] (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G) : Prop where
  z_inv : orderOf z = 2
  z_cen : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z
  t_mem : t ∈ (S : Subgroup G)
  t_conj : IsConj z t
  t_swap : K₁.map (MulAut.conj t).toMonoidHom = K₂
  u_mem : u ∈ (S : Subgroup G)
  u_ord : orderOf u = 2
  u_ne : u ≠ z
  u_conj : IsConj z u
  uz_conj : IsConj z (u * z)
  u_norm : u ∈ normalizer (K₁ : Set G)
  ut : u * t = t * u
  coset : ∀ s ∈ (S : Subgroup G), s ∉ normalizer (K₁ : Set G) →
    ∃ k ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), IsConj z (k * s)
  cs : ∀ s ∈ (S : Subgroup G), (∀ k ∈ K₁ ⊔ K₂, s * k = k * s) → s ∈ zpowers z
  card_S : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂))
  cen_ab : LUCenAb (S : Subgroup G) K₁

end CFSG.GH74.GLS.LU.Local
