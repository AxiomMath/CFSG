module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Cfg (z x : G) (T : Subgroup G) (q : ℕ) : Prop where
  z_central : IsCentralInvolution z
  x_mem : x ∈ Cen z
  x_nc : IsNonCentralInvolution x
  xz_conj : IsConj z (x * z)
  classes : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u
  T_syl : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))
  z_mem_T : z ∈ T
  z_extremal : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Cen z) (centralizer ({x, z} : Set G))
  q_odd : Odd q
  q_gt : 3 < q
  I_L2 : IVK.IsL2 (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) (fun r => r = q)

structure Syl (z x : G) (T D₁ D₂ U : Subgroup G) (n : ℕ) (t' : G) : Prop where
  D₁_dih : IVK.IsDihedralTwoGroup ↥D₁ n
  D₂_dih : IVK.IsDihedralTwoGroup ↥D₂ n
  D₁_le : D₁ ≤ T
  D₂_le : D₂ ≤ T
  comm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a
  inter : D₁ ⊓ D₂ = ⊥
  index : (D₁ ⊔ D₂).relIndex T ≤ 2
  D₁_normal : ∀ s ∈ T, ∀ d ∈ D₁, s * d * s⁻¹ ∈ D₁
  x_mem : x ∈ D₁
  x_center : n = 2 ∨ (center ↥D₁).map D₁.subtype = zpowers x
  z_mem : z ∈ D₁
  z_ne : z ≠ x
  U_syl : CFSG.ABGLocalTools.IsSylowOf 2 U (Ixz z x)
  U_le : U ≤ D₂
  U_card : Nat.card ↥D₂ ≤ 2 * Nat.card ↥U
  t'_mem : t' ∈ D₂
  t'_U : t' ∈ U
  t'_ord : orderOf t' = 2
  center_T : (center ↥T).map T.subtype = zpowers x ⊔ zpowers t'
  t'_conj : IsConj x t'
  xt'_conj : IsConj z (x * t')

structure Tr (z x : G) (T D₁ D₂ U T₁ : Subgroup G) : Prop where
  I_le_J : Ixz z x ≤ Jx x
  T₁_cyc : IsCyclic ↥T₁
  T₁_le : T₁ ≤ D₁
  x_mem_T₁ : x ∈ T₁
  T₁_card : Nat.card ↥T₁ * 2 = Nat.card ↥D₂
  S1 : ∀ g ∈ T ⊓ Jx x, g ∈ T₁ ⊔ D₂

@[expose] def Datum (z x : G) : Prop :=
  ∃ (T D₁ D₂ U T₁ : Subgroup G) (q n : ℕ) (t' : G),
    Cfg z x T q ∧ Syl z x T D₁ D₂ U n t' ∧ Tr z x T D₁ D₂ U T₁

@[expose] def P27Datum (z : G) (k : Kind) : Prop :=
  IsClassicalKind k → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) → ∃ x : G, Datum z x

@[expose] def Leaf_P27Datum
    (Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S → P27Datum z k

end CFSG.GH74.GLS.Stage2.Local.P27
