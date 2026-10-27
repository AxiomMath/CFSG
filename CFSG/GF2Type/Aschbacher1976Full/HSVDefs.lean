module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

structure HSV (z : G) (T V : Subgroup G) : Prop where
  isElem : CFSG.Open.IsElemAbelian 2 V
  card_eq : Nat.card V = 8
  le_F : V ≤ Fz z
  z_mem : z ∈ V
  sylow : IsPGroup 2 T ∧ ∀ S : Subgroup G, IsPGroup 2 S → T ≤ S → S = T
  le_H : T ≤ Hz z
  F_le_T : Fz z ≤ T
  normal_in_T : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V
  isConj : ∀ v ∈ V, v ≠ 1 → IsConj z v
  ZF_le : ∀ v ∈ V, v ≠ 1 → ZF v ≤ T
  ZF_comm : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∀ a ∈ ZF v, ∀ b ∈ ZF w, a * b = b * a
  trans : ∀ v ∈ V, v ≠ 1 → ∃ n ∈ Subgroup.normalizer (V : Set G), n * z * n⁻¹ = v
  W_comm : ∀ a ∈ WT T z, ∀ b ∈ WT T z, a * b = b * a
  card_W : Nat.card (WT T z) = 64
  W_le_T : WT T z ≤ T
  ZF_le_W : ∀ v ∈ V, v ≠ 1 → ZF v ≤ WT T z

end CFSG.GF2Type.Aschbacher1976Full.HS
