module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module

variable {G : Type*} [Group G] [Finite G]

structure Config (S : Setting G) where
  Xbar : Subgroup S.O
  At : Submodule (ZMod 2) S.Qt
  Bt : Submodule (ZMod 2) S.Qt
  four_le_width : 4 ≤ S.width
  Xbar_le : Xbar ≤ S.Mbar
  relIndex_Xbar : Xbar.relIndex S.Mbar = 2
  nonempty_equiv : Nonempty (Xbar ≃* Matrix.SpecialLinearGroup (Fin S.width) (ZMod 2))
  finrank_At : finrank (ZMod 2) At = S.width
  finrank_Bt : finrank (ZMod 2) Bt = S.width
  q_At : ∀ v ∈ At, S.q v = 0
  q_Bt : ∀ v ∈ Bt, S.q v = 0
  inf_eq : At ⊓ Bt = ⊥
  sup_eq : At ⊔ Bt = ⊤
  apply_At : ∀ x ∈ Xbar, ∀ v ∈ At, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ At
  apply_Bt : ∀ x ∈ Xbar, ∀ v ∈ Bt, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Bt
  map_At : ∀ σ ∈ S.Mbar, σ ∉ Xbar →
    At.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = Bt
  transitive : ∀ v ∈ At, v ≠ 0 → ∀ w ∈ At, w ≠ 0 →
    ∃ x ∈ Xbar, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w
  invariant : ∀ W : Submodule (ZMod 2) S.Qt,
    (∀ x ∈ Xbar, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) →
      W = ⊥ ∨ W = At ∨ W = Bt ∨ W = ⊤
  conj_At : ∀ v ∈ At, v ≠ 0 → ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧ S.cl (k * S.z * k⁻¹) = v
  fusion : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG →
    S.cl (k * S.z * k⁻¹) ∈ At ∨ S.cl (k * S.z * k⁻¹) ∈ Bt
  centralizer_A : centralizer (S.clPre At : Set G) = S.clPre At
  normalizer_inf_M : normalizer (S.clPre At : Set G) ⊓ S.M = (Xbar.comap S.ρ).map S.M.subtype
  card_normalizer : Nat.card (normalizer (S.clPre At : Set G)) =
    2 ^ (S.width + 1) * Nat.card (GL (Fin (S.width + 1)) (ZMod 2))

end CFSG.LargeExtraspecial.GLR
