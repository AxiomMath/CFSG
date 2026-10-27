module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G]

structure CaseI (K R T : Subgroup G) : Prop where
  relIndex_two : (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R = 2
  inv : ∀ x ∈ R, x ∉ R ⊓ Subgroup.normalizer (T : Set G) →
    ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), x * n * x⁻¹ = n⁻¹
  comm : ∀ a ∈ R ⊓ Subgroup.normalizer (T : Set G),
    ∀ b ∈ R ⊓ Subgroup.normalizer (T : Set G), a * b = b * a
  iso : Nonempty (↥(R ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T)
  exists_sq_ne : ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n ≠ 1
  not_cyclic : ¬ IsCyclic ↥(R ⊓ Subgroup.normalizer (T : Set G))
  normal : ((R ⊓ Subgroup.normalizer (T : Set G)).subgroupOf K).Normal

structure CaseII4 (K R T : Subgroup G) : Prop where
  elem_T : IsElemAbelian 2 T
  four_le : 4 ≤ Nat.card ↥T
  elem_N : IsElemAbelian 2 (R ⊓ Subgroup.normalizer (T : Set G))
  iso : Nonempty (↥(R ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T)
  central : ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), ∀ r ∈ R, n * r = r * n
  sq_mem : ∀ x ∈ R, x * x ∈ R ⊓ Subgroup.normalizer (T : Set G)
  comm_mem : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G)
  one_lt_relIndex : 1 < (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R
  relIndex_le : (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R ≤
    Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G))
  normal : ((R ⊓ Subgroup.normalizer (T : Set G)).subgroupOf K).Normal

structure CaseII5 (K R T H : Subgroup G) : Prop where
  elem_T : IsElemAbelian 2 T
  four_le : 4 ≤ Nat.card ↥T
  H_le : H ≤ R
  relIndex_two : H.relIndex R = 2
  card_H : Nat.card ↥H = Nat.card ↥T ^ 2
  pow_four : ∀ x ∈ H, x ^ 4 = 1
  omega_le : ∀ x ∈ H, x ^ 2 = 1 → x ∈ R ⊓ Subgroup.normalizer (T : Set G)
  N_le : R ⊓ Subgroup.normalizer (T : Set G) ≤ H
  N_central : ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), ∀ h ∈ H, n * h = h * n
  elem_N : ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n = 1
  iso : Nonempty (↥(R ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T)
  N_conj : ∀ r ∈ R, ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G),
    r * n * r⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G)
  normal : (H.subgroupOf K).Normal
  gen : ∀ x ∈ R, x ∉ H → ∀ h ∈ H,
    ∃ t ∈ T, ∃ z ∈ R ⊓ Subgroup.normalizer (T : Set G), h = z * (t * x * t⁻¹ * x⁻¹)
  comm_mem : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ H
  comm_not_mem : ∀ x ∈ R, x ∉ H → ∀ t ∈ T, t ≠ 1 →
    t * x * t⁻¹ * x⁻¹ ∉ R ⊓ Subgroup.normalizer (T : Set G)

end CFSG.CGT.PushingUpLit.SolKNA
