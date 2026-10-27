module

public import CFSG.GroupTheory.HuppertProduct.Mho
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem map_subtype_mho_top (S : Subgroup G) (p : ℕ) :
    (mho (⊤ : Subgroup S) p).map S.subtype = mho S p := by
  unfold mho
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨g, -, rfl⟩, rfl⟩
    exact ⟨g.1, g.2, by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩ ^ p, ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩, by simp⟩

theorem subgroupOf_mho_self (S : Subgroup G) (p : ℕ) :
    (mho S p).subgroupOf S = mho (⊤ : Subgroup S) p := by
  unfold Subgroup.subgroupOf
  rw [← map_subtype_mho_top S p]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem relIndex_mho_self (S : Subgroup G) (p : ℕ) :
    (mho S p).relIndex S = (mho (⊤ : Subgroup S) p).index := by
  unfold Subgroup.relIndex
  rw [subgroupOf_mho_self]

theorem pow_mem_of_isCoatom_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {H : Subgroup P} (hH : IsCoatom H) (x : P) : x ^ p ∈ H := by
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  have hidx : H.index = p := (IsPGroup.isCoatom_iff_index_eq_prime hP).1 hH
  haveI : H.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom H Group.normalizerCondition_of_isNilpotent hH
  have h := H.pow_index_mem x
  rwa [hidx] at h

theorem eq_bot_of_mho_eq_self {G : Type*} [Group G] [Finite G] {S : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hS : IsPGroup p S) (h : mho S p = S) : S = ⊥ := by
  by_contra hne
  have hnt : (⊥ : Subgroup S) ≠ ⊤ := by
    intro htop
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx⟩ : S) ∈ (⊥ : Subgroup S) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  obtain ⟨H, hH, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup S)).resolve_left hnt
  have hHle : mho (⊤ : Subgroup S) p ≤ H :=
    mho_le_of_forall fun x _ => pow_mem_of_isCoatom_of_isPGroup hS hH x
  have hmap : (mho (⊤ : Subgroup S) p).map S.subtype = (⊤ : Subgroup S).map S.subtype := by
    rw [map_subtype_mho_top, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : mho (⊤ : Subgroup S) p = ⊤ :=
    Subgroup.map_injective (f := S.subtype) Subtype.val_injective hmap
  rw [htop] at hHle
  exact hH.ne_top (top_le_iff.1 hHle)

theorem isCyclic_of_relIndex_mho_le {G : Type*} [Group G] [Finite G] {S : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hS : IsPGroup p S) (h : (mho S p).relIndex S ≤ p) : IsCyclic S := by
  rw [relIndex_mho_self] at h
  by_contra hnc
  haveI : Group.IsNilpotent S := IsPGroup.isNilpotent hS
  haveI : IsCoatomic (Subgroup S) := inferInstance
  obtain ⟨H₁, H₂, hne, h₁, h₂⟩ := (IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime hS).1 hnc
  have hc₁ : IsCoatom H₁ := (IsPGroup.isCoatom_iff_index_eq_prime hS).2 h₁
  have hc₂ : IsCoatom H₂ := (IsPGroup.isCoatom_iff_index_eq_prime hS).2 h₂
  have hM₁ : mho (⊤ : Subgroup S) p ≤ H₁ :=
    mho_le_of_forall fun x _ => pow_mem_of_isCoatom_of_isPGroup hS hc₁ x
  have hM₂ : mho (⊤ : Subgroup S) p ≤ H₂ :=
    mho_le_of_forall fun x _ => pow_mem_of_isCoatom_of_isPGroup hS hc₂ x
  have hrel : (mho (⊤ : Subgroup S) p).relIndex H₁ * H₁.index =
      (mho (⊤ : Subgroup S) p).index := Subgroup.relIndex_mul_index hM₁
  rw [h₁] at hrel
  have hpos : 0 < p := Nat.Prime.pos Fact.out
  have hMne : (mho (⊤ : Subgroup S) p).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr0 : 0 < (mho (⊤ : Subgroup S) p).relIndex H₁ :=
    Nat.pos_of_ne_zero fun h0 => hMne (by rw [← hrel, h0, zero_mul])
  have hr1 : (mho (⊤ : Subgroup S) p).relIndex H₁ ≤ 1 := by
    have hle : (mho (⊤ : Subgroup S) p).relIndex H₁ * p ≤ 1 * p := by
      rw [one_mul, hrel]
      exact h
    exact Nat.le_of_mul_le_mul_right hle hpos
  have hrel1 : (mho (⊤ : Subgroup S) p).relIndex H₁ = 1 := le_antisymm hr1 hr0
  have hH₁M : H₁ ≤ mho (⊤ : Subgroup S) p := Subgroup.relIndex_eq_one.1 hrel1
  have hH₁H₂ : H₁ ≤ H₂ := hH₁M.trans hM₂
  exact hne ((hc₁.le_iff_eq hc₂.ne_top).1 hH₁H₂).symm

end CFSG.GroupTheory.HuppertProduct
