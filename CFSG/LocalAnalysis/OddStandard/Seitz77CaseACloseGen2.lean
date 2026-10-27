module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem exists_normalizing_sq_mem {G : Type*} [Group G] [Finite G] {P T : Subgroup G}
    (hT : IsPGroup 2 T) (hPT : P ≤ T) (hne : P ≠ T) :
    ∃ δ ∈ T, (∀ x, x ∈ P ↔ δ * x * δ⁻¹ ∈ P) ∧ δ ∉ P ∧ δ * δ ∈ P := by
  have hI : P.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hPT fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : T) ∈ P.subgroupOf T := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hI)
  have hxN' : (x : G) ∈ normalizer (P : Set G) := by
    have hxsub : x ∈ (normalizer (P : Set G)).subgroupOf T := by
      rw [subgroupOf_normalizer_eq hPT]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  have hxP : (x : G) ∉ P := fun hx => hxnot (mem_subgroupOf.mpr hx)
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT x
  have hxn : (x : G) ^ (2 ^ n) ∈ P := by
    have : (x : G) ^ (2 ^ n) = 1 := by
      have h1 : (x : G) ^ orderOf (x : G) = 1 := pow_orderOf_eq_one _
      rwa [Subgroup.orderOf_coe, hn] at h1
    rw [this]
    exact P.one_mem
  have hex : ∃ k, (x : G) ^ (2 ^ k) ∈ P := ⟨n, hxn⟩
  classical
  set m := Nat.find hex with hm
  have hm0 : m ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm, h0] at this
    simp only [pow_zero, pow_one] at this
    exact hxP this
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : (x : G) ^ (2 ^ m') ∉ P := Nat.find_min hex (by omega)
  have hsq : (x : G) ^ (2 ^ m') * (x : G) ^ (2 ^ m') ∈ P := by
    have := Nat.find_spec hex
    rw [← hm, hm', pow_succ, pow_mul, sq] at this
    exact this
  have hδT : (x : G) ^ (2 ^ m') ∈ T := T.pow_mem x.2 _
  have hδN : (x : G) ^ (2 ^ m') ∈ normalizer (P : Set G) := Subgroup.pow_mem _ hxN' _
  exact ⟨_, hδT, fun y => mem_normalizer_iff.mp hδN y, hmin, hsq⟩

section Ext

variable {G : Type*} [Group G]

@[expose] def extByElt (P : Subgroup G) (δ : G) (hδ : ∀ x, x ∈ P ↔ δ * x * δ⁻¹ ∈ P)
    (hδ2 : δ * δ ∈ P) : Subgroup G where
  carrier := {x | x ∈ P ∨ δ⁻¹ * x ∈ P}
  mul_mem' := by
    have hc : ∀ x, δ⁻¹ * x * δ ∈ P ↔ x ∈ P := fun x => by
      rw [hδ (δ⁻¹ * x * δ)]
      have : δ * (δ⁻¹ * x * δ) * δ⁻¹ = x := by group
      rw [this]
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (P.mul_mem ha hb)
    · refine Or.inr ?_
      have : δ⁻¹ * (a * b) = (δ⁻¹ * a * δ) * (δ⁻¹ * b) := by group
      rw [this]
      exact P.mul_mem ((hc a).2 ha) hb
    · refine Or.inr ?_
      have : δ⁻¹ * (a * b) = (δ⁻¹ * a) * b := by group
      rw [this]
      exact P.mul_mem ha hb
    · refine Or.inl ?_
      have : a * b = (δ * δ) * (δ⁻¹ * (δ⁻¹ * a) * δ) * (δ⁻¹ * b) := by group
      rw [this]
      exact P.mul_mem (P.mul_mem hδ2 ((hc _).2 ha)) hb
  one_mem' := Or.inl P.one_mem
  inv_mem' := by
    have hc : ∀ x, δ⁻¹ * x * δ ∈ P ↔ x ∈ P := fun x => by
      rw [hδ (δ⁻¹ * x * δ)]
      have : δ * (δ⁻¹ * x * δ) * δ⁻¹ = x := by group
      rw [this]
    rintro a (ha | ha)
    · exact Or.inl (P.inv_mem ha)
    · refine Or.inr ?_
      have : δ⁻¹ * a⁻¹ = (δ⁻¹ * (δ⁻¹ * a)⁻¹ * δ) * (δ * δ)⁻¹ := by group
      rw [this]
      exact P.mul_mem ((hc _).2 (P.inv_mem ha)) (P.inv_mem hδ2)

theorem mem_extByElt_iff {P : Subgroup G} {δ : G} {hδ : ∀ x, x ∈ P ↔ δ * x * δ⁻¹ ∈ P}
    {hδ2 : δ * δ ∈ P} {x : G} : x ∈ extByElt P δ hδ hδ2 ↔ x ∈ P ∨ δ⁻¹ * x ∈ P := Iff.rfl

end Ext

end CFSG.OddStandard.Seitz77
