module

public import CFSG.GroupTheory.HuppertProduct.Mho
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory.HuppertProduct

private theorem exists_natPow_gen {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsCyclic A) : ∃ α ∈ A, ∀ a ∈ A, ∃ n : ℕ, a = α ^ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  refine ⟨(g : G), g.2, fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  have hak : (g : G) ^ k = a := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hpow : a ∈ Submonoid.powers (g : G) :=
    mem_powers_iff_mem_zpowers.mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, hak⟩)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a (g : G)).mp hpow
  exact ⟨n, hn.symm⟩

theorem relIndex_mho_le_of_mul_cyclic {G : Type*} [Group G] [Finite G] {S A B : Subgroup G} {p : ℕ}
    (hp : 0 < p) (hA : A ≤ S) (hB : B ≤ S) (hAc : IsCyclic A) (hBc : IsCyclic B)
    (hprod : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    (mho S p).relIndex S ≤ p ^ 2 := by
  obtain ⟨α, hαA, hα⟩ := exists_natPow_gen hAc
  obtain ⟨β, hβB, hβ⟩ := exists_natPow_gen hBc
  have hαS : α ∈ S := hA hαA
  have hβS : β ∈ S := hB hβB
  have hsplit : ∀ n : ℕ, ∃ r : ℕ, ∃ _ : r < p, ∃ q : ℕ, n = r + p * q := fun n =>
    ⟨n % p, Nat.mod_lt n hp, n / p, (Nat.mod_add_div n p).symm⟩
  have hsurj : Function.Surjective
      (fun rt : Fin p × Fin p =>
        (QuotientGroup.mk ⟨α ^ (rt.1 : ℕ) * β ^ (rt.2 : ℕ),
          S.mul_mem (S.pow_mem hαS _) (S.pow_mem hβS _)⟩ :
          ↥S ⧸ (mho S p).subgroupOf S)) := by
    intro x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha, b, hb, hsab⟩ := hprod (s : G) s.2
    obtain ⟨i, rfl⟩ := hα a ha
    obtain ⟨j, rfl⟩ := hβ b hb
    obtain ⟨r, hr, i₁, rfl⟩ := hsplit i
    obtain ⟨t, ht, j₁, rfl⟩ := hsplit j
    refine ⟨(⟨r, hr⟩, ⟨t, ht⟩), ?_⟩
    have key : (α ^ r * β ^ t)⁻¹ * (α ^ (r + p * i₁) * β ^ (t + p * j₁))
        = ((β ^ t)⁻¹ * α ^ (p * i₁) * ((β ^ t)⁻¹)⁻¹) * β ^ (p * j₁) := by
      rw [pow_add, pow_add]
      group
    have hαp : α ^ (p * i₁) ∈ mho S p := by
      rw [pow_mul']
      exact pow_mem_mho (S.pow_mem hαS i₁)
    have hβp : β ^ (p * j₁) ∈ mho S p := by
      rw [pow_mul']
      exact pow_mem_mho (S.pow_mem hβS j₁)
    have hβt : (β ^ t)⁻¹ ∈ S := S.inv_mem (S.pow_mem hβS t)
    have hconj : (β ^ t)⁻¹ * α ^ (p * i₁) * ((β ^ t)⁻¹)⁻¹ ∈ mho S p :=
      conj_mem_mho (fun s hs => S.mul_mem (S.mul_mem hβt hs) (S.inv_mem hβt)) hαp
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show (α ^ r * β ^ t)⁻¹ * (s : G) ∈ mho S p
    rw [hsab, key]
    exact (mho S p).mul_mem hconj hβp
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_fin] at hcard
  exact hcard.trans_eq (sq p).symm

end CFSG.GroupTheory.HuppertProduct
