module

public import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Basic

variable {G : Type*} [Group G]

theorem comm_of_mul_self_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem isPGroup_two_zpowers_of_mul_self_eq_one {z : G} (hz : z * z = 1) :
    IsPGroup 2 (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hz1 : z = 1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, hz1, orderOf_one, pow_zero])
  · have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz) hz1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])

theorem mem_sylow_of_mem_normalizer [Finite G] (S : Sylow 2 G) {z : G} (hz : z * z = 1)
    (hzN : z ∈ normalizer ((S : Subgroup G) : Set G)) : z ∈ (S : Subgroup G) := by
  have hP := isPGroup_two_zpowers_of_mul_self_eq_one hz
  have hzN' : z ∈ normalizer (S : Set G) := hzN
  have h1 : z ∈ zpowers z ⊓ normalizer (S : Set G) := ⟨Subgroup.mem_zpowers z, hzN'⟩
  rw [hP.inf_normalizer_sylow S] at h1
  exact h1.2

theorem sylow_eq_of_le [Finite G] (S : Sylow 2 G) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hST : (S : Subgroup G) ≤ T) : (S : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₂, hS₂⟩ := hT.exists_le_sylow
  have hcard : Nat.card S₂ = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h1 : (S : Subgroup G) = S₂ := Subgroup.eq_of_le_of_card_ge (hST.trans hS₂) hcard.le
  exact le_antisymm hST (h1 ▸ hS₂)

theorem sq_eq_one_of_two_pow_of_sylow [Finite G] (S : Sylow 2 G)
    (hS : ∀ x ∈ (S : Subgroup G), x * x = 1) {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers x) := by
    intro y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx,
      one_zpow]
    rfl
  obtain ⟨S₂, hS₂⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S₂
  have h1 : g⁻¹ * x * g ∈ (S : Subgroup G) :=
    (mem_sylow_smul_iff g S x).mp (hS₂ (Subgroup.mem_zpowers x))
  have h2 := hS _ h1
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem exists_index_two_of_ne [Finite G] {Q Z : Subgroup G} (hQ : IsPGroup 2 Q) (hZQ : Z ≤ Q)
    (hne : Z ≠ Q) :
    ∃ M : Subgroup G, M ≤ Q ∧ M ≠ Q ∧ Z ≤ M ∧ ∀ y ∈ Q, y * y ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hZ' : Z.subgroupOf Q ≠ ⊤ := by
    intro htop
    apply hne
    apply le_antisymm hZQ
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ Z.subgroupOf Q := by rw [htop]; trivial
    exact this
  obtain ⟨M', hM', hZM'⟩ : ∃ M' : Subgroup Q, IsCoatom M' ∧ Z.subgroupOf Q ≤ M' := by
    rcases eq_top_or_exists_le_coatom (Z.subgroupOf Q) with h | h
    · exact absurd h hZ'
    · exact h
  have hidx : M'.index = 2 := hQ.isCoatom_iff_index_eq_prime.mp hM'
  refine ⟨M'.map Q.subtype, Subgroup.map_subtype_le M', ?_, ?_, ?_⟩
  · intro h
    apply hM'.1
    apply Subgroup.map_injective (f := Q.subtype) Subtype.coe_injective
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] 
  · intro z hz
    have : (⟨z, hZQ hz⟩ : Q) ∈ M' := hZM' hz
    exact ⟨_, this, rfl⟩
  · intro y hy
    exact ⟨⟨y, hy⟩ * ⟨y, hy⟩, Subgroup.mul_self_mem_of_index_two hidx ⟨y, hy⟩, rfl⟩

end Basic

end CFSG.GH74.Uniqueness.Bender
