module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Syl

open Subgroup

theorem exists_central_involution {Y : Type*} [Group Y] {R : Subgroup Y} [Finite R]
    (hR : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) :
    ∃ τ ∈ R, orderOf τ = 2 ∧ ∀ g ∈ R, g * τ = τ * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hR1
  have : Nontrivial ↥(center ↥R) := hR.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥R) := hR.to_subgroup _
  have hZcard : 2 ∣ Nat.card ↥(center ↥R) := by
    rcases hZp.card_eq_or_dvd with h | h
    · have := Finite.one_lt_card (α := ↥(center ↥R))
      omega
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZcard
  refine ⟨((z : ↥(center ↥R)) : Y), (z : ↥R).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  · intro g hg
    have := Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩
    exact congrArg Subtype.val this

theorem card_map_mul_card_ker {H K : Type*} [Group H] [Group K] (π : H →* K) {S : Subgroup H}
    (hS : π.ker ≤ S) : Nat.card ↥(S.map π) * Nat.card ↥π.ker = Nat.card ↥S := by
  let f : ↥S →* K := π.comp S.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hr : f.range = S.map π := by
    ext k
    simp only [f, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_map]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hk : Nat.card ↥f.ker = Nat.card ↥π.ker := by
    refine Nat.card_congr ⟨fun x => ⟨(x.1 : H), ?_⟩, fun x => ⟨⟨x.1, hS x.2⟩, ?_⟩, ?_, ?_⟩
    · have h := x.2
      rw [MonoidHom.mem_ker] at h ⊢
      exact h
    · have h := x.2
      rw [MonoidHom.mem_ker] at h ⊢
      exact h
    · intro x
      rfl
    · intro x
      rfl
  rw [hr, hk] at h1
  rw [mul_comm]
  exact h1

theorem eq_one_or_eq_of_card_two {Y : Type*} [Group Y] {Z : Subgroup Y} (hZ : Nat.card ↥Z = 2)
    {τ : Y} (hτ : τ ∈ Z) (hτ1 : τ ≠ 1) {z : Y} (hz : z ∈ Z) : z = 1 ∨ z = τ := by
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by omega)
  have hord : orderOf τ = 2 := by
    have h1 : orderOf (⟨τ, hτ⟩ : ↥Z) ∣ 2 := hZ ▸ orderOf_dvd_natCard _
    have h2 : orderOf (⟨τ, hτ⟩ : ↥Z) ≠ 1 := by
      intro h
      apply hτ1
      have := orderOf_eq_one_iff.1 h
      exact congrArg Subtype.val this
    have h3 : orderOf (⟨τ, hτ⟩ : ↥Z) = 2 := by
      have := (Nat.dvd_prime Nat.prime_two).1 h1
      omega
    rw [← h3, Subgroup.orderOf_mk]
  have hle : Subgroup.zpowers τ ≤ Z := (Subgroup.zpowers_le).2 hτ
  have hcard : Nat.card ↥Z ≤ Nat.card ↥(Subgroup.zpowers τ) := by
    rw [hZ, Nat.card_zpowers, hord]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hz
  rcases Subgroup.mem_zpowers_iff.1 hz with ⟨k, rfl⟩
  have h2 : τ ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one τ
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : τ ^ k = (τ ^ 2) ^ (k / 2) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      omega
    rw [this, h2, one_zpow]
  · right
    have : τ ^ k = (τ ^ 2) ^ (k / 2) * τ := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add_one]
      congr 1
      omega
    rw [this, h2, one_zpow, one_mul]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Syl
