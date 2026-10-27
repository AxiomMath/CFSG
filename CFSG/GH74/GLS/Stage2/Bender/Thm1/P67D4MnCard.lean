module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup

section Card

variable {H : Type*} [Group H]

theorem card_sup_zpowers_of_cube_mem [Finite H] {T : Subgroup H} {m : H}
    (hm : ∀ t ∈ T, m * t * m⁻¹ ∈ T) (hm3 : m ^ 3 ∈ T) (hmT : m ∉ T) :
    Nat.card ↥(T ⊔ Subgroup.zpowers m) = 3 * Nat.card ↥T := by
  classical
  set S : Subgroup H := T ⊔ Subgroup.zpowers m with hS
  have hmS : m ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers m)
  have hTS : T ≤ S := le_sup_left
  have hmT' : ∀ t ∈ T, m⁻¹ * t * m ∈ T := by
    intro t ht
    have e : m⁻¹ * t * m = (m ^ 3)⁻¹ * (m * (m * t * m⁻¹) * m⁻¹) * m ^ 3 := by group
    rw [e]
    exact T.mul_mem (T.mul_mem (T.inv_mem hm3) (hm _ (hm _ ht))) hm3
  have hmN : m ∈ Subgroup.normalizer (T : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hm h hh, fun hh => ?_⟩
    have := hmT' _ hh
    simpa [mul_assoc] using this
  have hnorm : (T.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).2
      (sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hmN))
  let m' : ↥S := ⟨m, hmS⟩
  let q : S ⧸ T.subgroupOf S := QuotientGroup.mk m'
  have hq3 : q ^ 3 = 1 := by
    change (QuotientGroup.mk (m' ^ 3) : S ⧸ T.subgroupOf S) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hm3
  have hq1 : q ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hmT h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hgen : ∀ x : S ⧸ T.subgroupOf S, x ∈ Subgroup.zpowers q := by
    let W : Subgroup H :=
      ((Subgroup.zpowers q).comap (QuotientGroup.mk' (T.subgroupOf S))).map S.subtype
    have hTW : T ≤ W := by
      intro t ht
      have h1 : (QuotientGroup.mk (⟨t, hTS ht⟩ : ↥S) : S ⧸ T.subgroupOf S) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact ht
      refine ⟨⟨t, hTS ht⟩, ?_, rfl⟩
      show QuotientGroup.mk' (T.subgroupOf S) ⟨t, hTS ht⟩ ∈ Subgroup.zpowers q
      rw [QuotientGroup.mk'_apply, h1]
      exact Subgroup.one_mem _
    have hmW : m ∈ W := ⟨m', Subgroup.mem_zpowers q, rfl⟩
    have hSW : S ≤ W := sup_le hTW ((Subgroup.zpowers_le).2 hmW)
    intro x
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w, hw, hws⟩ := hSW hs
    have : w = ⟨s, hs⟩ := Subtype.ext hws
    subst this
    exact hw
  have hQ : Nat.card (S ⧸ T.subgroupOf S) = 3 := by
    have htop : Subgroup.zpowers q = ⊤ := (Subgroup.eq_top_iff' _).2 hgen
    calc Nat.card (S ⧸ T.subgroupOf S) = Nat.card (⊤ : Subgroup (S ⧸ T.subgroupOf S)) :=
          (Subgroup.card_top).symm
      _ = Nat.card (Subgroup.zpowers q) := by rw [htop]
      _ = 3 := by rw [Nat.card_zpowers, hqord]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf S), hQ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv]

end Card

end CFSG.GH74.GLS.Stage2.Bender.Thm1
