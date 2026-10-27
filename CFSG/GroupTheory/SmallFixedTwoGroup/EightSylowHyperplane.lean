module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_relIndex_two_notMem_of_fixed {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {x : G} (hx : x ^ 3 = 1)
    (hxN : x ∈ normalizer (T : Set G)) {p : G} (hpT : p ∈ T) (hp1 : p ≠ 1)
    (hpx : x * p * x⁻¹ = p) (hF : ∀ y ∈ T, x * y * x⁻¹ = y → y = 1 ∨ y = p) :
    ∃ M : Subgroup G, M ≤ T ∧ M.relIndex T = 2 ∧ p ∉ M := by
  haveI : IsMulCommutative ↥T :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hab a a.2 b b.2))
  have hppT : p * p ∈ T := T.mul_mem hpT hpT
  have hpp_fix : x * (p * p) * x⁻¹ = p * p := by
    calc x * (p * p) * x⁻¹ = (x * p * x⁻¹) * (x * p * x⁻¹) := by group
      _ = p * p := by rw [hpx]
  have hpp : p * p = 1 := by
    rcases hF (p * p) hppT hpp_fix with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one p).symm)) hp1
  let c : ↥T →* ↥T := MonoidHom.mk' (fun z : ↥T =>
      ⟨x * (z : G) * x⁻¹,
        ((Subgroup.mem_normalizer_iff (H := T) (g := x)).mp hxN z).mp z.2⟩)
    (fun a b => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk]
      group)
  have hc3 : ∀ y : ↥T, c (c (c y)) = y := by
    intro y
    apply Subtype.ext
    show x * (x * (x * (y : G) * x⁻¹) * x⁻¹) * x⁻¹ = (y : G)
    have hx3 : x * x * x = 1 := by simpa [pow_succ, pow_two] using hx
    calc x * (x * (x * (y : G) * x⁻¹) * x⁻¹) * x⁻¹
        = (x * x * x) * (y : G) * (x * x * x)⁻¹ := by group
      _ = (y : G) := by rw [hx3]; simp
  let φ : ↥T →* ↥T := MonoidHom.mk' (fun y : ↥T => y * c y * c (c y))
    (fun a b => by
      simp only [map_mul]
      ac_rfl)
  have hc_p : c ⟨p, hpT⟩ = ⟨p, hpT⟩ := by
    apply Subtype.ext
    show x * p * x⁻¹ = p
    exact hpx
  have hφp : φ ⟨p, hpT⟩ = ⟨p, hpT⟩ := by
    change (⟨p, hpT⟩ : ↥T) * c ⟨p, hpT⟩ * c (c ⟨p, hpT⟩) = ⟨p, hpT⟩
    simp only [hc_p]
    apply Subtype.ext
    change p * p * p = p
    rw [hpp]
    simp
  have hfix_c : ∀ y : ↥T, c (φ y) = φ y := by
    intro y
    change c (y * c y * c (c y)) = y * c y * c (c y)
    simp only [map_mul, hc3]
    ac_rfl
  have hfixG : ∀ y : ↥T, x * (φ y : G) * x⁻¹ = (φ y : G) := by
    intro y
    have h := congrArg (Subtype.val) (hfix_c y)
    exact h
  have hrange : ∀ y : ↥T, φ y = 1 ∨ φ y = ⟨p, hpT⟩ := by
    intro y
    rcases hF (φ y : G) (φ y).2 (hfixG y) with h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Subtype.ext (by simpa using h))
  have hq_ne : (⟨p, hpT⟩ : ↥T) ≠ 1 := by
    intro h
    exact hp1 (by simpa using Subtype.ext_iff.mp h)
  have hq_mem : (⟨p, hpT⟩ : ↥T) ∈ φ.range := ⟨⟨p, hpT⟩, hφp⟩
  have hcard : Nat.card φ.range = 2 := by
    rw [Nat.card_eq_two_iff' (1 : φ.range)]
    refine ⟨⟨⟨p, hpT⟩, hq_mem⟩, ?_, ?_⟩
    · intro h
      exact hq_ne (Subtype.ext_iff.mp h)
    · intro z hz
      have hzmem : z.1 ∈ φ.range := z.2
      rw [MonoidHom.mem_range] at hzmem
      obtain ⟨t, ht⟩ := hzmem
      have hzt : z.1 = 1 ∨ z.1 = ⟨p, hpT⟩ := by
        rw [← ht]
        exact hrange t
      rcases hzt with h1 | hq
      · exact absurd (Subtype.ext h1) hz
      · exact Subtype.ext hq
  refine ⟨φ.ker.map T.subtype, Subgroup.map_subtype_le φ.ker, ?_, ?_⟩
  · have hsub : (φ.ker.map T.subtype).subgroupOf T = φ.ker := by
      rw [← Subgroup.comap_subtype (φ.ker.map T.subtype) T,
        Subgroup.comap_map_eq_self_of_injective T.subtype_injective]
    show ((φ.ker.map T.subtype).subgroupOf T).index = 2
    rw [hsub, Subgroup.index_ker, hcard]
  · intro hpM
    rw [Subgroup.mem_map] at hpM
    obtain ⟨k, hk, hkp⟩ := hpM
    have hkq : k = ⟨p, hpT⟩ := Subtype.ext hkp
    have hk1 : φ k = 1 := hk
    rw [hkq, hφp] at hk1
    exact hq_ne hk1

end CFSG.GroupTheory.SmallFixedTwoGroup
