module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreA
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreB

import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem oddCore_normal_closure_orderOf (S : Type*) [Group S] (n : ℕ) :
    (Subgroup.closure {x : S | orderOf x = n}).Normal := by
  refine ⟨fun a ha g => ?_⟩
  refine Subgroup.closure_induction (p := fun a _ => g * a * g⁻¹ ∈
    Subgroup.closure {x : S | orderOf x = n}) (fun y hy => ?_) ?_ (fun a b _ _ ha hb => ?_)
    (fun a _ ha => ?_) ha
  · refine Subgroup.subset_closure ?_
    show orderOf (g * y * g⁻¹) = n
    rw [← hy]
    exact (MulAut.conj g).orderOf_eq y
  · simp
  · have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  · have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem oddCore_closure_orderOf_five_eq_top {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : Nat.card S = 60) : Subgroup.closure {x : S | orderOf x = 5} = ⊤ := by
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 (hS ▸ (by norm_num : 5 ∣ 60))
  have hN := oddCore_normal_closure_orderOf S 5
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {x : S | orderOf x = 5}) with
    h | h
  · exfalso
    have hxN : x ∈ Subgroup.closure {x : S | orderOf x = 5} := Subgroup.subset_closure hx
    rw [h, Subgroup.mem_bot] at hxN
    rw [hxN, orderOf_one] at hx
    omega
  · exact h

theorem oddCore_closure_orderOf_five_eq_top_prod {S₁ S₂ : Type*} [Group S₁] [Group S₂]
    (h₁ : Subgroup.closure {x : S₁ | orderOf x = 5} = ⊤)
    (h₂ : Subgroup.closure {x : S₂ | orderOf x = 5} = ⊤) :
    Subgroup.closure {x : S₁ × S₂ | orderOf x = 5} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have ha : (a, (1 : S₂)) ∈ Subgroup.closure {x : S₁ × S₂ | orderOf x = 5} := by
    have : a ∈ Subgroup.closure {x : S₁ | orderOf x = 5} := h₁ ▸ Subgroup.mem_top a
    have h' := Subgroup.mem_map_of_mem (MonoidHom.inl S₁ S₂) this
    rw [MonoidHom.map_closure] at h'
    refine (Subgroup.closure_mono ?_) h'
    rintro _ ⟨y, hy, rfl⟩
    show orderOf (y, (1 : S₂)) = 5
    rw [← hy]
    exact orderOf_injective (MonoidHom.inl S₁ S₂) (fun u v h => (Prod.ext_iff.mp h).1) y
  have hb : ((1 : S₁), b) ∈ Subgroup.closure {x : S₁ × S₂ | orderOf x = 5} := by
    have : b ∈ Subgroup.closure {x : S₂ | orderOf x = 5} := h₂ ▸ Subgroup.mem_top b
    have h' := Subgroup.mem_map_of_mem (MonoidHom.inr S₁ S₂) this
    rw [MonoidHom.map_closure] at h'
    refine (Subgroup.closure_mono ?_) h'
    rintro _ ⟨y, hy, rfl⟩
    show orderOf ((1 : S₁), y) = 5
    rw [← hy]
    exact orderOf_injective (MonoidHom.inr S₁ S₂) (fun u v h => (Prod.ext_iff.mp h).2) y
  have := mul_mem ha hb
  simpa using this

theorem odd_core_trivial_B_of_prod {H : Type*} [Group H] [Finite H]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (hperf : commutator H = ⊤)
    (K₀ : Subgroup H) [K₀.Normal] (hodd : Odd (Nat.card K₀))
    {S₁ S₂ : Type*} [Group S₁] [Group S₂] [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (h₁ : Nat.card S₁ = 60) (h₂ : Nat.card S₂ = 60)
    (e : H ⧸ K₀ ≃* S₁ × S₂) : K₀ = ⊥ := by
  refine odd_core_trivial_B ρ hρ hperf K₀ hodd ?_ ?_
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, h₁, h₂]
  · have hS := oddCore_closure_orderOf_five_eq_top_prod (oddCore_closure_orderOf_five_eq_top h₁)
      (oddCore_closure_orderOf_five_eq_top h₂)
    have hmap : (Subgroup.closure {y : S₁ × S₂ | orderOf y = 5}).map e.symm.toMonoidHom =
        Subgroup.closure {x : H ⧸ K₀ | orderOf x = 5} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show orderOf (e.symm y) = 5
        rw [MulEquiv.orderOf_eq]
        exact hy
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        show orderOf (e x) = 5
        rw [MulEquiv.orderOf_eq]
        exact hx
    rw [← hmap, hS]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective

theorem oddCore_nonempty_quotient_equiv_map {H N : Type*} [Group H] [Group N] (π : H →* N)
    (Hh : Subgroup H) : Nonempty (Hh ⧸ π.ker.subgroupOf Hh ≃* Hh.map π) := by
  have h1 : (π.comp Hh.subtype).ker = π.ker.subgroupOf Hh := rfl
  have h2 : (π.comp Hh.subtype).range = Hh.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h1.symm).trans
    ((QuotientGroup.quotientKerEquivRange (π.comp Hh.subtype)).trans
      (MulEquiv.subgroupCongr h2))⟩

theorem oddCore_odd_card_subgroupOf {H : Type*} [Group H] [Finite H] (K Hh : Subgroup H)
    (hodd : Odd (Nat.card K)) : Odd (Nat.card (K.subgroupOf Hh)) := by
  let f : K.subgroupOf Hh →* K :=
    (Hh.subtype.comp (K.subgroupOf Hh).subtype).codRestrict K (fun x => x.2)
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => (z : H)) h
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hf)

theorem oddCore_nonempty_mulEquiv_map_of_inf_ker_eq_bot {H N : Type*} [Group H] [Group N]
    (π : H →* N) (Hh : Subgroup H) (h : Hh ⊓ π.ker = ⊥) : Nonempty (Hh ≃* Hh.map π) := by
  have hinj : Function.Injective (π.comp Hh.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : H) ∈ Hh ⊓ π.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h2 : (π.comp Hh.subtype).range = Hh.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr h2)⟩

theorem odd_core_inf_ker_eq_bot_A {H N : Type*} [Group H] [Finite H] [Group N]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (π : H →* N) (Hh : Subgroup H)
    (hperf : commutator Hh = ⊤) (hodd : Odd (Nat.card π.ker))
    (hsimple : IsSimpleGroup (Hh.map π)) (hcard : Nat.card (Hh.map π) = 4080) :
    Hh ⊓ π.ker = ⊥ := by
  obtain ⟨e⟩ := oddCore_nonempty_quotient_equiv_map π Hh
  have := hsimple
  have h := odd_core_trivial_A (ρ.comp Hh.subtype) (hρ.comp Hh.subtype_injective) hperf
    (π.ker.subgroupOf Hh) (oddCore_odd_card_subgroupOf π.ker Hh hodd) e.isSimpleGroup
    (by rw [Nat.card_congr e.toEquiv, hcard])
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx.1⟩ : Hh) ∈ π.ker.subgroupOf Hh := hx.2
  rw [h, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem odd_core_inf_ker_eq_bot_B {H N : Type*} [Group H] [Finite H] [Group N]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (π : H →* N) (Hh : Subgroup H)
    (hperf : commutator Hh = ⊤) (hodd : Odd (Nat.card π.ker))
    {S₁ S₂ : Type*} [Group S₁] [Group S₂] [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (h₁ : Nat.card S₁ = 60) (h₂ : Nat.card S₂ = 60) (e' : Hh.map π ≃* S₁ × S₂) :
    Hh ⊓ π.ker = ⊥ := by
  obtain ⟨e⟩ := oddCore_nonempty_quotient_equiv_map π Hh
  have h := odd_core_trivial_B_of_prod (ρ.comp Hh.subtype) (hρ.comp Hh.subtype_injective) hperf
    (π.ker.subgroupOf Hh) (oddCore_odd_card_subgroupOf π.ker Hh hodd) h₁ h₂ (e.trans e')
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx.1⟩ : Hh) ∈ π.ker.subgroupOf Hh := hx.2
  rw [h, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

end CFSG.OddStandard.Seitz77
