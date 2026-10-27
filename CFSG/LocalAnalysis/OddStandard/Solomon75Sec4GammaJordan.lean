module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup

section AltStar

variable {α : Type*} [DecidableEq α]

lemma altStar_cyc_apply_a {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap a c) a = c := by
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]

lemma altStar_cyc_apply_c (a b c : α) :
    (swap a b * swap a c) c = b := by
  rw [Perm.mul_apply, swap_apply_right, swap_apply_left]

lemma altStar_cyc_apply_other {a b c d : α} (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) :
    (swap a b * swap a c) d = d := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb]

omit [DecidableEq α] in
open scoped Pointwise in
lemma altStar_block_map_mem (H : Subgroup (Perm α)) {B : Set α} (hB : MulAction.IsBlock ↥H B)
    {g : Perm α} (hg : g ∈ H) {b : α} (hb : b ∈ B) (hgb : g b ∈ B) {b' : α} (hb' : b' ∈ B) :
    g b' ∈ B := by
  have h1 : (⟨g, hg⟩ : ↥H) • B = B := hB.smul_eq_of_mem hb hgb
  have h2 : (⟨g, hg⟩ : ↥H) • b' ∈ (⟨g, hg⟩ : ↥H) • B := Set.smul_mem_smul_set hb'
  rw [h1] at h2
  exact h2

lemma altStar_key (H : Subgroup (Perm α)) {ι : Type*} (F : ι → Finset α)
    (h3 : ∀ i, 3 ≤ (F i).card)
    (hH : ∀ (i : ι) (a b c : α), a ∈ F i → b ∈ F i → c ∈ F i → a ≠ b → a ≠ c → b ≠ c →
      swap a b * swap a c ∈ H)
    {B : Set α} (hB : MulAction.IsBlock ↥H B) (hns : ¬ B.Subsingleton)
    {i : ι} {x y : α} (hx : x ∈ B) (hxF : x ∈ F i) (hyF : y ∈ F i) : y ∈ B := by
  by_cases hyx : y = x
  · exact hyx ▸ hx
  obtain ⟨z, hzF, hz⟩ : ∃ z, z ∈ F i ∧ z ∉ ({x, y} : Finset α) :=
    Finset.exists_mem_notMem_of_card_lt_card (Finset.card_le_two.trans_lt (h3 i))
  have hzx : z ≠ x := fun h => hz (by simp [h])
  have hzy : z ≠ y := fun h => hz (by simp [h])
  have hc : swap x y * swap x z ∈ H := hH i x y z hxF hyF hzF (Ne.symm hyx) hzx.symm hzy.symm
  have hcx : (swap x y * swap x z) x = z := altStar_cyc_apply_a hzx.symm hzy.symm
  have hcz : (swap x y * swap x z) z = y := altStar_cyc_apply_c x y z
  obtain ⟨b', hb', hb'x⟩ := (Set.not_subsingleton_iff.mp hns).exists_ne x
  by_cases hb'y : b' = y
  · exact hb'y ▸ hb'
  have hzB : z ∈ B := by
    by_cases hb'z : b' = z
    · exact hb'z ▸ hb'
    · have hfix : (swap x y * swap x z) b' = b' := altStar_cyc_apply_other hb'x hb'y hb'z
      have := altStar_block_map_mem H hB hc hb' (by rw [hfix]; exact hb') hx
      rwa [hcx] at this
  have := altStar_block_map_mem H hB hc hx (by rw [hcx]; exact hzB) hzB
  rwa [hcz] at this

end AltStar

theorem alt_le_of_star {α : Type*} [Fintype α] [DecidableEq α] (H : Subgroup (Perm α)) (w₀ : α)
    {ι : Type*} (F : ι → Finset α) (h3 : ∀ i, 3 ≤ (F i).card)
    (hH : ∀ (i : ι) (a b c : α), a ∈ F i → b ∈ F i → c ∈ F i → a ≠ b → a ≠ c → b ≠ c →
      swap a b * swap a c ∈ H)
    (hstar : ∀ x : α, ∃ i, x ∈ F i ∧ w₀ ∈ F i) :
    alternatingGroup α ≤ H := by
  have hpre : MulAction.IsPretransitive ↥H α := by
    rw [MulAction.isPretransitive_iff_base w₀]
    intro x
    by_cases hx : x = w₀
    · exact ⟨1, by simp [hx]⟩
    · obtain ⟨i, hxF, hwF⟩ := hstar x
      obtain ⟨z, hzF, hz⟩ : ∃ z, z ∈ F i ∧ z ∉ ({x, w₀} : Finset α) :=
        Finset.exists_mem_notMem_of_card_lt_card (Finset.card_le_two.trans_lt (h3 i))
      have hzx : z ≠ x := fun h => hz (by simp [h])
      have hzw : z ≠ w₀ := fun h => hz (by simp [h])
      refine ⟨⟨swap w₀ z * swap w₀ x, hH i w₀ z x hwF hzF hxF hzw.symm (Ne.symm hx) hzx⟩, ?_⟩
      exact altStar_cyc_apply_a (Ne.symm hx) hzx
  have hprim : MulAction.IsPreprimitive ↥H α := by
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base w₀ ?_
    intro B hwB hB
    by_cases hns : B.Subsingleton
    · exact Or.inl hns
    · refine Or.inr (Set.eq_univ_of_forall fun x => ?_)
      obtain ⟨i, hxF, hwF⟩ := hstar x
      exact altStar_key H F h3 hH hB hns hwB hwF hxF
  obtain ⟨i₀, -, -⟩ := hstar w₀
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (h3 i₀)
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (isThreeCycle_swap_mul_swap_same hab hac hbc) (hH i₀ a b c ha hb hc hab hac hbc)

end CFSG.OddStandard.Solomon75.AhatData
