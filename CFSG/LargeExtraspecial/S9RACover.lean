module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.LargeExtraspecial.S9

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem apply_eq_zero_of_mem_span {f : LinearMap.BilinForm (ZMod 2) V} {s : Set V}
    (hs : ∀ c ∈ s, ∀ c' ∈ s, f c c' = 0) {x y : V} (hx : x ∈ Submodule.span (ZMod 2) s)
    (hy : y ∈ Submodule.span (ZMod 2) s) : f x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hs x hx y hy
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [map_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

variable [FiniteDimensional (ZMod 2) V]

theorem finrank_le_two_of_isotropic {f : LinearMap.BilinForm (ZMod 2) V} (hf : f.Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) {T : Submodule (ZMod 2) V}
    (hT : ∀ x ∈ T, ∀ y ∈ T, f x y = 0) : finrank (ZMod 2) T ≤ 2 := by
  have hle : T ≤ f.orthogonal T := fun y hy x hx => hT x hx y hy
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hf T
  have h3 := Submodule.finrank_le T
  omega

theorem card_le_three_of_orthogonal {f : LinearMap.BilinForm (ZMod 2) V} (hf : f.Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) {s : Finset V} (hs0 : (0 : V) ∉ s)
    (hs : ∀ c ∈ s, ∀ c' ∈ s, f c c' = 0) : s.card ≤ 3 := by
  classical
  set T := Submodule.span (ZMod 2) (s : Set V) with hT
  have hTiso : ∀ x ∈ T, ∀ y ∈ T, f x y = 0 := fun x hx y hy =>
    apply_eq_zero_of_mem_span (fun c hc c' hc' => hs c hc c' hc') hx hy
  have hdim := finrank_le_two_of_isotropic hf hV hTiso
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype T := Fintype.ofFinite T
  have hcardT : Fintype.card T ≤ 4 := by
    rw [← Nat.card_eq_fintype_card, ← FiniteField.pow_finrank_eq_natCard 2]
    calc 2 ^ finrank (ZMod 2) T ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdim
      _ = 4 := by norm_num
  have hsub : ∀ x ∈ insert (0 : V) s, x ∈ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_mem T
    · exact Submodule.subset_span hx
  have hinj := Finset.card_le_card_of_injOn (s := insert (0 : V) s) (t := (Finset.univ : Finset T))
    (fun x => if h : x ∈ T then (⟨x, h⟩ : T) else 0) (fun _ _ => Finset.mem_univ _)
    (by
      intro x hx y hy hxy
      simp only [hsub x hx, hsub y hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val hxy)
  rw [Finset.card_insert_of_notMem hs0, Finset.card_univ] at hinj
  omega

theorem card_filter_ne_zero_of_finrank_two {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    [Fintype Z] [DecidableEq Z] (D : Submodule (ZMod 2) Z) [DecidablePred (· ∈ D)]
    (hD : finrank (ZMod 2) D = 2) :
    ((Finset.univ : Finset Z).filter (fun w => w ≠ 0 ∧ w ∈ D)).card = 3 := by
  have hcard : Nat.card D = 4 := by
    rw [← FiniteField.pow_finrank_eq_natCard 2, hD]
    norm_num
  have e1 : ((Finset.univ : Finset Z).filter (fun w => w ∈ D)).card = 4 := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e2 : (Finset.univ : Finset Z).filter (fun w => w ∈ D) =
      insert 0 ((Finset.univ : Finset Z).filter (fun w => w ≠ 0 ∧ w ∈ D)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hw
      by_cases h0 : w = 0
      · exact Or.inl h0
      · exact Or.inr ⟨h0, hw⟩
    · rintro (rfl | ⟨-, hw⟩)
      · exact zero_mem D
      · exact hw
  rw [e2, Finset.card_insert_of_notMem (by simp)] at e1
  omega

theorem exists_mem_of_cover {f : LinearMap.BilinForm (ZMod 2) V} (hf : f.Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) {Z : Type*} [AddCommGroup Z]
    [Module (ZMod 2) Z] [FiniteDimensional (ZMod 2) Z] (hZ : finrank (ZMod 2) Z = 4)
    (D : V → Submodule (ZMod 2) Z) (hD : ∀ c, c ≠ 0 → finrank (ZMod 2) (D c) = 2)
    (hDD : ∀ c c', f c c' = 1 → D c ⊓ D c' = ⊥) (z : Z) : ∃ c, c ≠ 0 ∧ z ∈ D c := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite Z := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  have : Fintype Z := Fintype.ofFinite Z
  have hcardV : Fintype.card V = 16 := by
    rw [← Nat.card_eq_fintype_card, ← FiniteField.pow_finrank_eq_natCard 2, hV]
    norm_num
  have hcardZ : Fintype.card Z = 16 := by
    rw [← Nat.card_eq_fintype_card, ← FiniteField.pow_finrank_eq_natCard 2, hZ]
    norm_num
  by_cases hz : z = 0
  · obtain ⟨c, hc⟩ : ∃ c : V, c ≠ 0 := by
      by_contra h
      push Not at h
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [h a, h b]
      omega
    exact ⟨c, hc, hz ▸ zero_mem _⟩
  by_contra hno
  push Not at hno
  set P := (Finset.univ : Finset V).filter (fun c => c ≠ 0) with hP
  set Zs := (Finset.univ : Finset Z).filter (fun w => w ≠ 0) with hZs
  have hPcard : P.card = 15 := by
    have e : P = (Finset.univ : Finset V).erase 0 := by
      ext c; simp [hP, and_comm]
    rw [e, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardV]
  have hZcard : Zs.card = 15 := by
    have e : Zs = (Finset.univ : Finset Z).erase 0 := by
      ext c; simp [hZs, and_comm]
    rw [e, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardZ]
  have hsum : ∑ c ∈ P, (Zs.filter (fun w => w ∈ D c)).card =
      ∑ w ∈ Zs, (P.filter (fun c => w ∈ D c)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hleft : ∑ c ∈ P, (Zs.filter (fun w => w ∈ D c)).card = 45 := by
    rw [Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const, hPcard, smul_eq_mul]
    intro c hc
    rw [hP, Finset.mem_filter] at hc
    rw [← card_filter_ne_zero_of_finrank_two (D c) (hD c hc.2), hZs, Finset.filter_filter]
  have hright : ∀ w ∈ Zs, (P.filter (fun c => w ∈ D c)).card ≤ 3 := by
    intro w hw
    rw [hZs, Finset.mem_filter] at hw
    refine card_le_three_of_orthogonal hf hV ?_ ?_
    · simp [hP]
    · intro c hc c' hc'
      rw [Finset.mem_filter] at hc hc'
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (f c c') with h0 | h1
      · exact h0
      · have := hDD c c' h1
        have hmem : w ∈ D c ⊓ D c' := ⟨hc.2, hc'.2⟩
        rw [this, Submodule.mem_bot] at hmem
        exact absurd hmem hw.2
  have hzero : (P.filter (fun c => z ∈ D c)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc
    rw [hP, Finset.mem_filter] at hc
    exact hno c hc.2
  have hzZ : z ∈ Zs := by simp [hZs, hz]
  have hle : ∑ w ∈ Zs, (P.filter (fun c => w ∈ D c)).card ≤ ∑ w ∈ Zs.erase z, 3 := by
    rw [← Finset.add_sum_erase _ _ hzZ, hzero, zero_add]
    exact Finset.sum_le_sum fun w hw => hright w (Finset.mem_of_mem_erase hw)
  rw [Finset.sum_const, Finset.card_erase_of_mem hzZ, hZcard, smul_eq_mul] at hle
  omega

end CFSG.LargeExtraspecial.S9
