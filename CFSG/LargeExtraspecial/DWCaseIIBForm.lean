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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.DW

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

structure IsHypFamily (U : Submodule (ZMod 2) V) (H : V → Submodule (ZMod 2) V) : Prop where
  mem : ∀ c ∈ U, c ≠ 0 → c ∈ H c
  ne : ∀ c ∈ U, c ≠ 0 → ∃ u ∈ U, u ∉ H c
  add : ∀ c ∈ U, c ≠ 0 → ∀ u ∈ U, ∀ u' ∈ U, u ∉ H c → u' ∉ H c → u + u' ∈ H c
  symm : ∀ c ∈ U, ∀ c' ∈ U, c ≠ 0 → c' ≠ 0 → (c' ∈ H c ↔ c ∈ H c')

open Classical in
@[expose] noncomputable def hypFun (H : V → Submodule (ZMod 2) V) (u v : V) : ZMod 2 :=
  if v = 0 ∨ u ∈ H v then 0 else 1

variable {U : Submodule (ZMod 2) V} {H : V → Submodule (ZMod 2) V}

theorem hypFun_eq_zero_iff {u v : V} (hv : v ≠ 0) : hypFun H u v = 0 ↔ u ∈ H v := by
  unfold hypFun
  split_ifs with h
  · exact ⟨fun _ => h.resolve_left hv, fun _ => rfl⟩
  · push Not at h
    exact ⟨fun h1 => absurd h1 one_ne_zero, fun h1 => absurd h1 h.2⟩

theorem hypFun_eq_one_iff {u v : V} : hypFun H u v = 1 ↔ v ≠ 0 ∧ u ∉ H v := by
  unfold hypFun
  split_ifs with h
  · constructor
    · intro h1
      exact absurd h1 zero_ne_one
    · rintro ⟨h1, h2⟩
      exact absurd (h.resolve_left h1) h2
  · push Not at h
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem hypFun_zero_right (u : V) : hypFun H u 0 = 0 := by
  unfold hypFun
  simp

theorem hypFun_zero_left (v : V) : hypFun H 0 v = 0 := by
  unfold hypFun
  simp [(H v).zero_mem]

theorem hypFun_apply_apply (f : V →ₗ[ZMod 2] V) (hf0 : ∀ v ∈ U, v ≠ 0 → f v ≠ 0)
    (hf : ∀ u ∈ U, ∀ v ∈ U, v ≠ 0 → (u ∈ H v ↔ f u ∈ H (f v))) {u v : V} (hu : u ∈ U)
    (hv : v ∈ U) : hypFun H (f u) (f v) = hypFun H u v := by
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, hypFun_zero_right, hypFun_zero_right]
  rcases zmod2_dichotomy (hypFun H u v) with e | e
  · rw [e, hypFun_eq_zero_iff (hf0 v hv hv0), ← hf u hu v hv hv0]
    exact (hypFun_eq_zero_iff hv0).mp e
  · rw [e, hypFun_eq_one_iff]
    exact ⟨hf0 v hv hv0, fun e' => (hypFun_eq_one_iff.mp e).2 ((hf u hu v hv hv0).mpr e')⟩

namespace IsHypFamily

variable (h : IsHypFamily U H)
include h

theorem hypFun_add_left {u u' v : V} (hu : u ∈ U) (hu' : u' ∈ U) (hv : v ∈ U) :
    hypFun H (u + u') v = hypFun H u v + hypFun H u' v := by
  by_cases hv0 : v = 0
  · subst hv0
    simp [hypFun_zero_right]
  have key0 : ∀ w : V, w ∈ H v → hypFun H w v = 0 := fun w hw =>
    (hypFun_eq_zero_iff hv0).mpr hw
  have key1 : ∀ w : V, w ∉ H v → hypFun H w v = 1 := fun w hw =>
    hypFun_eq_one_iff.mpr ⟨hv0, hw⟩
  by_cases h1 : u ∈ H v <;> by_cases h2 : u' ∈ H v
  · rw [key0 _ (add_mem h1 h2), key0 _ h1, key0 _ h2, add_zero]
  · have h3 : u + u' ∉ H v := fun h3 => h2 (by simpa using sub_mem h3 h1)
    rw [key1 _ h3, key0 _ h1, key1 _ h2, zero_add]
  · have h3 : u + u' ∉ H v := fun h3 => h1 (by simpa using sub_mem h3 h2)
    rw [key1 _ h3, key1 _ h1, key0 _ h2, add_zero]
  · rw [key0 _ (h.add v hv hv0 u hu u' hu' h1 h2), key1 _ h1, key1 _ h2]
    decide

theorem hypFun_symm {u v : V} (hu : u ∈ U) (hv : v ∈ U) : hypFun H u v = hypFun H v u := by
  by_cases hu0 : u = 0
  · subst hu0
    rw [hypFun_zero_left, hypFun_zero_right]
  by_cases hv0 : v = 0
  · subst hv0
    rw [hypFun_zero_left, hypFun_zero_right]
  rcases zmod2_dichotomy (hypFun H u v) with e | e <;> rw [e]
  · rw [hypFun_eq_zero_iff hv0] at e
    exact ((hypFun_eq_zero_iff hu0).mpr ((h.symm v hv u hu hv0 hu0).mp e)).symm
  · obtain ⟨-, e⟩ := hypFun_eq_one_iff.mp e
    exact (hypFun_eq_one_iff.mpr ⟨hu0, fun e' => e ((h.symm v hv u hu hv0 hu0).mpr e')⟩).symm

@[expose] noncomputable def form : LinearMap.BilinForm (ZMod 2) U :=
  LinearMap.mk₂ (ZMod 2) (fun u v => hypFun H (u : V) (v : V))
    (fun u u' v => h.hypFun_add_left u.2 u'.2 v.2)
    (fun c u v => by
      rcases zmod2_dichotomy c with rfl | rfl
      · simp [hypFun_zero_left]
      · simp)
    (fun u v v' => by
      change hypFun H u (v + v') = hypFun H u v + hypFun H u v'
      rw [h.hypFun_symm u.2 (add_mem v.2 v'.2), h.hypFun_add_left v.2 v'.2 u.2,
        h.hypFun_symm v.2 u.2, h.hypFun_symm v'.2 u.2])
    (fun c u v => by
      rcases zmod2_dichotomy c with rfl | rfl
      · simp [hypFun_zero_right]
      · simp)

theorem form_apply (u v : U) : h.form u v = hypFun H (u : V) (v : V) := rfl

theorem form_eq_zero_iff (u : U) {v : U} (hv : (v : V) ≠ 0) :
    h.form u v = 0 ↔ (u : V) ∈ H v :=
  hypFun_eq_zero_iff hv

theorem form_isAlt : h.form.IsAlt := fun v => by
  rw [form_apply]
  by_cases hv : (v : V) = 0
  · rw [hv, hypFun_zero_right]
  · exact (hypFun_eq_zero_iff hv).mpr (h.mem v v.2 hv)

theorem form_separating (u : U) (hu : ∀ v : U, h.form u v = 0) : u = 0 := by
  by_contra hu0
  have hu0' : (u : V) ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨w, hwU, hw⟩ := h.ne u u.2 hu0'
  have hw0 : w ≠ 0 := fun e => hw (e ▸ (H u).zero_mem)
  have h1 := hu ⟨w, hwU⟩
  rw [form_apply, hypFun_eq_zero_iff hw0] at h1
  exact hw ((h.symm w hwU u u.2 hw0 hu0').mp h1)

theorem form_nondegenerate : h.form.Nondegenerate :=
  ⟨fun u hu => h.form_separating u hu, fun v hv => h.form_separating v fun u => by
    rw [form_apply, h.hypFun_symm v.2 u.2]
    exact hv u⟩

end IsHypFamily

theorem add_mem_of_finrank_add_one [FiniteDimensional (ZMod 2) V] {S : Submodule (ZMod 2) V}
    (hSU : S ≤ U) (hdim : finrank (ZMod 2) S + 1 = finrank (ZMod 2) U) {u u' : V} (hu : u ∈ U)
    (hu' : u' ∈ U) (huS : u ∉ S) (hu'S : u' ∉ S) : u + u' ∈ S := by
  have hu0 : u ≠ 0 := fun e => huS (e ▸ S.zero_mem)
  have h1 : S ⊔ ZMod 2 ∙ u = U := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hSU ((Submodule.span_singleton_le_iff_mem
      _ _).mpr hu)) ?_
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq S (ZMod 2 ∙ u)
    have h3 : S ⊓ ZMod 2 ∙ u = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvS, hv⟩
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rcases zmod2_dichotomy μ with rfl | rfl
      · rw [zero_smul]
        exact zero_mem _
      · rw [one_smul] at hvS
        exact absurd hvS huS
    rw [h3, finrank_bot, add_zero, finrank_span_singleton hu0] at h2
    omega
  have hu'' : u' ∈ S ⊔ ZMod 2 ∙ u := by rw [h1]; exact hu'
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hu''
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases zmod2_dichotomy μ with rfl | rfl
  · rw [zero_smul, add_zero] at hu'S
    exact absurd hs hu'S
  · rw [one_smul, add_comm s u, ← add_assoc, ZModModule.add_self, zero_add]
    exact hs

end CFSG.LargeExtraspecial.DW
