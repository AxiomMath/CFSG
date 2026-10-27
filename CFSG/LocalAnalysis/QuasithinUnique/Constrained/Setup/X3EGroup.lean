module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EData
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
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.QuasithinUnique.Setup.X3E

open Equiv CFSG.QuasithinUnique.A6Facts

abbrev S6 : Type := alternatingGroup (Fin 6)

@[expose] def gx : S6 := ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def gy : S6 := ⟨c[1, 2, 3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def gen (b : Bool) : S6 := if b then gy else gx

@[expose] def evalG : List Bool → S6
  | [] => 1
  | b :: w => gen b * evalG w

@[expose] def c6 (g : S6) : List ℕ := codeN 6 g.1

theorem c6_mul (g h : S6) : c6 (g * h) = Core.cmul (c6 g) (c6 h) := codeN_mul _ _

theorem c6_one : c6 1 = List.range 6 := codeN_one

theorem c6_injective : Function.Injective c6 := fun _ _ h => Subtype.ext (codeN_injective h)

@[expose] def cgen (b : Bool) : List ℕ := if b then [0, 2, 3, 4, 5, 1] else [1, 2, 0, 3, 4, 5]

theorem c6_gen (b : Bool) : c6 (gen b) = cgen b := by
  cases b <;> decide +kernel

@[expose] def evalC : List Bool → List ℕ
  | [] => List.range 6
  | b :: w => Core.cmul (cgen b) (evalC w)

theorem c6_evalG (w : List Bool) : c6 (evalG w) = evalC w := by
  induction w with
  | nil => exact c6_one
  | cons b w ih => rw [evalG, c6_mul, ih, c6_gen]; rfl

@[expose] def R0list : List S6 := eR0W.map evalG

@[expose] def R0C : List (List ℕ) := eR0W.map evalC

theorem R0list_map : R0list.map c6 = R0C := by
  unfold R0list R0C
  rw [List.map_map]
  exact List.map_congr_left fun w _ => c6_evalG w

theorem mem_R0list_of_code {g : S6} (h : c6 g ∈ R0C) : g ∈ R0list := by
  rw [← R0list_map, List.mem_map] at h
  obtain ⟨r, hr, hrg⟩ := h
  rw [c6_injective hrg] at hr
  exact hr

theorem code_mem_R0C {g : S6} (h : g ∈ R0list) : c6 g ∈ R0C := by
  rw [← R0list_map]; exact List.mem_map_of_mem h

theorem R0C_mul : ∀ a ∈ R0C, ∀ b ∈ R0C, Core.cmul a b ∈ R0C := by decide +kernel

theorem R0C_one : List.range 6 ∈ R0C := by decide +kernel

theorem R0C_inv : ∀ a ∈ R0C, ∃ b ∈ R0C, Core.cmul a b = List.range 6 := by decide +kernel

theorem R0C_nodup : R0C.Nodup := by decide +kernel

theorem R0C_length : R0C.length = 8 := by decide +kernel

@[expose] def R0 : Subgroup S6 where
  carrier := {g | g ∈ R0list}
  mul_mem' := fun {a b} ha hb => by
    apply mem_R0list_of_code
    rw [c6_mul]
    exact R0C_mul _ (code_mem_R0C ha) _ (code_mem_R0C hb)
  one_mem' := by
    apply mem_R0list_of_code
    rw [c6_one]
    exact R0C_one
  inv_mem' := fun {a} ha => by
    obtain ⟨b, hb, hab⟩ := R0C_inv _ (code_mem_R0C ha)
    rw [← R0list_map, List.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have h1 : a * b' = 1 := c6_injective (by rw [c6_mul, hab, c6_one])
    have h2 : a⁻¹ = b' := (eq_inv_of_mul_eq_one_right h1).symm
    show a⁻¹ ∈ R0list
    rw [h2]
    exact hb'

theorem mem_R0 {g : S6} : g ∈ R0 ↔ g ∈ R0list := Iff.rfl

theorem card_R0 : Nat.card R0 = 8 := by
  have h : (R0 : Set S6) = ↑R0list.toFinset := by
    ext g; simp [mem_R0]
  have hnd : R0list.Nodup := by
    have : (R0list.map c6).Nodup := by rw [R0list_map]; exact R0C_nodup
    exact List.Nodup.of_map _ this
  have hlen : R0list.length = 8 := by
    have := congrArg List.length R0list_map
    rw [List.length_map] at this
    rw [this]; exact R0C_length
  rw [show Nat.card R0 = Nat.card (R0 : Set S6) from rfl, Nat.card_coe_set_eq, h,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]

@[expose] def tauOf (b : Bool) (i : ℕ) : ℕ := (if b then eTauY else eTauX).getD i 0

@[expose] def rep (i : ℕ) : S6 := evalG (eRepW.getD i [])

theorem tau_lt : ∀ i : Fin 45, ∀ b : Bool, tauOf b i < 45 := by decide +kernel

theorem rep_zero : rep 0 = 1 := by
  apply c6_injective
  unfold rep
  rw [c6_evalG, c6_one]
  decide +kernel

@[expose] def cosetOK : Bool :=
  (List.range 45).all fun i => [false, true].all fun b =>
    R0C.any fun r => Core.cmul (cgen b) (evalC (eRepW.getD i [])) ==
      Core.cmul (evalC (eRepW.getD (tauOf b i) [])) r

theorem cosetOK_true : cosetOK = true := by decide +kernel

theorem coset_rel (i : ℕ) (hi : i < 45) (b : Bool) :
    (rep (tauOf b i))⁻¹ * gen b * rep i ∈ R0 := by
  have h := cosetOK_true
  unfold cosetOK at h
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨r, hr, hrel⟩ := h i hi b (by simp)
  rw [← R0list_map, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  have h1 : gen b * rep i = rep (tauOf b i) * r' := by
    apply c6_injective
    rw [c6_mul, c6_mul]
    unfold rep
    rw [c6_evalG, c6_evalG, c6_gen]
    exact hrel
  have h2 : (rep (tauOf b i))⁻¹ * gen b * rep i = r' := by
    rw [mul_assoc, h1, inv_mul_cancel_left]
  rw [h2]
  exact hr'

@[expose] def genC : List (List ℕ) := eGenW.map evalC

theorem genC_nodup : genC.Nodup := by decide +kernel

theorem genC_length : genC.length = 360 := by decide +kernel

theorem evalG_mem_closure (w : List Bool) : evalG w ∈ Subgroup.closure ({gx, gy} : Set S6) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    unfold evalG
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (by simp [gen])
    · exact Subgroup.subset_closure (by simp [gen])

theorem card_S6 : Nat.card S6 = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem closure_xy : Subgroup.closure ({gx, gy} : Set S6) = ⊤ := by
  have hnd : (eGenW.map evalG).Nodup := by
    have : ((eGenW.map evalG).map c6).Nodup := by
      rw [List.map_map]
      have : c6 ∘ evalG = evalC := funext c6_evalG
      rw [this]; exact genC_nodup
    exact List.Nodup.of_map _ this
  have hlen : (eGenW.map evalG).length = 360 := by
    rw [List.length_map]
    have := genC_length
    unfold genC at this
    rwa [List.length_map] at this
  apply Subgroup.eq_top_of_le_card
  rw [card_S6]
  have hsub : ((eGenW.map evalG).toFinset : Set S6) ⊆
      (Subgroup.closure ({gx, gy} : Set S6) : Set S6) := by
    intro g hg
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hg
    obtain ⟨w, -, rfl⟩ := hg
    exact evalG_mem_closure w
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen] at this
  calc 360 ≤ _ := this
    _ = Nat.card (Subgroup.closure ({gx, gy} : Set S6)) := (Nat.card_coe_set_eq _).symm

end CFSG.QuasithinUnique.Setup.X3E
