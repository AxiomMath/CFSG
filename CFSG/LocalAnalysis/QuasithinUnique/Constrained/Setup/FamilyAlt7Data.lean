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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAlt7Pack

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Equiv Equiv.Perm MulAction
open scoped Pointwise

def a7 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

def b7 : Perm (Fin 7) := swap 0 2 * swap 4 5

def e7 : Finset (Perm (Fin 7)) :=
  {1, a7, b7, a7 * a7, a7 * b7, b7 * a7, a7 * a7 * a7, b7 * a7 * a7}

theorem e7_card : e7.card = 8 := by decide

set_option maxRecDepth 100000 in
theorem e7_mul : ∀ x ∈ e7, ∀ y ∈ e7, x * y ∈ e7 := by
  have hm : ∀ u, u ∈ e7 ↔
      u ∈ [1, a7, b7, a7 * a7, a7 * b7, b7 * a7, a7 * a7 * a7, b7 * a7 * a7] := by
    intro u
    simp [e7]
  intro x hx y hy
  rw [hm] at hx hy ⊢
  exact (FamilyAlt7Pack.e7_closed_of a7 b7 rfl rfl).2.1 x hx y hy

set_option maxRecDepth 100000 in
theorem e7_inv : ∀ x ∈ e7, x⁻¹ ∈ e7 := by
  have hm : ∀ u, u ∈ e7 ↔
      u ∈ [1, a7, b7, a7 * a7, a7 * b7, b7 * a7, a7 * a7 * a7, b7 * a7 * a7] := by
    intro u
    simp [e7]
  intro x hx
  rw [hm] at hx ⊢
  exact (FamilyAlt7Pack.e7_closed_of a7 b7 rfl rfl).2.2 x hx

theorem a7_even : a7 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  simp [a7, Equiv.Perm.sign_mul]

theorem b7_even : b7 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  simp [b7, Equiv.Perm.sign_mul]

def U7 : Subgroup (Perm (Fin 7)) where
  carrier := ↑e7
  mul_mem' := fun {x y} hx hy => by
    exact_mod_cast e7_mul x (by exact_mod_cast hx) y (by exact_mod_cast hy)
  one_mem' := by simp [e7]
  inv_mem' := fun {x} hx => by exact_mod_cast e7_inv x (by exact_mod_cast hx)

theorem U7_le_alt : U7 ≤ alternatingGroup (Fin 7) := by
  intro x hx
  have hx' : x ∈ e7 := hx
  simp only [e7, Finset.mem_insert, Finset.mem_singleton] at hx'
  have ha := a7_even
  have hb := b7_even
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact ha
  · exact hb
  · exact mul_mem ha ha
  · exact mul_mem ha hb
  · exact mul_mem hb ha
  · exact mul_mem (mul_mem ha ha) ha
  · exact mul_mem (mul_mem hb ha) ha

theorem card_U7 : Nat.card U7 = 8 := by
  have h1 : Nat.card U7 = Nat.card (e7 : Set (Perm (Fin 7))) := Nat.card_congr (Equiv.refl _)
  rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset, e7_card]

def orb7 (x : Fin 7) : Finset (Fin 7) := e7.image fun u => u x

set_option maxRecDepth 100000 in
theorem fix_e7 : ∀ x : Fin 7, (∀ u ∈ e7, u x = x) → x = 6 := by
  have ha : ∀ x : Fin 7, a7 x = x → x = 6 := by decide +kernel
  intro x h
  exact ha x (h a7 (by simp [e7]))

set_option maxRecDepth 100000 in
theorem fix_e7' : ∀ u ∈ e7, u 6 = 6 := by
  intro u hu
  exact FamilyAlt7Pack.e7_fix6_of a7 b7 rfl rfl u (by simpa [e7] using hu)

set_option maxRecDepth 100000 in
theorem orb7_zero : orb7 0 = {0, 1, 2, 3} := by decide +kernel

set_option maxRecDepth 100000 in
theorem orb7_card : ∀ x : Fin 7, (orb7 x).card = 4 → x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem orb7_of_mem : ∀ x ∈ ({0, 1, 2, 3} : Finset (Fin 7)), orb7 x = {0, 1, 2, 3} := by
  decide +kernel

theorem normalizer_e7 (σ : Perm (Fin 7)) (h1 : ∀ u ∈ e7, σ * u * σ⁻¹ ∈ e7)
    (h2 : ∀ u ∈ e7, σ⁻¹ * u * σ ∈ e7) :
    σ 6 = 6 ∧ ∀ x : Fin 7, x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) →
      σ x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
  constructor
  · apply fix_e7
    intro v hv
    have := fix_e7' _ (h2 v hv)
    simpa [Perm.mul_apply] using congrArg σ this
  · have horb : ∀ x, orb7 (σ x) = (orb7 x).image σ := by
      intro x
      ext y
      simp only [orb7, Finset.mem_image]
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨(σ⁻¹ * u * σ) x, ⟨σ⁻¹ * u * σ, h2 u hu, rfl⟩, ?_⟩
        simp [Perm.mul_apply]
      · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨σ * u * σ⁻¹, h1 u hu, ?_⟩
        simp [Perm.mul_apply]
    have h0 : σ 0 ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
      apply orb7_card
      rw [horb, Finset.card_image_of_injective _ σ.injective, orb7_zero]
      decide
    intro x hx
    have : σ x ∈ orb7 (σ 0) := by
      rw [horb, orb7_zero]
      exact Finset.mem_image_of_mem σ hx
    rwa [orb7_of_mem _ h0] at this

abbrev Alt7 : Type := alternatingGroup (Fin 7)

def Q71 : Subgroup Alt7 := stabilizer Alt7 ({6} : Set (Fin 7))

def Q72 : Subgroup Alt7 := stabilizer Alt7 (↑({0, 1, 2, 3} : Finset (Fin 7)) : Set (Fin 7))

theorem mem_Q71 (g : Alt7) : g ∈ Q71 ↔ (g : Perm (Fin 7)) 6 = 6 := by
  unfold Q71
  rw [MulAction.mem_stabilizer_set]
  constructor
  · intro h
    exact (h 6).2 rfl
  · intro h b
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hb
      have : (g : Perm (Fin 7)) b = (g : Perm (Fin 7)) 6 := by rw [h]; exact hb
      exact (g : Perm (Fin 7)).injective this
    · intro hb; rw [hb]; exact h

theorem mem_Q72 (g : Alt7) : g ∈ Q72 ↔
    ∀ x : Fin 7, (g : Perm (Fin 7)) x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) ↔
      x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
  unfold Q72
  rw [MulAction.mem_stabilizer_set]
  simp only [Finset.mem_coe]
  rfl

theorem Q71_coatom : IsCoatom Q71 := by
  refine alternatingGroup.isCoatom_stabilizer (by simp) (by simp) ?_
  simp

def c012 : Alt7 := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

def c263 : Alt7 := ⟨swap 2 6 * swap 6 3, by rw [mem_alternatingGroup]; decide⟩

def c245 : Alt7 := ⟨swap 2 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩

def c456 : Alt7 := ⟨swap 4 5 * swap 5 6, by rw [mem_alternatingGroup]; decide⟩

theorem Q71_not_normal : ¬ Q71.Normal := by
  intro h
  have hq : c012 ∈ Q71 := (mem_Q71 _).2 (by decide)
  have := h.conj_mem _ hq c263
  have := (mem_Q71 _).1 this
  revert this
  decide

theorem Q72_not_normal : ¬ Q72.Normal := by
  intro h
  have hq : c012 ∈ Q72 := (mem_Q72 _).2 (by decide)
  have := h.conj_mem _ hq c245
  have := (mem_Q72 _).1 this 1
  revert this
  decide

theorem Q71_sup_Q72 : Q71 ⊔ Q72 = ⊤ := by
  have hnle : ¬ Q72 ≤ Q71 := by
    intro hle
    have hmem : c456 ∈ Q72 := (mem_Q72 _).2 (by decide)
    have := (mem_Q71 _).1 (hle hmem)
    revert this
    decide
  refine Q71_coatom.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle ?_)
  rw [h]
  exact le_sup_right

def U7' : Subgroup Alt7 := U7.subgroupOf (alternatingGroup (Fin 7))

theorem mem_U7' (g : Alt7) : g ∈ U7' ↔ (g : Perm (Fin 7)) ∈ e7 := Iff.rfl

theorem card_U7' : Nat.card U7' = 8 := by
  rw [← card_U7]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe U7_le_alt).toEquiv

theorem card_Alt7 : Nat.card Alt7 = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem isPGroup_U7' : IsPGroup 2 U7' := IsPGroup.of_card (n := 3) (by rw [card_U7']; norm_num)

theorem index_U7' : U7'.index = 315 := by
  have h := Subgroup.card_mul_index U7'
  rw [card_U7', card_Alt7] at h
  omega

theorem inv_of_conj (α : MulAut Alt7) (σ : Perm (Fin 7))
    (hσ : ∀ g : Alt7, (α g : Perm (Fin 7)) = σ * (g : Perm (Fin 7)) * σ⁻¹)
    (hU : U7'.map α.toMonoidHom = U7') :
    Q71.map α.toMonoidHom = Q71 ∧ Q72.map α.toMonoidHom = Q72 := by
  have hmem : ∀ u : Perm (Fin 7), u ∈ e7 → u ∈ alternatingGroup (Fin 7) := fun u hu =>
    U7_le_alt (show u ∈ U7 from hu)
  have h1 : ∀ u ∈ e7, σ * u * σ⁻¹ ∈ e7 := by
    intro u hu
    have hx : (⟨u, hmem u hu⟩ : Alt7) ∈ U7' := (mem_U7' _).2 hu
    have hy : α ⟨u, hmem u hu⟩ ∈ U7'.map α.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [hU, mem_U7', hσ] at hy
    exact hy
  have h2 : ∀ u ∈ e7, σ⁻¹ * u * σ ∈ e7 := by
    intro u hu
    have hx : (⟨u, hmem u hu⟩ : Alt7) ∈ U7' := (mem_U7' _).2 hu
    rw [← hU] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h3 := congrArg (fun z : Alt7 => (z : Perm (Fin 7))) hyx
    simp only [MulEquiv.coe_toMonoidHom] at h3
    rw [hσ] at h3
    have h4 : (y : Perm (Fin 7)) = σ⁻¹ * u * σ := by
      rw [← h3]; group
    rw [← h4]
    exact (mem_U7' y).1 hy
  obtain ⟨h6, h4⟩ := normalizer_e7 σ h1 h2
  have h6' : σ⁻¹ 6 = 6 := by rw [Perm.inv_eq_iff_eq]; exact h6.symm
  have hS4 : ∀ x, σ x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) ↔
      x ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
    intro x
    refine ⟨fun hx => ?_, h4 x⟩
    have hsub : ({0, 1, 2, 3} : Finset (Fin 7)).image σ ⊆ ({0, 1, 2, 3} : Finset (Fin 7)) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact h4 z hz
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ σ.injective])
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 hx
    rwa [← σ.injective hzx]
  have hfin : ∀ Q : Subgroup Alt7, Q.map α.toMonoidHom ≤ Q → Q.map α.toMonoidHom = Q := by
    intro Q hle
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
  refine ⟨hfin _ ?_, hfin _ ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Q71 := hg
    rw [mem_Q71] at hg'
    show α g ∈ Q71
    rw [mem_Q71]
    have : (α g : Perm (Fin 7)) 6 = σ ((g : Perm (Fin 7)) (σ⁻¹ 6)) := by
      rw [hσ]; simp [Perm.mul_apply]
    rw [this, h6', hg', h6]
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Q72 := hg
    rw [mem_Q72] at hg'
    show α g ∈ Q72
    rw [mem_Q72]
    intro x
    have : (α g : Perm (Fin 7)) x = σ ((g : Perm (Fin 7)) (σ⁻¹ x)) := by
      rw [hσ]; simp [Perm.mul_apply]
    rw [this, hS4, hg']
    have h5 := hS4 (σ⁻¹ x)
    have h7 : σ (σ⁻¹ x) = x := by simp
    rw [h7] at h5
    exact h5.symm

end CFSG.QuasithinUnique.Setup.Family
