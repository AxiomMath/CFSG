module

public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Equiv

section Rigid

variable {H Q : Type*} [Group H] [Group Q]

theorem not_nonempty_quotient_iso_of_pCore_ne_bot {p : ℕ} (hQ : CFSG.pCore p Q ≠ ⊥) :
    ¬ Nonempty (H ⧸ CFSG.pCore p H ≃* Q) := by
  rintro ⟨f⟩
  apply hQ
  have h1 := CFSG.pCore_map_iso p f.symm
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at h1
  exact Subgroup.map_injective (f := f.symm.toMonoidHom) f.symm.injective
    (h1.trans (Subgroup.map_bot _).symm)

theorem le_pCore_of_normal_pGroup' {G : Type*} [Group G] {p : ℕ} {K : Subgroup G}
    (hK : K.Normal) (hp : IsPGroup p K) : K ≤ CFSG.pCore p G := by
  unfold CFSG.pCore
  exact le_sSup (show K ∈ {K : Subgroup G | K.Normal ∧ IsPGroup p K} from ⟨hK, hp⟩)

end Rigid

section Klein

def kleinFourFinset : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinFourFinset_mul_mem : ∀ x ∈ kleinFourFinset, ∀ y ∈ kleinFourFinset,
    x * y ∈ kleinFourFinset := by
  decide

theorem kleinFourFinset_inv_mem : ∀ x ∈ kleinFourFinset, x⁻¹ ∈ kleinFourFinset := by
  decide

theorem kleinFourFinset_conj_mem : ∀ n ∈ kleinFourFinset, ∀ g : Perm (Fin 4),
    g * n * g⁻¹ ∈ kleinFourFinset := by
  decide

theorem kleinFourFinset_sq : ∀ x ∈ kleinFourFinset, x ^ 2 = 1 := by
  decide

def kleinFour : Subgroup (Perm (Fin 4)) where
  carrier := {x | x ∈ kleinFourFinset}
  mul_mem' hx hy := kleinFourFinset_mul_mem _ hx _ hy
  one_mem' := by
    show (1 : Perm (Fin 4)) ∈ kleinFourFinset
    exact Finset.mem_insert_self _ _
  inv_mem' hx := kleinFourFinset_inv_mem _ hx

theorem kleinFour_normal : kleinFour.Normal :=
  ⟨fun n hn g => kleinFourFinset_conj_mem n (show n ∈ kleinFourFinset from hn) g⟩

theorem kleinFour_isPGroup : IsPGroup 2 kleinFour := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using kleinFourFinset_sq (x : Perm (Fin 4)) (show (x : Perm (Fin 4)) ∈ kleinFourFinset from x.2)

theorem swap_mul_swap_mem_kleinFour :
    swap (0 : Fin 4) 1 * swap 2 3 ∈ kleinFour := by
  show swap (0 : Fin 4) 1 * swap 2 3 ∈ kleinFourFinset
  decide

theorem swap_mul_swap_ne_one : swap (0 : Fin 4) 1 * swap 2 3 ≠ 1 := by
  decide

theorem pCore_two_perm_four_ne_bot : CFSG.pCore 2 (Perm (Fin 4)) ≠ ⊥ := by
  intro h
  have hle := le_pCore_of_normal_pGroup' (p := 2) kleinFour_normal kleinFour_isPGroup
  rw [h] at hle
  exact swap_mul_swap_ne_one (Subgroup.mem_bot.mp (hle swap_mul_swap_mem_kleinFour))

end Klein

section Product

theorem prod_bot_normal {A B : Type*} [Group A] [Group B] (N : Subgroup A) (hN : N.Normal) :
    (N.prod (⊥ : Subgroup B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_prod] at hn ⊢
  have h2 : n.2 = 1 := Subgroup.mem_bot.mp hn.2
  refine ⟨hN.conj_mem _ hn.1 g.1, ?_⟩
  rw [Subgroup.mem_bot]
  simp [h2]

theorem prod_bot_isPGroup {A B : Type*} [Group A] [Group B] (N : Subgroup A)
    (hN2 : IsPGroup 2 N) : IsPGroup 2 (N.prod (⊥ : Subgroup B)) := by
  intro x
  obtain ⟨k, hk⟩ := hN2 ⟨x.1.1, (Subgroup.mem_prod.mp x.2).1⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h2 : x.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp x.2).2
  have h1 : x.1.1 ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  ext
  · simpa using h1
  · simp [h2]

theorem pCore_two_prod_ne_bot {A B : Type*} [Group A] [Group B] (N : Subgroup A)
    (hN : N.Normal) (hN2 : IsPGroup 2 N) (hN1 : N ≠ ⊥) :
    CFSG.pCore 2 (A × B) ≠ ⊥ := by
  intro h
  have hle := le_pCore_of_normal_pGroup' (p := 2) (prod_bot_normal N hN)
    (prod_bot_isPGroup (B := B) N hN2)
  rw [h] at hle
  apply hN1
  rw [eq_bot_iff]
  intro a ha
  have hmem : (a, (1 : B)) ∈ N.prod (⊥ : Subgroup B) :=
    Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem _⟩
  have h1 : ((a, (1 : B)) : A × B) = 1 := Subgroup.mem_bot.mp (hle hmem)
  exact Subgroup.mem_bot.mpr (congrArg Prod.fst h1)

theorem top_isPGroup_perm_two : IsPGroup 2 (⊤ : Subgroup (Perm (Fin 2))) :=
  IsPGroup.of_card (n := 1) (by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl)

theorem pCore_two_perm_two_ne_bot : CFSG.pCore 2 (Perm (Fin 2)) ≠ ⊥ := by
  intro h
  have hle := le_pCore_of_normal_pGroup' (p := 2) (K := (⊤ : Subgroup (Perm (Fin 2))))
    inferInstance (top_isPGroup_perm_two)
  rw [h] at hle
  exact (by decide : swap (0 : Fin 2) 1 ≠ 1)
    (Subgroup.mem_bot.mp (hle (Subgroup.mem_top _)))

theorem pCore_two_perm_prod_ne_bot {r s : ℕ} (hr : r = 2 ∨ r = 4) :
    CFSG.pCore 2 (Perm (Fin r) × Perm (Fin s)) ≠ ⊥ := by
  rcases hr with rfl | rfl
  · refine pCore_two_prod_ne_bot (⊤ : Subgroup (Perm (Fin 2))) inferInstance
      top_isPGroup_perm_two ?_
    intro h
    have hsw : swap (0 : Fin 2) 1 ∈ (⊤ : Subgroup (Perm (Fin 2))) := Subgroup.mem_top _
    rw [h] at hsw
    exact (by decide : swap (0 : Fin 2) 1 ≠ 1) (Subgroup.mem_bot.mp hsw)
  · refine pCore_two_prod_ne_bot kleinFour kleinFour_normal kleinFour_isPGroup ?_
    intro h
    have hsw := swap_mul_swap_mem_kleinFour
    rw [h] at hsw
    exact swap_mul_swap_ne_one (Subgroup.mem_bot.mp hsw)

end Product

section Corollaries

variable {H : Type*} [Group H]

theorem not_nonempty_quotient_perm_prod {r s : ℕ} (hr : r = 2 ∨ r = 4) :
    ¬ Nonempty (H ⧸ CFSG.pCore 2 H ≃* Perm (Fin r) × Perm (Fin s)) :=
  not_nonempty_quotient_iso_of_pCore_ne_bot (pCore_two_perm_prod_ne_bot hr)

theorem not_nonempty_quotient_perm_four :
    ¬ Nonempty (H ⧸ CFSG.pCore 2 H ≃* Perm (Fin 4)) :=
  not_nonempty_quotient_iso_of_pCore_ne_bot pCore_two_perm_four_ne_bot

end Corollaries

end CFSG.HardMathSupport.Cooperstein.Proving

end
