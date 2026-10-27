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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.LargeExtraspecial.S14

open Subgroup

theorem eq_bot_of_perfect_perm_three {P : Subgroup (Equiv.Perm (Fin 3))} (hP : ⁅P, P⁆ = P) :
    P = ⊥ := by
  have hA : ⁅P, P⁆ ≤ alternatingGroup (Fin 3) :=
    (commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ))
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    have h := two_mul_card_alternatingGroup (α := Fin 3)
    rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card] at h
    generalize Nat.card (alternatingGroup (Fin 3)) = n at h ⊢
    norm_num [Nat.factorial] at h
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card h3
  have hcomm : ∀ x ∈ alternatingGroup (Fin 3), ∀ y ∈ alternatingGroup (Fin 3), x * y = y * x := by
    intro x hx y hy
    have := (IsCyclic.commGroup (α := alternatingGroup (Fin 3))).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hbot : ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact hcomm y (hA hy) x (hA hx)
  rw [hP, hP] at hbot
  exact hbot

theorem exists_of_perm_three_prod {A P : Type*} [Group A] [Group P] {F : Subgroup A}
    (φ : A →* Equiv.Perm (Fin 3) × P) (hφ : Function.Surjective φ) (hker : φ.ker = F)
    {K : Subgroup A} (hK : ⁅K, K⁆ = K) :
    ∃ a : A, a ∉ F ∧ a * a ∈ F ∧ ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ F := by
  set ψ := (MonoidHom.fst (Equiv.Perm (Fin 3)) P).comp φ
  have hKψ : K.map ψ = ⊥ := by
    refine eq_bot_of_perfect_perm_three ?_
    rw [← map_commutator, hK]
  have hk1 : ∀ k ∈ K, (φ k).1 = 1 := fun k hk => by
    have : ψ k ∈ K.map ψ := ⟨k, hk, rfl⟩
    rw [hKψ, mem_bot] at this
    exact this
  obtain ⟨a, ha⟩ := hφ (Equiv.swap 0 1, 1)
  refine ⟨a, ?_, ?_, fun k hk => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ha]
    intro h
    have h1 := congrArg (fun p => (p.1 : Equiv.Perm (Fin 3)) 0) h
    simp at h1
  · rw [← hker, MonoidHom.mem_ker, map_mul, ha]
    ext <;> simp
  · rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, ha]
    ext <;> simp [hk1 k hk]

theorem ker_mulEquiv_comp {A X B : Type*} [Group A] [Group X] [Group B] (φ : A →* X)
    (e : X ≃* B) : (e.toMonoidHom.comp φ).ker = φ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

end CFSG.LargeExtraspecial.S14
