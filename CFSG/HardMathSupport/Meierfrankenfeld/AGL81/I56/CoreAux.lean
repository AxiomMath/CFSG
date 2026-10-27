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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open scoped commutatorElement

section Comm

variable {X : Type*} [Group X]

theorem commutator_le_of_invariant (V K : Subgroup X)
    (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) : ⁅V, K⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv k hk
  have h1 : k * v⁻¹ * k⁻¹ ∈ V := hVK k hk v⁻¹ (V.inv_mem hv)
  have h2 : v * (k * v⁻¹ * k⁻¹) ∈ V := V.mul_mem hv h1
  have h3 : (⁅v, k⁆ : X) = v * (k * v⁻¹ * k⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h3]; exact h2

theorem conj_mem_commutator (V K : Subgroup X) (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (k : X) (hk : k ∈ K) {u : X} (hu : u ∈ ⁅V, K⁆) : k * u * k⁻¹ ∈ ⁅V, K⁆ := by
  have h := Subgroup.map_commutator V K (MulAut.conj k).toMonoidHom
  have hV : V.map (MulAut.conj k).toMonoidHom = V := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hVK k hk y hy
    · intro hx
      refine ⟨k⁻¹ * x * k, ?_, by group⟩
      have := hVK k⁻¹ (K.inv_mem hk) x hx
      simpa using this
  have hK : K.map (MulAut.conj k).toMonoidHom = K := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)
    · intro hx
      refine ⟨k⁻¹ * x * k, ?_, by group⟩
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
  rw [hV, hK] at h
  rw [← h]
  exact ⟨u, hu, by simp⟩

end Comm

open Equiv Equiv.Perm
open scoped commutatorElement in
theorem alt_eight_perfect :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 8))), (⊤ : Subgroup (alternatingGroup (Fin 8)))⁆ = ⊤ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hN : (⁅(⊤ : Subgroup (alternatingGroup (Fin 8))),
      (⊤ : Subgroup (alternatingGroup (Fin 8)))⁆).Normal := Subgroup.commutator_normal _ _
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hN with h | h
  · exfalso
    let a : alternatingGroup (Fin 8) := ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩
    let b : alternatingGroup (Fin 8) := ⟨c[0, 1, 3], by rw [Perm.mem_alternatingGroup]; decide⟩
    have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup (alternatingGroup (Fin 8))),
        (⊤ : Subgroup (alternatingGroup (Fin 8)))⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    have h2 : (a * b : Perm (Fin 8)) = b * a := congrArg Subtype.val h1
    revert h2
    decide +kernel
  · exact h

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
