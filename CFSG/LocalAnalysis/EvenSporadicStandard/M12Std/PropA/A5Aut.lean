module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
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

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup

private theorem card_centralizer_alt5 :
    ∀ σ : Perm (Fin 5), σ * σ = 1 →
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * σ = σ * (a : Perm (Fin 5))} = 4 ∨
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * σ = σ * (a : Perm (Fin 5))} = 6 ∨
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * σ = σ * (a : Perm (Fin 5))} = 60 := by
  decide +kernel

theorem card_fixedPoints_of_alt5 {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 5))
    (α : H ≃* H) (hα : ∀ h, α (α h) = h) :
    Nat.card {h : H // α h = h} = 4 ∨ Nat.card {h : H // α h = h} = 6 ∨
      Nat.card {h : H // α h = h} = 60 := by
  classical
  let β : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5) := e.symm.trans (α.trans e)
  have hββ : β * β = 1 := by
    ext a
    simp [β, hα]
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).2 β
  have hinj :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).1
  have hππ : π * π = 1 := by
    apply hinj
    rw [map_mul, map_one, hπ]
    exact hββ
  have hcard₁ : Nat.card {h : H // α h = h} =
      Nat.card {a : alternatingGroup (Fin 5) // MulAut.conjNormal π a = a} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun h => by
      change α h = h ↔ MulAut.conjNormal π (e h) = e h
      rw [hπ]
      constructor
      · intro hh
        simp [β, hh]
      · intro hh
        exact e.injective (by simpa [β] using hh))
  have hcard₂ : Nat.card {a : alternatingGroup (Fin 5) // MulAut.conjNormal π a = a} =
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * π = π * (a : Perm (Fin 5))} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [Subtype.ext_iff, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact eq_comm)
  have hcard : Nat.card {h : H // α h = h} =
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * π = π * (a : Perm (Fin 5))} :=
    hcard₁.trans hcard₂
  rcases card_centralizer_alt5 π hππ with h | h | h
  · left; rw [hcard]; exact h
  · right; left; rw [hcard]; exact h
  · right; right; rw [hcard]; exact h

theorem card_inf_centralizer_of_alt5 {G : Type*} [Group G] {H : Subgroup G}
    (e : H ≃* alternatingGroup (Fin 5)) {t : G} (htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    (ht2 : t * t = 1) :
    Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = 4 ∨
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = 6 ∨
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = 60 := by
  classical
  have htinv : t⁻¹ = t := mul_eq_one_iff_inv_eq.mp ht2
  let fH : H →* H :=
    ((MulAut.conj t).toMonoidHom.comp H.subtype).codRestrict H fun h => htH h.1 h.2
  have hfH : Function.Bijective fH := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have h : t * ↑x * t⁻¹ = t * ↑y * t⁻¹ := by
        simpa [fH] using congrArg Subtype.val hxy
      calc ↑x = t⁻¹ * (t * ↑x * t⁻¹) * t := by simp [mul_assoc]
        _ = t⁻¹ * (t * ↑y * t⁻¹) * t := by rw [h]
        _ = ↑y := by simp [mul_assoc]
    · intro y
      refine ⟨⟨t⁻¹ * ↑y * t, ?_⟩, ?_⟩
      · simpa [htinv] using htH y.1 y.2
      · apply Subtype.ext
        change t * (t⁻¹ * ↑y * t) * t⁻¹ = ↑y
        simp [mul_assoc]
  let α : H ≃* H := MulEquiv.ofBijective fH hfH
  have hα : ∀ h, α (α h) = h := by
    intro h
    ext
    change t * (t * ↑h * t⁻¹) * t⁻¹ = ↑h
    rw [htinv]
    calc t * (t * ↑h * t) * t = (t * t) * ↑h * (t * t) := by simp only [mul_assoc]
      _ = ↑h := by rw [ht2]; simp
  have hcard : Nat.card {h : H // α h = h} =
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun h => ⟨h.1.1, ⟨h.1.2, ?_⟩⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun h => by ext; rfl
        right_inv := fun x => by ext; rfl }
    · change h.1.1 ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hh : t * h.1.1 * t⁻¹ = h.1.1 := by
        have := congrArg Subtype.val h.2
        simpa [α, fH] using this
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · apply Subtype.ext
      change t * x.1 * t⁻¹ = x.1
      exact mul_inv_eq_iff_eq_mul.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm
  rcases card_fixedPoints_of_alt5 e α hα with h | h | h
  · left; rw [hcard] at h; exact h
  · right; left; rw [hcard] at h; exact h
  · right; right; rw [hcard] at h; exact h

end CFSG.EvenSporadicStandard.M12Std.PropA
