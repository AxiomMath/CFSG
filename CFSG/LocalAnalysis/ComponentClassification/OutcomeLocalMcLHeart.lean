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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Submodule

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

section Defs

variable (m : ℕ)

@[expose] def sumZero : Submodule (ZMod 2) (Fin m → ZMod 2) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' {x y} hx hy := by
    change ∑ i, (x i + y i) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  zero_mem' := by
    change ∑ _i : Fin m, (0 : ZMod 2) = 0
    rw [Finset.sum_const_zero]
  smul_mem' c x hx := by
    change ∑ i, c * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

@[expose] def onesLine : Submodule (ZMod 2) (sumZero m) :=
  (span (ZMod 2) {fun _ => (1 : ZMod 2)}).comap (sumZero m).subtype

end Defs

variable {m : ℕ}

theorem mem_sumZero {x : Fin m → ZMod 2} : x ∈ sumZero m ↔ ∑ i, x i = 0 :=
  Iff.rfl

theorem mem_onesLine {x : sumZero m} :
    x ∈ onesLine m ↔ ∃ c : ZMod 2, (x : Fin m → ZMod 2) = fun _ => c := by
  change (x : Fin m → ZMod 2) ∈ span (ZMod 2) {fun _ => (1 : ZMod 2)} ↔ _
  rw [mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc]; funext i; simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; funext i; simp⟩

@[expose] def pairVec (i j : Fin m) : sumZero m :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    rw [mem_sumZero]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
    simp only [Finset.mem_univ, ite_true]
    decide⟩

theorem coe_pairVec (i j : Fin m) :
    (pairVec i j : Fin m → ZMod 2) = Pi.single i 1 + Pi.single j 1 :=
  rfl

@[expose] def permCoord (σ : Equiv.Perm (Fin m)) :
    (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ⁻¹

theorem permCoord_apply (σ : Equiv.Perm (Fin m)) (x : Fin m → ZMod 2) (j : Fin m) :
    permCoord σ x j = x (σ⁻¹ j) :=
  rfl

theorem permCoord_mul (σ τ : Equiv.Perm (Fin m)) (x : Fin m → ZMod 2) :
    permCoord (σ * τ) x = permCoord σ (permCoord τ x) := by
  funext j
  simp only [permCoord_apply, mul_inv_rev, Equiv.Perm.mul_apply]

theorem permCoord_one (x : Fin m → ZMod 2) : permCoord 1 x = x :=
  rfl

theorem permCoord_mem (σ : Equiv.Perm (Fin m)) {x : Fin m → ZMod 2} (hx : x ∈ sumZero m) :
    permCoord σ x ∈ sumZero m := by
  rw [mem_sumZero] at hx ⊢
  simp only [permCoord_apply]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact hx

theorem map_permCoord_sumZero (σ : Equiv.Perm (Fin m)) :
    (sumZero m).map (permCoord σ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) =
      sumZero m := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact permCoord_mem σ hx
  · intro y hy
    refine ⟨permCoord σ⁻¹ y, permCoord_mem σ⁻¹ hy, ?_⟩
    change permCoord σ (permCoord σ⁻¹ y) = y
    rw [← permCoord_mul, mul_inv_cancel, permCoord_one]

@[expose] def sumZeroEquiv (σ : Equiv.Perm (Fin m)) : sumZero m ≃ₗ[ZMod 2] sumZero m :=
  (permCoord σ).ofSubmodules (sumZero m) (sumZero m) (map_permCoord_sumZero σ)

theorem coe_sumZeroEquiv (σ : Equiv.Perm (Fin m)) (x : sumZero m) :
    ((sumZeroEquiv σ x : sumZero m) : Fin m → ZMod 2) = permCoord σ x :=
  rfl

theorem permCoord_swap (i j : Fin m) (x : Fin m → ZMod 2) :
    permCoord (Equiv.swap i j) x = x + (x i + x j) • (Pi.single i 1 + Pi.single j 1) := by
  classical
  funext k
  rw [permCoord_apply, Equiv.swap_inv, Pi.add_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Equiv.swap_self, Equiv.refl_apply, add_self_zmod2, mul_zero, add_zero]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero, mul_one]
    generalize x k = a
    generalize x j = b
    revert a b
    decide
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add,
      mul_one]
    generalize x k = a
    generalize x i = b
    revert a b
    decide
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
      add_zero, mul_zero, add_zero]

@[expose] def sumZeroRep (m : ℕ) :
    Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m) where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv (sumZeroEquiv σ)
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' σ τ := Units.ext (LinearMap.ext fun x => Subtype.ext (permCoord_mul σ τ x))

theorem sumZeroRep_apply (σ : Equiv.Perm (Fin m)) (x : sumZero m) :
    ((sumZeroRep m σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m)) :
      sumZero m →ₗ[ZMod 2] sumZero m) x = sumZeroEquiv σ x :=
  rfl

theorem map_sumZeroEquiv_onesLine (σ : Equiv.Perm (Fin m)) :
    (onesLine m).map (sumZeroEquiv σ : sumZero m →ₗ[ZMod 2] sumZero m) = onesLine m := by
  have key : ∀ τ : Equiv.Perm (Fin m), ∀ x ∈ onesLine m, sumZeroEquiv τ x ∈ onesLine m := by
    intro τ x hx
    obtain ⟨c, hc⟩ := mem_onesLine.mp hx
    refine mem_onesLine.mpr ⟨c, ?_⟩
    rw [coe_sumZeroEquiv, hc]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key σ x hx
  · intro y hy
    refine ⟨sumZeroEquiv σ⁻¹ y, key σ⁻¹ y hy, Subtype.ext ?_⟩
    change permCoord σ (permCoord σ⁻¹ y) = y
    rw [← permCoord_mul, mul_inv_cancel, permCoord_one]

@[expose] def heartEquiv (σ : Equiv.Perm (Fin m)) :
    (sumZero m ⧸ onesLine m) ≃ₗ[ZMod 2] (sumZero m ⧸ onesLine m) :=
  Submodule.Quotient.equiv (onesLine m) (onesLine m) (sumZeroEquiv σ)
    (map_sumZeroEquiv_onesLine σ)

@[expose] def heartRep (m : ℕ) :
    Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m) where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv (heartEquiv σ)
  map_one' := Units.ext (LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl)
  map_mul' σ τ := Units.ext (LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (sumZeroEquiv (σ * τ) x) =
        (Submodule.Quotient.mk (sumZeroEquiv σ (sumZeroEquiv τ x)) : sumZero m ⧸ onesLine m)
      exact congrArg Submodule.Quotient.mk (Subtype.ext (permCoord_mul σ τ x)))

theorem heartRep_apply_mk (σ : Equiv.Perm (Fin m)) (x : sumZero m) :
    ((heartRep m σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m)) :
      sumZero m ⧸ onesLine m →ₗ[ZMod 2] sumZero m ⧸ onesLine m) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (sumZeroEquiv σ x) :=
  rfl

@[expose] def coordSum (m : ℕ) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i, LinearMap.proj i

theorem coordSum_apply (x : Fin m → ZMod 2) : coordSum m x = ∑ i, x i := by
  simp [coordSum]

theorem sumZero_eq_ker : sumZero m = LinearMap.ker (coordSum m) := by
  ext x
  rw [mem_sumZero, LinearMap.mem_ker, coordSum_apply]

theorem finrank_sumZero (hm : 1 ≤ m) : finrank (ZMod 2) (sumZero m) = m - 1 := by
  have hsurj : LinearMap.range (coordSum m) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨c • Pi.single ⟨0, hm⟩ 1, ?_⟩
    rw [map_smul, coordSum_apply, Finset.sum_pi_single']
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (coordSum m)
  rw [hsurj, finrank_top, finrank_self, Module.finrank_fin_fun, ← sumZero_eq_ker] at h
  omega

theorem onesLine_eq_bot (hm : Odd m) : onesLine m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := mem_onesLine.mp hx
  have hsum := x.2
  rw [mem_sumZero, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm1 : (m : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_iff]
    obtain ⟨k, rfl⟩ := hm
    exact ⟨k, by simp [ZMod.val_one]; omega⟩
  rw [hm1, one_mul] at hsum
  rw [mem_bot]
  exact Subtype.ext (by rw [hc, hsum]; rfl)

theorem finrank_quotient_onesLine (hm : 2 ≤ m) (he : Even m) :
    finrank (ZMod 2) (sumZero m ⧸ onesLine m) = m - 2 := by
  have h1 : (fun _ => (1 : ZMod 2)) ∈ sumZero m := by
    rw [mem_sumZero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := he
    rw [Nat.cast_add, ← two_mul]
    exact mul_eq_zero_of_left rfl _
  have hline : onesLine m = span (ZMod 2) {⟨fun _ => 1, h1⟩} := by
    ext x
    rw [mem_onesLine, mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, Subtype.ext (by rw [hc]; funext i; simp)⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by funext i; simp⟩
  have hne : (⟨fun _ => 1, h1⟩ : sumZero m) ≠ 0 := by
    intro h
    have := congrFun (congrArg Subtype.val h) ⟨0, by omega⟩
    exact one_ne_zero this
  have hq := Submodule.finrank_quotient_add_finrank (onesLine m)
  rw [hline, finrank_span_singleton hne, finrank_sumZero (by omega)] at hq
  rw [hline]
  omega

end CFSG.ComponentClassification.OutcomeLocal
