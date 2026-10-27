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

public section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open Equiv Equiv.Perm

@[expose] def upperEquiv : Fin 7 ≃ {x : Fin 11 // 4 ≤ x.val} where
  toFun i := ⟨⟨i.val + 4, by omega⟩, Nat.le_add_left 4 i.val⟩
  invFun x := ⟨x.1.val - 4, by have := x.1.isLt; omega⟩
  left_inv i := Fin.ext (Nat.add_sub_cancel i.val 4)
  right_inv x := Subtype.ext (Fin.ext (Nat.sub_add_cancel x.2))

theorem coe_upperEquiv (i : Fin 7) : ((upperEquiv i : Fin 11) : ℕ) = i.val + 4 := rfl

@[expose] def extendSeven : Perm (Fin 7) →* Perm (Fin 11) := extendDomainHom upperEquiv

theorem extendSeven_apply_upper (σ : Perm (Fin 7)) (i : Fin 7) :
    extendSeven σ (upperEquiv i) = upperEquiv (σ i) :=
  extendDomain_apply_image σ upperEquiv i

theorem extendSeven_apply_low (σ : Perm (Fin 7)) {x : Fin 11} (hx : x.val < 4) :
    extendSeven σ x = x :=
  extendDomain_apply_not_subtype σ upperEquiv (by omega)

theorem sign_extendSeven (σ : Perm (Fin 7)) : sign (extendSeven σ) = sign σ :=
  sign_extendDomain σ upperEquiv

@[expose] def altExtend : alternatingGroup (Fin 7) →* alternatingGroup (Fin 11) :=
  (extendSeven.comp (alternatingGroup (Fin 7)).subtype).codRestrict (alternatingGroup (Fin 11))
    fun σ => mem_alternatingGroup.mpr ((sign_extendSeven σ).trans (mem_alternatingGroup.mp σ.2))

theorem coe_altExtend (σ : alternatingGroup (Fin 7)) :
    (altExtend σ : Perm (Fin 11)) = extendSeven σ := rfl

theorem altExtend_injective : Function.Injective altExtend := by
  intro σ τ h
  exact Subtype.ext (extendDomainHom_injective upperEquiv (congrArg Subtype.val h))

@[expose] def stabFour : Subgroup (alternatingGroup (Fin 11)) where
  carrier := {h | ∀ i : Fin 11, i.val < 4 → (h : Perm (Fin 11)) i = i}
  mul_mem' {a b} ha hb i hi := by
    change (a : Perm (Fin 11)) ((b : Perm (Fin 11)) i) = i
    rw [hb i hi, ha i hi]
  one_mem' _ _ := rfl
  inv_mem' {a} ha i hi := by
    change (a : Perm (Fin 11))⁻¹ i = i
    rw [Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

theorem mem_stabFour {h : alternatingGroup (Fin 11)} :
    h ∈ stabFour ↔ ∀ i : Fin 11, i.val < 4 → (h : Perm (Fin 11)) i = i := Iff.rfl

theorem four_le_apply_iff_of_mem_stabFour {h : alternatingGroup (Fin 11)} (hh : h ∈ stabFour)
    (x : Fin 11) : 4 ≤ ((h : Perm (Fin 11)) x).val ↔ 4 ≤ x.val := by
  constructor
  · intro hx
    by_contra hlt
    rw [not_le] at hlt
    rw [hh x hlt] at hx
    omega
  · intro hx
    by_contra hlt
    rw [not_le] at hlt
    have := hh _ hlt
    rw [(h : Perm (Fin 11)).injective this] at hlt
    omega

theorem range_altExtend : altExtend.range = stabFour := by
  ext h
  constructor
  · rintro ⟨σ, rfl⟩ i hi
    exact extendSeven_apply_low σ hi
  · intro hh
    set f : Perm (Fin 11) := (h : Perm (Fin 11))
    let τ : Perm {x : Fin 11 // 4 ≤ x.val} :=
      f.subtypePerm (four_le_apply_iff_of_mem_stabFour hh)
    let σ : Perm (Fin 7) := (upperEquiv.permCongr).symm τ
    have hσ : extendSeven σ = f := by
      ext x
      by_cases hx : 4 ≤ x.val
      · have hx' : x = (upperEquiv (upperEquiv.symm ⟨x, hx⟩) : Fin 11) := by
          rw [Equiv.apply_symm_apply]
        rw [hx', extendSeven_apply_upper]
        simp [σ, τ, Equiv.permCongr_apply]
      · rw [not_le] at hx
        rw [extendSeven_apply_low σ hx, hh x hx]
    have hσA : σ ∈ alternatingGroup (Fin 7) := by
      rw [mem_alternatingGroup, ← sign_extendSeven, hσ]
      exact mem_alternatingGroup.mp h.2
    exact ⟨⟨σ, hσA⟩, Subtype.ext hσ⟩

@[expose] noncomputable def relabel : stabFour ≃* alternatingGroup (Fin 7) :=
  ((MonoidHom.ofInjective altExtend_injective).trans
    (MulEquiv.subgroupCongr range_altExtend)).symm

theorem altExtend_relabel (h : stabFour) : altExtend (relabel h) = h := by
  have := (MonoidHom.ofInjective altExtend_injective).apply_symm_apply
    ((MulEquiv.subgroupCongr range_altExtend).symm h)
  exact congrArg Subtype.val this

theorem altExtend_mem_stabFour (σ : alternatingGroup (Fin 7)) : altExtend σ ∈ stabFour :=
  range_altExtend ▸ ⟨σ, rfl⟩

theorem relabel_altExtend (σ : alternatingGroup (Fin 7)) :
    relabel ⟨altExtend σ, altExtend_mem_stabFour σ⟩ = σ := by
  apply altExtend_injective
  rw [altExtend_relabel]

theorem relabel_apply (h : stabFour) (i : Fin 7) :
    ((relabel h : Perm (Fin 7)) i).val =
      ((h : Perm (Fin 11)) ⟨i.val + 4, by omega⟩).val - 4 := by
  have e := congrArg (fun g : alternatingGroup (Fin 11) => (g : Perm (Fin 11)) (upperEquiv i))
    (altExtend_relabel h)
  simp only [coe_altExtend, extendSeven_apply_upper] at e
  change _ = ((h : Perm (Fin 11)) (upperEquiv i)).val - 4
  rw [← e, coe_upperEquiv, Nat.add_sub_cancel]

@[expose] def tZero : alternatingGroup (Fin 7) :=
  ⟨swap 2 3 * swap 4 6, by
    rw [mem_alternatingGroup, map_mul, sign_swap (by decide), sign_swap (by decide)]
    rfl⟩

theorem coe_tZero : (tZero : Perm (Fin 7)) = swap 2 3 * swap 4 6 := rfl

theorem coe_altExtend_tZero : (altExtend tZero : Perm (Fin 11)) = swap 6 7 * swap 8 10 := by
  decide

theorem orderOf_tZero : orderOf tZero = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem cycleType_of_orderOf_eq_two {t : alternatingGroup (Fin 7)} (ht : orderOf t = 2) :
    (t : Perm (Fin 7)).cycleType = Multiset.replicate 2 2 := by
  have ht' : orderOf (t : Perm (Fin 7)) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨n, hn⟩ := cycleType_prime_order (ht'.symm ▸ Nat.prime_two)
  rw [ht'] at hn
  have hsum := sum_cycleType_le (t : Perm (Fin 7))
  have hsign : sign (t : Perm (Fin 7)) = 1 := mem_alternatingGroup.mp t.2
  rw [sign_of_cycleType, hn] at hsign
  rw [hn] at hsum
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    Fintype.card_fin] at hsum hsign
  have hn2 : n ≤ 2 := by omega
  interval_cases n
  · exact absurd hsign (by decide)
  · exact hn
  · exact absurd hsign (by decide)

theorem isConj_tZero {t : alternatingGroup (Fin 7)} (ht : orderOf t = 2) : IsConj tZero t := by
  apply alternatingGroup.isConj_of
  · rw [isConj_iff_cycleType_eq, cycleType_of_orderOf_eq_two orderOf_tZero,
      cycleType_of_orderOf_eq_two ht]
  · rw [← sum_cycleType, cycleType_of_orderOf_eq_two orderOf_tZero]
    decide

end CFSG.ComponentClassification.UnbalancedAltSeven
