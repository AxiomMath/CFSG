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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

private theorem fin3_witness : ∀ r : Perm (Fin 3), r ≠ 1 → r * r = 1 →
    ∃ h : Perm (Fin 3), (r * h * r⁻¹ * h⁻¹) ^ 3 = 1 ∧ r * h * r⁻¹ * h⁻¹ ≠ 1 := by
  decide +kernel

theorem normal_isPGroup_perm_eq_bot_of_card {α : Type*} [Fintype α] [DecidableEq α]
    (h2 : Fintype.card α ≠ 2) (h4 : Fintype.card α ≠ 4) {Q : Subgroup (Perm α)} (hn : Q.Normal)
    (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  by_contra hne
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hlt | hge
  ·
    have : Subsingleton (Perm α) := by
      have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 (by omega)
      infer_instance
    exact hq1' (Subsingleton.elim _ _)
  · rcases Nat.lt_or_ge (Fintype.card α) 5 with hlt5 | hge5
    · have h3 : Fintype.card α = 3 := by omega
      obtain ⟨k, hk⟩ := hQ ⟨q, hqQ⟩
      have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨j, hj⟩ : ∃ j, orderOf q = 2 ^ j := by
        have := orderOf_dvd_of_pow_eq_one hk'
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
        exact ⟨j, hj⟩
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · rw [h] at hj; exact absurd (orderOf_eq_one_iff.1 (by simpa using hj)) hq1'
        · exact h
      set r : Perm α := q ^ 2 ^ (j - 1) with hr
      have hrQ : r ∈ Q := Q.pow_mem hqQ _
      have hr2 : r * r = 1 := by
        rw [hr, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hjpos, ← hj]
        exact pow_orderOf_eq_one _
      have hr1 : r ≠ 1 := by
        intro h
        have : orderOf q ∣ 2 ^ (j - 1) := orderOf_dvd_of_pow_eq_one h
        rw [hj] at this
        have := Nat.le_of_dvd (by positivity) this
        have : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨e⟩ : Nonempty (α ≃ Fin 3) := ⟨Fintype.equivFinOfCardEq h3⟩
      let E : Perm α ≃* Perm (Fin 3) := e.permCongrHom
      obtain ⟨h', hh1, hh2⟩ := fin3_witness (E r) (fun h => hr1 (E.injective (by simpa using h)))
        (by rw [← map_mul, hr2]; simp)
      set h := E.symm h' with hh
      have hq' : r * h * r⁻¹ * h⁻¹ ∈ Q := by
        have := Q.mul_mem hrQ (hn.conj_mem _ (Q.inv_mem hrQ) h)
        simpa [mul_assoc] using this
      have hpow : (r * h * r⁻¹ * h⁻¹) ^ 3 = 1 := by
        apply E.injective
        simpa [map_mul, map_inv, map_pow, hh] using hh1
      have hne1 : r * h * r⁻¹ * h⁻¹ ≠ 1 := by
        intro hc
        apply hh2
        have := congrArg E hc
        simpa [map_mul, map_inv, hh] using this
      obtain ⟨m, hm⟩ := hQ ⟨_, hq'⟩
      have hm' : (r * h * r⁻¹ * h⁻¹) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hd1 : orderOf (r * h * r⁻¹ * h⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
      have hd2 : orderOf (r * h * r⁻¹ * h⁻¹) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have : orderOf (r * h * r⁻¹ * h⁻¹) ∣ Nat.gcd 3 (2 ^ m) := Nat.dvd_gcd hd1 hd2
      have hcop : Nat.gcd 3 (2 ^ m) = 1 :=
        Nat.Coprime.pow_right _ (by norm_num)
      rw [hcop] at this
      exact hne1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 this))
    · have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
      haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      have hle := alternatingGroup_le_of_normal (α := α) (by rwa [Nat.card_eq_fintype_card])
        (N := Q) hnt
      have hdvd : Nat.card (alternatingGroup α) ∣ Nat.card Q := Subgroup.card_dvd_of_le hle
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      have h2' := two_mul_nat_card_alternatingGroup (α := α)
      rw [Nat.card_eq_fintype_card (α := Perm α), Fintype.card_perm] at h2'
      have h3 : 3 ∣ Nat.factorial (Fintype.card α) := Nat.dvd_factorial (by norm_num) (by omega)
      have h4' : 3 ∣ Nat.card (alternatingGroup α) := by
        have : 3 ∣ 2 * Nat.card (alternatingGroup α) := by rwa [h2']
        exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
      have h5 : 3 ∣ 2 ^ k := hk ▸ h4'.trans hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
      omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
