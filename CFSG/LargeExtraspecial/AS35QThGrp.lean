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
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.LargeExtraspecial.AS35QTh

theorem le_card_of_normal {H : Type*} [Group H] {Mb X P : Subgroup H} [Finite Mb]
    (hXM : X ≤ Mb) (hXn : ∀ m ∈ Mb, ∀ x ∈ X, m * x * m⁻¹ ∈ X) (hX : Nat.card X = 27)
    (hPM : P ≤ Mb) (hP : Nat.card P = 8) {y : H} (hyM : y ∈ Mb) (hyX : y ∉ X)
    (hy3 : y ^ 3 = 1) : 648 ≤ Nat.card Mb := by
  set X' := X.subgroupOf Mb with hX'
  have hn : X'.Normal := ⟨fun a ha m => by
    rw [hX', Subgroup.mem_subgroupOf] at ha ⊢
    exact hXn m m.2 a ha⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup X'
  have hX'c : Nat.card X' = 27 := by
    rw [hX', ← hX]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have h3 : 3 ∣ Nat.card (Mb ⧸ X') := by
    have hne : (QuotientGroup.mk ⟨y, hyM⟩ : Mb ⧸ X') ≠ 1 := by
      rw [ne_eq, QuotientGroup.eq_one_iff, hX', Subgroup.mem_subgroupOf]
      exact hyX
    have hpow : (QuotientGroup.mk ⟨y, hyM⟩ : Mb ⧸ X') ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have e : (⟨y, hyM⟩ : Mb) ^ 3 = 1 := Subtype.ext (by simp [hy3])
      rw [e]
      exact X'.one_mem
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← orderOf_eq_prime hpow hne]
    exact orderOf_dvd_natCard _
  have h8 : 8 ∣ Nat.card (Mb ⧸ X') := by
    set f : P →* Mb ⧸ X' := (QuotientGroup.mk' X').comp (Subgroup.inclusion hPM) with hf
    have hfi : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro p hp
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hX', Subgroup.mem_subgroupOf] at hp
      have h1 : orderOf (p : H) ∣ 8 := hP ▸ Subgroup.orderOf_dvd_natCard P p.2
      have h2 : orderOf (p : H) ∣ 27 := hX ▸ Subgroup.orderOf_dvd_natCard X hp
      have h3 : orderOf (p : H) ∣ Nat.gcd 8 27 := Nat.dvd_gcd h1 h2
      rw [show Nat.gcd 8 27 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact Subgroup.mem_bot.mpr (Subtype.ext h3)
    rw [← hP]
    exact Subgroup.card_dvd_of_injective f hfi
  have h24 : 24 ∣ Nat.card (Mb ⧸ X') :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h8
  have hpos : 0 < Nat.card (Mb ⧸ X') := Nat.card_pos
  have := Nat.le_of_dvd hpos h24
  rw [hcard, hX'c]
  omega

theorem exists_hom_of_index_odd {C : Type*} [Group C] {z : C} (hzc : ∀ c, c * z = z * c)
    (hz2 : z * z = 1) {T T₀ : Subgroup C} (hodd : Odd T.index) (hzT₀ : z ∉ T₀)
    (hT : ∀ x ∈ T, x ∈ T₀ ∨ x * z ∈ T₀) :
    ∃ ψ : C →* Multiplicative (ZMod 2), ψ z = Multiplicative.ofAdd 1 := by
  classical
  have : T.FiniteIndex := ⟨hodd.pos.ne'⟩
  have hne : ∀ {x y : C}, x ∈ T₀ → y ∉ T₀ → x * y ∉ T₀ := fun hx hy hxy =>
    hy (by simpa using T₀.mul_mem (T₀.inv_mem hx) hxy)
  have hne' : ∀ {x y : C}, x ∉ T₀ → y ∈ T₀ → x * y ∉ T₀ := fun hx hy hxy =>
    hx (by simpa using T₀.mul_mem hxy (T₀.inv_mem hy))
  let ϕ : T →* Multiplicative (ZMod 2) :=
    { toFun := fun x => if (x : C) ∈ T₀ then 1 else Multiplicative.ofAdd 1
      map_one' := by simp [T₀.one_mem]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        by_cases hx : (x : C) ∈ T₀ <;> by_cases hy : (y : C) ∈ T₀
        · simp [hx, hy, T₀.mul_mem hx hy]
        · simp [hx, hy, hne hx hy]
        · simp [hx, hy, hne' hx hy]
        · have hxz := (hT x x.2).resolve_left hx
          have hyz := (hT y y.2).resolve_left hy
          have hxy : (x : C) * y ∈ T₀ := by
            have h := T₀.mul_mem hxz hyz
            rwa [show (x : C) * z * (y * z) = x * y * (z * z) by
              rw [mul_assoc, ← mul_assoc z, ← hzc y]; group, hz2, mul_one] at h
          simp only [hx, hy, hxy, ite_false, ite_true]
          rw [← ofAdd_add]
          decide }
  have hzi : z ^ T.index = z := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  refine ⟨ϕ.transfer, (MonoidHom.transfer_eq_pow ϕ z fun k g₀ _ => by
    rw [mul_assoc, ← (Commute.pow_right (show Commute g₀ z from hzc g₀) k).eq, ← mul_assoc,
      inv_mul_cancel, one_mul]).trans ?_⟩
  change (if z ^ T.index ∈ T₀ then 1 else Multiplicative.ofAdd 1) = _
  simp only [hzi, hzT₀, ite_false]

end CFSG.LargeExtraspecial.AS35QTh
