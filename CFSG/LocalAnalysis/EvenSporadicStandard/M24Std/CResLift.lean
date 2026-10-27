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
public import Mathlib.GroupTheory.SchurZassenhaus
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

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {U E : Type*} [Group U] [Group E]

theorem exists_lift_elemAb [Finite U] (q : U →* E) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) (S₀ : Subgroup E) (hab : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a)
    (h2 : ∀ a ∈ S₀, a * a = 1) :
    ∃ S : Subgroup U, S.map q = S₀ ∧ (∀ s ∈ S, q s = 1 → s = 1) ∧
      (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧ ∀ a ∈ S, a * a = 1 := by
  classical
  have : Finite E := Finite.of_surjective q hq
  set P : Subgroup U := S₀.comap q with hP
  let qP : P →* E := q.comp P.subtype
  have hker_le : q.ker ≤ P := fun k hk => by
    rw [hP, mem_comap, MonoidHom.mem_ker.1 hk]
    exact one_mem _
  have hrange : qP.range = S₀ := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2
    · intro hx
      obtain ⟨u, hu⟩ := hq x
      exact ⟨⟨u, by rw [hP, mem_comap, hu]; exact hx⟩, hu⟩
  have hS₀p : IsPGroup 2 S₀ := by
    intro a
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_one, sq] using h2 a a.2
  have hS₀card : ∃ n : ℕ, Nat.card S₀ = 2 ^ n := (IsPGroup.iff_card).1 hS₀p
  have hNker : qP.ker = q.ker.subgroupOf P := by
    ext x
    simp [qP, MonoidHom.mem_ker, mem_subgroupOf]
  have hNcard : Nat.card qP.ker = Nat.card q.ker := by
    rw [hNker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hNindex : qP.ker.index = Nat.card S₀ := by
    rw [Subgroup.index_ker, hrange]
  have hcop : Nat.Coprime (Nat.card qP.ker) qP.ker.index := by
    obtain ⟨n, hn⟩ := hS₀card
    rw [hNcard, hNindex, hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdisj := hH.disjoint
  have hsup := hH.sup_eq_top
  refine ⟨H.map P.subtype, ?_, ?_, ?_, ?_⟩
  · have hmap : (H.map P.subtype).map q = H.map qP := by
      rw [Subgroup.map_map]
    rw [hmap, ← hrange]
    ext x
    constructor
    · rintro ⟨h, _, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨p, rfl⟩
      have hp : p ∈ qP.ker ⊔ H := by rw [hsup]; exact mem_top p
      obtain ⟨n, hn, h, hh, hnh⟩ := (Subgroup.mem_sup_of_normal_left (s := qP.ker) (t := H)).1 hp
      refine ⟨h, hh, ?_⟩
      rw [← hnh, map_mul, MonoidHom.mem_ker.1 hn, one_mul]
  · rintro s ⟨h, hh, rfl⟩ hs
    have h1 : h ∈ qP.ker := hs
    have := (Subgroup.disjoint_def.1 hdisj) h1 hh
    simp [this]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (a : U) * b = b * a
    have hinj : ∀ x ∈ H, ∀ y ∈ H, qP x = qP y → x = y := by
      intro x hx y hy hxy
      have : x * y⁻¹ ∈ qP.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
      have := (Subgroup.disjoint_def.1 hdisj) this (mul_mem hx (inv_mem hy))
      exact mul_inv_eq_one.1 this
    have := hinj (a * b) (mul_mem ha hb) (b * a) (mul_mem hb ha) (by
      rw [map_mul, map_mul]
      exact hab _ (hrange ▸ ⟨a, rfl⟩) _ (hrange ▸ ⟨b, rfl⟩))
    exact congrArg Subtype.val this
  · rintro _ ⟨a, ha, rfl⟩
    show (a : U) * a = 1
    have hinj : ∀ x ∈ H, ∀ y ∈ H, qP x = qP y → x = y := by
      intro x hx y hy hxy
      have : x * y⁻¹ ∈ qP.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
      have := (Subgroup.disjoint_def.1 hdisj) this (mul_mem hx (inv_mem hy))
      exact mul_inv_eq_one.1 this
    have := hinj (a * a) (mul_mem ha ha) 1 (one_mem _) (by
      rw [map_mul, map_one]
      exact h2 _ (hrange ▸ ⟨a, rfl⟩))
    exact congrArg Subtype.val this

theorem exists_conj_of_map_eq [Finite U] (q : U →* E) (hodd : Odd (Nat.card q.ker)) {t u : U}
    (ht : t * t = 1) (hu : u * u = 1) (hq : q t = q u) : ∃ g : U, g * t * g⁻¹ = u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set k : U := t * u with hk
  have hkK : k ∈ q.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, hq, ← map_mul, hu, map_one]
  have htk : t * k * t⁻¹ = k⁻¹ := by
    have h1 : t * (t * u) * t⁻¹ = u * t := by
      rw [hti]
      calc t * (t * u) * t = (t * t) * u * t := by simp only [mul_assoc]
        _ = u * t := by rw [ht, one_mul]
    rw [hk, h1, mul_inv_rev, hui, hti]
  have hdvd : orderOf k ∣ Nat.card q.ker := by
    have := orderOf_dvd_natCard (⟨k, hkK⟩ : q.ker)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨c, hc⟩ := Odd.of_dvd_nat hodd hdvd
  set m : U := k ^ (c + 1) with hm
  have hmm : m * m = k := by
    rw [hm, ← pow_add]
    have : c + 1 + (c + 1) = orderOf k + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have htm : t * m * t⁻¹ = m⁻¹ := by
    rw [hm, ← conj_pow, htk, inv_pow]
  refine ⟨m⁻¹, ?_⟩
  have h2 : t * m = m⁻¹ * t := by
    rw [mul_inv_eq_iff_eq_mul] at htm
    exact htm
  calc m⁻¹ * t * m⁻¹⁻¹ = m⁻¹ * (t * m) := by rw [inv_inv, mul_assoc]
    _ = m⁻¹ * (m⁻¹ * t) := by rw [h2]
    _ = (m * m)⁻¹ * t := by rw [mul_inv_rev, mul_assoc]
    _ = k⁻¹ * t := by rw [hmm]
    _ = u := by rw [hk, mul_inv_rev, hui, hti, mul_assoc, ht, mul_one]

end CFSG.EvenSporadicStandard.M24Std
