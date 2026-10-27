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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups

section Field

variable {F : Type} [Field F]

theorem exists_primitiveRoot_dvd [Finite F] {m : ℕ} [NeZero m] (h : m ∣ Nat.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    intro h0
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hdvd : m ∣ orderOf g := hg ▸ h
  have hord := orderOf_pow_orderOf_div hne hdvd
  refine ⟨((g ^ (orderOf g / m) : Fˣ) : F), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / m))
  rwa [hord] at this

theorem zpow_gen_isCube_iff [Finite F] (h3 : 3 ∣ Nat.card F - 1) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) (m : ℤ) :
    (∃ c : Fˣ, g ^ m = c ^ 3) ↔ (3 : ℤ) ∣ m := by
  have hN : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg c)
    have hc' : g ^ m = g ^ (t * 3) := by
      rw [hc, _root_.zpow_mul]
      norm_num
    have h1 : g ^ (m - t * 3) = 1 := by
      rw [zpow_sub, hc', mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hN] at h2
    have h3' : (3 : ℤ) ∣ ((Nat.card F - 1 : ℕ) : ℤ) := by exact_mod_cast h3
    have := dvd_trans h3' h2
    omega
  · rintro ⟨t, rfl⟩
    exact ⟨g ^ t, by
      rw [mul_comm, _root_.zpow_mul]
      norm_num⟩

theorem exists_cube_mul_pow [Finite F] (h3 : 3 ∣ Nat.card F - 1) {a : Fˣ}
    (ha : ∀ c : Fˣ, a ≠ c ^ 3) (b : Fˣ) :
    ∃ k : Fin 3, ∃ d : Fˣ, b * a ^ (k : ℕ) = d ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  have hi : ¬ (3 : ℤ) ∣ i := fun h => ha _ ((zpow_gen_isCube_iff h3 hg i).mpr h).choose_spec
  have key : ∃ k : Fin 3, (3 : ℤ) ∣ j + (k : ℕ) * i := by
    have h1 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have h2 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · exact ⟨0, by simp; omega⟩
    · exact ⟨2, by simp; omega⟩
    · exact ⟨1, by simp; omega⟩
    · exact ⟨0, by simp; omega⟩
    · exact ⟨1, by simp; omega⟩
    · exact ⟨2, by simp; omega⟩
  obtain ⟨k, hk⟩ := key
  obtain ⟨c, hc⟩ := (zpow_gen_isCube_iff h3 hg _).mpr hk
  refine ⟨k, c, ?_⟩
  rw [← hc, zpow_add, ← zpow_natCast, ← _root_.zpow_mul, mul_comm i]

end Field

section Group

variable {G : Type*} [Group G]

theorem mul_pow_three_of_central (u v s : G) (hs : s ∈ Subgroup.center G) (hs3 : s ^ 3 = 1)
    (h : u * v = s * (v * u)) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have ht : s⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hs
  have hc : ∀ x y : G, x * (s⁻¹ * y) = s⁻¹ * (x * y) := fun x y => by
    rw [← mul_assoc, (Subgroup.mem_center_iff.mp ht x), mul_assoc]
  have h1 : v * u = s⁻¹ * (u * v) := by
    rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : v * v * u = s⁻¹ * (s⁻¹ * (u * v * v)) := by
    calc v * v * u = v * (v * u) := by rw [mul_assoc]
      _ = v * (s⁻¹ * (u * v)) := by rw [h1]
      _ = s⁻¹ * (v * (u * v)) := hc _ _
      _ = s⁻¹ * ((v * u) * v) := by rw [mul_assoc]
      _ = s⁻¹ * ((s⁻¹ * (u * v)) * v) := by rw [h1]
      _ = s⁻¹ * (s⁻¹ * (u * v * v)) := by rw [mul_assoc s⁻¹ (u * v) v]
  have h3 : (u * v) ^ 3 = s⁻¹ * (u * u * (v * v * u) * v) := by
    calc (u * v) ^ 3 = u * (v * u) * v * u * v := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = u * (s⁻¹ * (u * v)) * v * u * v := by rw [h1]
      _ = s⁻¹ * (u * u * v * v * u * v) := by
          rw [hc u (u * v)]
          simp only [mul_assoc]
      _ = s⁻¹ * (u * u * (v * v * u) * v) := by simp only [mul_assoc]
  have hs' : s⁻¹ * (s⁻¹ * s⁻¹) = 1 := by
    have := congrArg (fun z => z⁻¹) hs3
    simpa [pow_succ, mul_assoc] using this
  rw [h3, h2]
  simp only [mul_assoc, hc]
  have h5 : ∀ z : G, s⁻¹ * (s⁻¹ * (s⁻¹ * z)) = z := fun z => by
    calc s⁻¹ * (s⁻¹ * (s⁻¹ * z)) = (s⁻¹ * (s⁻¹ * s⁻¹)) * z := by simp only [mul_assoc]
      _ = z := by rw [hs', one_mul]
  rw [h5]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow_mul_of_central (x z s : G) (hs : s ∈ Subgroup.center G)
    (h : x * z = s * (z * x)) (n : ℕ) : x ^ n * z = s ^ n * (z * x ^ n) := by
  have hc : ∀ a b : G, a * (s * b) = s * (a * b) := fun a b => by
    rw [← mul_assoc, (Subgroup.mem_center_iff.mp hs a), mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * z = x * (x ^ n * z) := by rw [pow_succ', mul_assoc]
      _ = x * (s ^ n * (z * x ^ n)) := by rw [ih]
      _ = s ^ n * (x * (z * x ^ n)) := by
          rw [← mul_assoc x, (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hs n) x), mul_assoc]
      _ = s ^ n * ((x * z) * x ^ n) := by rw [mul_assoc]
      _ = s ^ n * ((s * (z * x)) * x ^ n) := by rw [h]
      _ = s ^ (n + 1) * (z * x ^ (n + 1)) := by
          rw [pow_succ', mul_assoc s, hc]
          simp only [mul_assoc, pow_succ']

theorem mul_pow_of_central (x z s : G) (hs : s ∈ Subgroup.center G)
    (h : x * z = s * (z * x)) (n : ℕ) : x * z ^ n = s ^ n * (z ^ n * x) := by
  have hc : ∀ a b : G, a * (s * b) = s * (a * b) := fun a b => by
    rw [← mul_assoc, (Subgroup.mem_center_iff.mp hs a), mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * z ^ (n + 1) = (x * z ^ n) * z := by rw [pow_succ, mul_assoc]
      _ = (s ^ n * (z ^ n * x)) * z := by rw [ih]
      _ = s ^ n * (z ^ n * (x * z)) := by simp only [mul_assoc]
      _ = s ^ n * (z ^ n * (s * (z * x))) := by rw [h]
      _ = s ^ (n + 1) * (z ^ (n + 1) * x) := by
          rw [hc (z ^ n)]
          simp only [mul_assoc, pow_succ, hc]

section Cosets

variable (A : Subgroup G) (N : Subgroup A) {ι : Type*}

theorem exists_mem_of_injective_of_index [Finite ι] [Finite A] (f : ι → A)
    (hinj : ∀ i j, (f i)⁻¹ * f j ∈ N → i = j) (hcard : Nat.card ι = N.index) (z : A) :
    ∃ i, (f i)⁻¹ * z ∈ N := by
  let g : ι → A ⧸ N := fun i => QuotientGroup.mk (f i)
  have hg : Function.Injective g := fun i j hij => hinj i j (QuotientGroup.eq.mp hij)
  have hb : Function.Bijective g :=
    (Nat.bijective_iff_injective_and_card g).mpr ⟨hg, hcard.trans rfl⟩
  obtain ⟨i, hi⟩ := hb.2 (QuotientGroup.mk z)
  exact ⟨i, QuotientGroup.eq.mp hi⟩

theorem index_le_of_cover [Finite ι] (f : ι → A) (h : ∀ z : A, ∃ i, (f i)⁻¹ * z ∈ N) :
    N.index ≤ Nat.card ι := by
  let g : ι → A ⧸ N := fun i => QuotientGroup.mk (f i)
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi⟩ := h z
    exact ⟨i, QuotientGroup.eq.mpr hi⟩
  exact Nat.card_le_card_of_surjective g hs

end Cosets

end Group

section GroupMore

variable {G : Type*} [Group G]

theorem monomial_commute (x z s : G) (hs : s ∈ Subgroup.center G) (h : x * z = s * (z * x))
    (i j : ℕ) :
    (x ^ i * z ^ j) * z = s ^ i * (z * (x ^ i * z ^ j)) ∧
      x * (x ^ i * z ^ j) = s ^ j * ((x ^ i * z ^ j) * x) := by
  have hi := pow_mul_of_central x z s hs h i
  have hj := mul_pow_of_central x z s hs h j
  have hcen : ∀ n : ℕ, ∀ a : G, a * s ^ n = s ^ n * a := fun n a =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hs n) a
  constructor
  · calc (x ^ i * z ^ j) * z = x ^ i * (z ^ j * z) := by rw [mul_assoc]
      _ = x ^ i * (z * z ^ j) := by rw [← pow_succ, pow_succ']
      _ = (x ^ i * z) * z ^ j := by rw [mul_assoc]
      _ = (s ^ i * (z * x ^ i)) * z ^ j := by rw [hi]
      _ = s ^ i * (z * (x ^ i * z ^ j)) := by simp only [mul_assoc]
  · calc x * (x ^ i * z ^ j) = x ^ i * (x * z ^ j) := by rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc]
      _ = x ^ i * (s ^ j * (z ^ j * x)) := by rw [hj]
      _ = s ^ j * (x ^ i * (z ^ j * x)) := by
          rw [← mul_assoc, hcen, mul_assoc]
      _ = s ^ j * ((x ^ i * z ^ j) * x) := by simp only [mul_assoc]

theorem eq_of_pair_right (u c z a a' : G) (hc : c ∈ Subgroup.center G)
    (h : u * z = a * (z * u)) (h' : (u * c) * z = a' * (z * (u * c))) : a = a' := by
  have hcz : c * z = z * c := (Subgroup.mem_center_iff.mp hc z).symm
  have : a * (z * (u * c)) = a' * (z * (u * c)) := by
    calc a * (z * (u * c)) = (a * (z * u)) * c := by simp only [mul_assoc]
      _ = (u * z) * c := by rw [h]
      _ = u * (c * z) := by rw [mul_assoc, ← hcz]
      _ = (u * c) * z := (mul_assoc u c z).symm
      _ = a' * (z * (u * c)) := h'
  exact mul_right_cancel this

theorem eq_of_pair_left (u c x b b' : G) (hc : c ∈ Subgroup.center G)
    (h : x * u = b * (u * x)) (h' : x * (u * c) = b' * ((u * c) * x)) : b = b' := by
  have hcx : c * x = x * c := (Subgroup.mem_center_iff.mp hc x).symm
  have : b * ((u * c) * x) = b' * ((u * c) * x) := by
    calc b * ((u * c) * x) = b * (u * (c * x)) := by rw [mul_assoc u c x]
      _ = b * (u * (x * c)) := by rw [hcx]
      _ = (b * (u * x)) * c := by simp only [mul_assoc]
      _ = (x * u) * c := by rw [h]
      _ = x * (u * c) := mul_assoc x u c
      _ = b' * ((u * c) * x) := h'
  exact mul_right_cancel this

theorem central_swap_right (P C z a : G) (hC : C ∈ Subgroup.center G)
    (h : P * z = a * (z * P)) : (P * C) * z = a * (z * (P * C)) := by
  have hcz : C * z = z * C := (Subgroup.mem_center_iff.mp hC z).symm
  calc (P * C) * z = P * (C * z) := mul_assoc P C z
    _ = (P * z) * C := by rw [hcz, mul_assoc]
    _ = (a * (z * P)) * C := by rw [h]
    _ = a * (z * (P * C)) := by simp only [mul_assoc]

theorem central_swap_left (P C x b : G) (hC : C ∈ Subgroup.center G)
    (h : x * P = b * (P * x)) : (P * C) * x = b⁻¹ * (x * (P * C)) := by
  have hcx : C * x = x * C := (Subgroup.mem_center_iff.mp hC x).symm
  have h' : P * x = b⁻¹ * (x * P) := by
    rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (P * C) * x = P * (C * x) := mul_assoc P C x
    _ = (P * x) * C := by rw [hcx, mul_assoc]
    _ = (b⁻¹ * (x * P)) * C := by rw [h']
    _ = b⁻¹ * (x * (P * C)) := by simp only [mul_assoc]

end GroupMore

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
