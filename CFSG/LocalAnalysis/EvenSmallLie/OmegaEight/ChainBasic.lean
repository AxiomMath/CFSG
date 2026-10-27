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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup

variable {G : Type*} [Group G]

@[expose] def pw (A : Subgroup G) (n : ℕ) : Subgroup G := closure {x | ∃ a ∈ A, a ^ n = x}

@[expose] def om (A : Subgroup G) (n : ℕ) : Subgroup G := closure {x | x ∈ A ∧ x ^ n = 1}

theorem pw_le (A : Subgroup G) (n : ℕ) : pw A n ≤ A := by
  rw [pw, closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact pow_mem ha n

theorem om_le (A : Subgroup G) (n : ℕ) : om A n ≤ A := by
  rw [om, closure_le]
  exact fun x hx => hx.1

theorem pow_mem_pw {A : Subgroup G} {a : G} (ha : a ∈ A) (n : ℕ) : a ^ n ∈ pw A n :=
  subset_closure ⟨a, ha, rfl⟩

theorem mem_om_of {A : Subgroup G} {a : G} (ha : a ∈ A) {n : ℕ} (h : a ^ n = 1) : a ∈ om A n :=
  subset_closure ⟨ha, h⟩

section Abelian

variable {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
include hA

theorem mem_pw {n : ℕ} {x : G} : x ∈ pw A n ↔ ∃ a ∈ A, a ^ n = x := by
  refine ⟨fun hx => ?_, fun ⟨a, ha, h⟩ => h ▸ pow_mem_pw ha n⟩
  induction hx using closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, one_mem _, one_pow n⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, mul_mem ha hb, Commute.mul_pow (hA a ha b hb) n⟩
  | inv x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a⁻¹, inv_mem ha, inv_pow a n⟩

theorem mem_om {n : ℕ} {x : G} : x ∈ om A n ↔ x ∈ A ∧ x ^ n = 1 := by
  refine ⟨fun hx => ?_, fun h => mem_om_of h.1 h.2⟩
  induction hx using closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, one_pow n⟩
  | mul x y _ _ hx hy =>
    exact ⟨mul_mem hx.1 hy.1, by rw [Commute.mul_pow (hA x hx.1 y hy.1) n, hx.2, hy.2, one_mul]⟩
  | inv x _ hx => exact ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

@[expose] def powHom (n : ℕ) : A →* A where
  toFun a := a ^ n
  map_one' := one_pow n
  map_mul' a b := Commute.mul_pow (Subtype.ext (hA a a.2 b b.2)) n

theorem card_eq_card_om_mul_card_pw [Finite G] (n : ℕ) :
    Nat.card A = Nat.card (om A n) * Nat.card (pw A n) := by
  have eK : (powHom hA n).ker ≃ om A n :=
    { toFun := fun x => ⟨x.1.1, (mem_om hA).2 ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, ((mem_om hA).1 x.2).1⟩,
        Subtype.ext ((mem_om hA).1 x.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have eR : (powHom hA n).range ≃ pw A n :=
    { toFun := fun x => ⟨x.1.1, by
        obtain ⟨a, ha⟩ := x.2
        rw [← ha]
        exact pow_mem_pw a.2 n⟩
      invFun := fun x => ⟨⟨x.1, pw_le A n x.2⟩, by
        obtain ⟨a, ha, h⟩ := (mem_pw hA).1 x.2
        exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr eK, ← Nat.card_congr eR, ← index_ker, card_mul_index]

end Abelian

theorem pw_comm {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (n : ℕ) :
    ∀ x ∈ pw A n, ∀ y ∈ pw A n, x * y = y * x :=
  fun x hx y hy => hA x (pw_le A n hx) y (pw_le A n hy)

theorem om_pw_le {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (m n : ℕ) :
    om (pw A m) n ≤ om A n := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := (mem_om (pw_comm hA m)).1 hx
  exact mem_om_of (pw_le A m hx1) hx2

theorem om_om_le {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (m n : ℕ) :
    om (om A m) n ≤ om A n := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := (mem_om fun x hx y hy => hA x (om_le A m hx) y (om_le A m hy)).1 hx
  exact mem_om_of (om_le A m hx1) hx2

theorem card_le_pow [Finite G] {Ω : Subgroup G} (e : ℕ) :
    ∀ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → om B 2 ≤ Ω →
      (∀ b ∈ B, b ^ 2 ^ e = 1) → Nat.card B ≤ Nat.card Ω ^ e := by
  induction e with
  | zero =>
    intro B _ _ he
    have : B = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have := he b hb
      rw [pow_zero, pow_one] at this
      exact this ▸ one_mem _
    rw [this, card_bot, pow_zero]
  | succ e ih =>
    intro B hB hΩ he
    rw [card_eq_card_om_mul_card_pw hB 2, pow_succ, mul_comm (Nat.card Ω ^ e)]
    refine Nat.mul_le_mul (card_le_of_le hΩ) (ih (pw B 2) (pw_comm hB 2)
      ((om_pw_le hB 2 2).trans hΩ) fun b hb => ?_)
    obtain ⟨a, ha, rfl⟩ := (mem_pw hB).1 hb
    rw [← pow_mul, ← pow_succ']
    exact he a ha

structure Level (Q : Subgroup G) (k : ℕ) (A : Subgroup G) : Prop where
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  card_eq : Nat.card A = 2 ^ (6 * k)
  Q_le : Q ≤ A
  mem_Q : ∀ a ∈ A, a * a = 1 → a ∈ Q
  pow_eq_one : ∀ a ∈ A, a ^ 2 ^ k = 1

namespace Level

variable {Q : Subgroup G} {k : ℕ} {A : Subgroup G}

theorem om_two (hQ2 : ∀ q ∈ Q, q * q = 1) (hL : Level Q k A) : om A 2 = Q := by
  refine le_antisymm (fun x hx => ?_) (fun q hq => mem_om_of (hL.Q_le hq) (by rw [sq, hQ2 q hq]))
  obtain ⟨hx1, hx2⟩ := (mem_om hL.comm).1 hx
  exact hL.mem_Q x hx1 (by rw [← sq, hx2])

variable [Finite G] (hQ : Nat.card Q = 64) (hQ2 : ∀ q ∈ Q, q * q = 1) (hL : Level Q k A)
include hQ hQ2 hL

theorem card_pw_two (hk : 1 ≤ k) : Nat.card (pw A 2) = 2 ^ (6 * (k - 1)) := by
  have h := card_eq_card_om_mul_card_pw hL.comm 2
  rw [om_two hQ2 hL, hQ, hL.card_eq] at h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e : 2 ^ (6 * (j + 1)) = 64 * 2 ^ (6 * j) := by rw [mul_add, pow_add]; ring
  rw [e] at h
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm

omit [Finite G] hQ hQ2 in
theorem pow_mem_Q (hk : 1 ≤ k) {a : G} (ha : a ∈ A) : a ^ 2 ^ (k - 1) ∈ Q := by
  refine hL.mem_Q _ (pow_mem ha _) ?_
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hk]
  exact hL.pow_eq_one a ha

theorem om_pow (hk : 1 ≤ k) : om A (2 ^ (k - 1)) = pw A 2 := by
  symm
  refine eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨a, ha, rfl⟩ := (mem_pw hL.comm).1 hx
    refine mem_om_of (pow_mem ha 2) ?_
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hk]
    exact hL.pow_eq_one a ha
  · rw [card_pw_two hQ hQ2 hL hk]
    have hcomm : ∀ x ∈ om A (2 ^ (k - 1)), ∀ y ∈ om A (2 ^ (k - 1)), x * y = y * x :=
      fun x hx y hy => hL.comm x (om_le A _ hx) y (om_le A _ hy)
    have h := card_le_pow (Ω := Q) (k - 1) (om A (2 ^ (k - 1))) hcomm
      ((om_om_le hL.comm _ 2).trans (om_two hQ2 hL).le)
      (fun b hb => ((mem_om hL.comm).1 hb).2)
    rwa [hQ, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul] at h

theorem pw_top (hk : 1 ≤ k) : pw A (2 ^ (k - 1)) = Q := by
  refine eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨a, ha, rfl⟩ := (mem_pw hL.comm).1 hx
    exact pow_mem_Q hL hk ha
  · have h := card_eq_card_om_mul_card_pw hL.comm (2 ^ (k - 1))
    rw [om_pow hQ hQ2 hL hk, card_pw_two hQ hQ2 hL hk, hL.card_eq] at h
    have e : 2 ^ (6 * k) = 2 ^ (6 * (k - 1)) * 64 := by
      rw [show 6 * k = 6 * (k - 1) + 6 by omega, pow_add]; norm_num
    rw [e] at h
    rw [hQ, (Nat.eq_of_mul_eq_mul_left (by positivity) h)]

theorem pow_eq_one_iff (hk : 1 ≤ k) {a : G} (ha : a ∈ A) :
    a ^ 2 ^ (k - 1) = 1 ↔ a ∈ pw A 2 := by
  rw [← om_pow hQ hQ2 hL hk, mem_om hL.comm]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

theorem exists_pow_eq (hk : 1 ≤ k) {q : G} (hq : q ∈ Q) : ∃ a ∈ A, a ^ 2 ^ (k - 1) = q := by
  rw [← pw_top hQ hQ2 hL hk, mem_pw hL.comm] at hq
  exact hq

theorem pw_two (hk : 2 ≤ k) : Level Q (k - 1) (pw A 2) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hcomm := pw_comm hL.comm 2
  have hexp : ∀ b ∈ pw A 2, b ^ 2 ^ (k - 1) = 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (mem_pw hL.comm).1 hb
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hk1]
    exact hL.pow_eq_one a ha
  have hle : om (pw A 2) 2 ≤ Q := (om_pw_le hL.comm 2 2).trans (om_two hQ2 hL).le
  have hQle : Q ≤ om (pw A 2) 2 := by
    have hcard : Nat.card Q ≤ Nat.card (om (pw A 2) 2) := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      have hdvd : Nat.card (om (pw A 2) 2) ∣ 64 := hQ ▸ card_dvd_of_le hle
      have h32 : Nat.card (om (pw A 2) 2) ≤ 32 := by
        rw [hQ] at hlt
        have := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases h : Nat.card (om (pw A 2) 2) <;> simp_all
      have h1 := card_le_pow (k - 1) (pw A 2) hcomm le_rfl hexp
      rw [card_pw_two hQ hQ2 hL hk1] at h1
      have h2 : Nat.card (om (pw A 2) 2) ^ (k - 1) ≤ 32 ^ (k - 1) := Nat.pow_le_pow_left h32 _
      have h3 : 32 ^ (k - 1) < 2 ^ (6 * (k - 1)) := by
        rw [pow_mul]
        exact Nat.pow_lt_pow_left (by norm_num) (by omega)
      omega
    exact (eq_of_le_of_card_ge hle hcard).symm.le
  exact ⟨hcomm, card_pw_two hQ hQ2 hL hk1, hQle.trans (om_le _ 2),
    fun b hb h => hL.mem_Q b (pw_le A 2 hb) h, hexp⟩

end Level

theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 (sup_le hXN le_normalizer)
  have : (N.subgroupOf X).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer_inf]
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf]
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(mem_normalizer_iff.1 (hXN hx) y).1 hy1, mul_mem (mul_mem hx hy2) (inv_mem hx)⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨(mem_normalizer_iff.1 (hXN hx) y).2 hy1, ?_⟩
      have := mul_mem (mul_mem (inv_mem hx) hy2) hx
      simpa [mul_assoc] using this
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← card_map_of_injective X.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

end CFSG.EvenSmallLie.OmegaEight.Chain
