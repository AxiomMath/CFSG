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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup
open scoped Pointwise

section Generic

variable {Γ : Type*} [Group Γ]

theorem card_sup_of_inf_eq_bot' {X Y : Subgroup Γ} (hYX : Y ≤ normalizer (X : Set Γ))
    (hXY : X ⊓ Y = ⊥) : Nat.card (X ⊔ Y : Subgroup Γ) = Nat.card X * Nat.card Y := by
  have hset : ((Y : Set Γ) * (X : Set Γ)) = ((Y ⊔ X : Subgroup Γ) : Set Γ) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right Y X hYX).symm
  have hc : Nat.card (Y ⊔ X : Subgroup Γ) = Nat.card ((Y : Set Γ) * (X : Set Γ) : Set Γ) := by
    rw [hset]
    rfl
  rw [sup_comm, hc, Nat.mul_comm (Nat.card X), ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : ↥Y × ↥X =>
      (⟨(q.1 : Γ) * q.2, Set.mul_mem_mul q.1.2 q.2.2⟩ : ((Y : Set Γ) * (X : Set Γ) : Set Γ)))
    ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h' : a * b = a' * b' := congrArg Subtype.val hab
    have hm : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ X ⊓ Y :=
      ⟨hm ▸ X.mul_mem hb' (X.inv_mem hb), Y.mul_mem (Y.inv_mem ha') ha⟩
    rw [hXY, Subgroup.mem_bot] at hmem
    obtain rfl : a' = a := inv_mul_eq_one.mp hmem
    obtain rfl : b = b' := mul_left_cancel h'
    rfl
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩⟩
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

theorem card_sup_mul_card_inf' [Finite Γ] {H N : Subgroup Γ} (hHN : H ≤ normalizer (N : Set Γ)) :
    Nat.card (H ⊔ N : Subgroup Γ) * Nat.card (H ⊓ N : Subgroup Γ) = Nat.card H * Nat.card N := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have hA := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have hB := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  rw [← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv] at hA
  have hcN : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup Γ) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ N ≤ H)).toEquiv
  rw [hcN] at hB
  calc Nat.card (H ⊔ N : Subgroup Γ) * Nat.card (H ⊓ N : Subgroup Γ)
      = (Nat.card (↥H ⧸ N.subgroupOf H) * Nat.card N) * Nat.card (H ⊓ N : Subgroup Γ) := by rw [hA]
    _ = (Nat.card (↥H ⧸ N.subgroupOf H) * Nat.card (H ⊓ N : Subgroup Γ)) * Nat.card N := by ring
    _ = Nat.card H * Nat.card N := by rw [← hB]

theorem inf_eq_bot_of_isPGroup_of_pow_five {Z W : Subgroup Γ} (hZ : IsPGroup 2 Z)
    (hW : ∀ w ∈ W, w ^ 5 = 1) : Z ⊓ W = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgZ, hgW⟩ := hg
  obtain ⟨n, hn⟩ := hZ ⟨g, hgZ⟩
  have h1 : g ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h2 : g ^ 5 = 1 := hW g hgW
  have hdvd : orderOf g ∣ Nat.gcd (2 ^ n) 5 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.gcd (2 ^ n) 5 = 1 := by
    apply Nat.Coprime.pow_left
    norm_num
  rw [hcop] at hdvd
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd))

end Generic

structure IsFrob {Γ : Type*} [Group Γ] (x y : Γ) : Prop where
  x5 : x ^ 5 = 1
  x1 : x ≠ 1
  y4 : y ^ 4 = 1
  yx : y * x * y⁻¹ = x ^ 3

namespace IsFrob

variable {Γ : Type*} [Group Γ] {x y : Γ}

theorem orderOf_x (h : IsFrob x y) : orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.x5 h.x1

theorem card_zpowers_x (h : IsFrob x y) : Nat.card (zpowers x) = 5 := by
  rw [Nat.card_zpowers, h.orderOf_x]

theorem y_pow_conj (h : IsFrob x y) (b : ℕ) : y ^ b * x * (y ^ b)⁻¹ = x ^ (3 ^ b) := by
  induction b with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by group
      _ = y * x ^ (3 ^ n) * y⁻¹ := by rw [ih]
      _ = (y * x * y⁻¹) ^ (3 ^ n) := by rw [conj_pow]
      _ = (x ^ 3) ^ (3 ^ n) := by rw [h.yx]
      _ = x ^ (3 ^ (n + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

theorem x_pow_eq_one_iff (h : IsFrob x y) (n : ℕ) : x ^ n = 1 ↔ 5 ∣ n := by
  rw [← h.orderOf_x]
  exact orderOf_dvd_iff_pow_eq_one.symm

theorem four_dvd_of_comm (h : IsFrob x y) (b : ℕ) (hc : y ^ b * x = x * y ^ b) : 4 ∣ b := by
  have h1 : x ^ (3 ^ b) = x := by
    rw [← h.y_pow_conj b, hc]
    group
  have h2 : x ^ (3 ^ b - 1) = 1 := by
    have h3 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have : x ^ (3 ^ b) = x ^ (3 ^ b - 1) * x := by
      rw [← pow_succ, Nat.sub_add_cancel h3]
    rw [this] at h1
    exact mul_eq_right.1 h1
  have h5 : 5 ∣ 3 ^ b - 1 := (h.x_pow_eq_one_iff _).1 h2
  have hmod : 3 ^ b % 5 = 1 := by
    have h3 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hb : b % 4 = 0 := by
    have key : ∀ r : ℕ, r < 4 → 3 ^ r % 5 = 1 → r = 0 := by decide
    have hpow : 3 ^ b % 5 = 3 ^ (b % 4) % 5 := by
      conv_lhs => rw [← Nat.mod_add_div b 4, pow_add, pow_mul]
      rw [Nat.mul_mod, Nat.pow_mod (3 ^ 4) (b / 4) 5]
      norm_num
    exact key _ (Nat.mod_lt _ (by norm_num)) (hpow ▸ hmod)
  omega

theorem orderOf_y (h : IsFrob x y) : orderOf y = 4 := by
  have h2 : ¬ y ^ 2 ^ 1 = 1 := by
    intro hy
    have := h.four_dvd_of_comm 2 (by
      have : y ^ 2 = 1 := by simpa using hy
      rw [this]
      simp)
    omega
  have h4 : y ^ 2 ^ (1 + 1) = 1 := by simpa using h.y4
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  simpa using this

theorem card_zpowers_y (h : IsFrob x y) : Nat.card (zpowers y) = 4 := by
  rw [Nat.card_zpowers, h.orderOf_y]

theorem y_mem_normalizer (h : IsFrob x y) : y ∈ normalizer (zpowers x : Set Γ) := by
  have hback : y⁻¹ * x * y = x ^ 2 := by
    have hw5 : (y⁻¹ * x * y) ^ 5 = 1 := by
      rw [show y⁻¹ * x * y = (y⁻¹)  * x * (y⁻¹)⁻¹ by simp, conj_pow, h.x5]
      group
    have hw3 : (y⁻¹ * x * y) ^ 3 = x := by
      rw [show y⁻¹ * x * y = (y⁻¹) * x * (y⁻¹)⁻¹ by simp, conj_pow, ← h.yx]
      group
    calc y⁻¹ * x * y = (y⁻¹ * x * y) ^ 6 := by
          rw [show (6 : ℕ) = 5 + 1 from rfl, pow_add, hw5, one_mul, pow_one]
      _ = ((y⁻¹ * x * y) ^ 3) ^ 2 := by rw [← pow_mul]
      _ = x ^ 2 := by rw [hw3]
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨3 * n, ?_⟩
    show x ^ (3 * n) = y * x ^ n * y⁻¹
    rw [← conj_zpow, h.yx, ← zpow_natCast, ← zpow_mul]
    norm_num
  · rintro ⟨n, hn⟩
    refine ⟨2 * n, ?_⟩
    have hg : g = y⁻¹ * (y * g * y⁻¹) * y := by group
    have hn' : x ^ n = y * g * y⁻¹ := hn
    show x ^ (2 * n) = g
    have hc : y⁻¹ * x ^ n * y = (y⁻¹ * x * y) ^ n := by
      have := conj_zpow (a := y⁻¹) (b := x) (i := n)
      rw [inv_inv] at this
      exact this.symm
    rw [hg, ← hn', hc, hback, ← zpow_natCast, ← zpow_mul]
    norm_num

theorem pow_five_eq_one_of_mem_zpowers (h : IsFrob x y) {g : Γ} (hg : g ∈ zpowers x) : g ^ 5 = 1 := by
  obtain ⟨n, rfl⟩ := hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.x5, one_zpow]

theorem pow_four_eq_one_of_mem_zpowers (h : IsFrob x y) {g : Γ} (hg : g ∈ zpowers y) : g ^ 4 = 1 := by
  obtain ⟨n, rfl⟩ := hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.y4, one_zpow]

theorem inf_eq_bot (h : IsFrob x y) : zpowers x ⊓ zpowers y = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hg1, hg2⟩ := hg
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (h.pow_five_eq_one_of_mem_zpowers hg1))
    (orderOf_dvd_of_pow_eq_one (h.pow_four_eq_one_of_mem_zpowers hg2))
  have hcop : Nat.gcd 5 4 = 1 := by norm_num
  rw [hcop] at hd
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd))

theorem zpowers_y_le_normalizer (h : IsFrob x y) : zpowers y ≤ normalizer (zpowers x : Set Γ) :=
  zpowers_le.2 h.y_mem_normalizer

theorem card_sup (h : IsFrob x y) : Nat.card (zpowers x ⊔ zpowers y : Subgroup Γ) = 20 := by
  rw [card_sup_of_inf_eq_bot' h.zpowers_y_le_normalizer h.inf_eq_bot, h.card_zpowers_x,
    h.card_zpowers_y]

theorem sup_le_normalizer (h : IsFrob x y) :
    (zpowers x ⊔ zpowers y : Subgroup Γ) ≤ normalizer (zpowers x : Set Γ) :=
  sup_le Subgroup.le_normalizer h.zpowers_y_le_normalizer

theorem mem_sup_iff (h : IsFrob x y) {g : Γ} :
    g ∈ (zpowers x ⊔ zpowers y : Subgroup Γ) ↔ ∃ b : ℕ, ∃ m : ℤ, g = y ^ b * x ^ m := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers y) (zpowers x)
    h.zpowers_y_le_normalizer
  rw [sup_comm]
  constructor
  · intro hg
    have hg' : g ∈ ((zpowers y ⊔ zpowers x : Subgroup Γ) : Set Γ) := hg
    rw [hset] at hg'
    obtain ⟨a, ⟨k, rfl⟩, c, ⟨m, rfl⟩, rfl⟩ := hg'
    refine ⟨(k % 4).toNat, m, ?_⟩
    have hk : y ^ (k % 4) = y ^ k := by
      have := zpow_mod_orderOf y k
      rwa [h.orderOf_y] at this
    have hnn : ((k % 4).toNat : ℤ) = k % 4 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    show y ^ k * x ^ m = y ^ (k % 4).toNat * x ^ m
    rw [← zpow_natCast, hnn, hk]
  · rintro ⟨b, m, rfl⟩
    exact mul_mem (pow_mem (mem_sup_left (mem_zpowers y)) b) (zpow_mem (mem_sup_right (mem_zpowers x)) m)

theorem mem_zpowers_of_comm (h : IsFrob x y) {g : Γ} (hg : g ∈ (zpowers x ⊔ zpowers y : Subgroup Γ))
    (hc : g * x = x * g) : g ∈ zpowers x := by
  obtain ⟨b, m, rfl⟩ := h.mem_sup_iff.1 hg
  have hxm : x ^ m * x = x * x ^ m := (Commute.zpow_left (Commute.refl x) m).eq
  have hyb : y ^ b * x = x * y ^ b := by
    have h1 : y ^ b * x * x ^ m = x * y ^ b * x ^ m := by
      calc y ^ b * x * x ^ m = y ^ b * (x * x ^ m) := by group
        _ = y ^ b * (x ^ m * x) := by rw [hxm]
        _ = (y ^ b * x ^ m) * x := by group
        _ = x * (y ^ b * x ^ m) := hc
        _ = x * y ^ b * x ^ m := by group
    exact mul_right_cancel h1
  obtain ⟨q, rfl⟩ := h.four_dvd_of_comm b hyb
  rw [pow_mul, h.y4, one_pow, one_mul]
  exact zpow_mem (mem_zpowers x) m

theorem inf_eq_bot_of_isPGroup (h : IsFrob x y) {Z : Subgroup Γ} (hZ : IsPGroup 2 Z)
    (hxZ : x ∈ normalizer (Z : Set Γ)) :
    Z ⊓ (zpowers x ⊔ zpowers y : Subgroup Γ) = ⊥ := by
  have hZW : Z ⊓ zpowers x = ⊥ :=
    inf_eq_bot_of_isPGroup_of_pow_five hZ fun g hg => h.pow_five_eq_one_of_mem_zpowers hg
  refine eq_bot_iff.2 fun w hw => ?_
  obtain ⟨hwZ, hwK⟩ := hw
  have hwN : w ∈ normalizer (zpowers x : Set Γ) := h.sup_le_normalizer hwK
  have hc : w * x * w⁻¹ * x⁻¹ ∈ Z ⊓ zpowers x := by
    refine ⟨?_, ?_⟩
    · have e : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
      rw [e]
      exact Z.mul_mem hwZ ((mem_normalizer_iff.1 hxZ _).1 (Z.inv_mem hwZ))
    · exact (zpowers x).mul_mem ((mem_normalizer_iff.1 hwN x).1 (mem_zpowers x))
        ((zpowers x).inv_mem (mem_zpowers x))
  rw [hZW, mem_bot] at hc
  have hcomm : w * x = x * w := by
    calc w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
      _ = x * w := by rw [hc, one_mul]
  have hwx : w ∈ zpowers x := h.mem_zpowers_of_comm hwK hcomm
  have : w ∈ Z ⊓ zpowers x := ⟨hwZ, hwx⟩
  rwa [hZW] at this

theorem card_sup_of_isPGroup (h : IsFrob x y) {Z : Subgroup Γ} (hZ : IsPGroup 2 Z)
    (hxZ : x ∈ normalizer (Z : Set Γ)) (hyZ : y ∈ normalizer (Z : Set Γ)) :
    Nat.card (Z ⊔ zpowers x ⊔ zpowers y : Subgroup Γ) = 20 * Nat.card Z := by
  rw [sup_assoc, card_sup_of_inf_eq_bot' (X := Z) (Y := zpowers x ⊔ zpowers y)
    (sup_le (zpowers_le.2 hxZ) (zpowers_le.2 hyZ)) (h.inf_eq_bot_of_isPGroup hZ hxZ), h.card_sup,
    Nat.mul_comm]

theorem centralizer_inf_eq (h : IsFrob x y) :
    (zpowers x ⊔ zpowers y : Subgroup Γ) ⊓ centralizer ({x} : Set Γ) = zpowers x := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨mem_sup_left hg, ?_⟩)
  · obtain ⟨hgK, hgc⟩ := hg
    have : g * x = x * g := mem_centralizer_singleton_iff.1 hgc
    exact h.mem_zpowers_of_comm hgK this
  · obtain ⟨n, rfl⟩ := hg
    exact mem_centralizer_singleton_iff.2 (Commute.zpow_left (Commute.refl x) n).eq

end IsFrob

end CFSG.LocalAnalysis.EvenBN.Tits.N
