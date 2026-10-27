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

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

section DAction

variable {G : Type*} [Group G] {a c : G}

theorem three_dvd_of_zpow_eq_one {x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {i : ℤ}
    (h : x ^ i = 1) : (3 : ℤ) ∣ i := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hxo] at this
  exact_mod_cast this

theorem pow_mul_pow_eq_one (ha1 : a ≠ 1) (hc1 : c ≠ 1) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hnot : c ∉ Subgroup.zpowers a) {i j : ℤ} (h : c ^ i * a ^ j = 1) :
    (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
  have hci : c ^ i ∈ Subgroup.zpowers a := by
    have : c ^ i = (a ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j)
  have hi : (3 : ℤ) ∣ i := by
    by_contra hnd
    apply hnot
    have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hmod : c ^ i = c ^ (i % 3) := by
      have := zpow_mod_orderOf c i
      rw [hc3'] at this
      exact_mod_cast this.symm
    have h12 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h12 with h1 | h2
    · rw [hmod, h1, zpow_one] at hci; exact hci
    · rw [hmod, h2] at hci
      have h4 : c = (c ^ (2 : ℤ)) ^ (2 : ℕ) := by
        rw [← zpow_natCast, ← zpow_mul]
        have : c ^ (2 * (2 : ℕ) : ℤ) = c ^ (3 : ℤ) * c := by
          rw [← zpow_add_one]; norm_num
        rw [show ((2 : ℤ) * ((2 : ℕ) : ℤ)) = 3 + 1 by norm_num, zpow_add_one]
        have h3z : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
        rw [h3z, one_mul]
      rw [h4]
      exact Subgroup.pow_mem _ hci 2
  have hc : c ^ i = 1 := by
    obtain ⟨k, rfl⟩ := hi
    rw [zpow_mul]
    have h3z : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
    rw [h3z, one_zpow]
  rw [hc, one_mul] at h
  exact ⟨hi, three_dvd_of_zpow_eq_one ha3 ha1 h⟩

theorem pow_mod_three {g : G} (hg : g ^ 3 = 1) (n : ℕ) : g ^ (n % 3) = g ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hg, one_pow, mul_one]

theorem pow_val_add {g : G} (hg : g ^ 3 = 1) (x y : ZMod 3) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  rw [← pow_add, ZMod.val_add, pow_mod_three hg]

@[expose] def kap (a c : G) (x : ZMod 3 × ZMod 3) : G := c ^ x.1.val * a ^ x.2.val

variable (hca : c * a = a * c) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
include hca ha3 hc3

theorem kap_add (x y : ZMod 3 × ZMod 3) : kap a c (x + y) = kap a c x * kap a c y := by
  unfold kap
  simp only [Prod.fst_add, Prod.snd_add, pow_val_add hc3, pow_val_add ha3]
  have h : ∀ m n : ℕ, a ^ m * c ^ n = c ^ n * a ^ m := fun m n =>
    ((Commute.pow_pow (show Commute a c from hca.symm) m n).eq)
  calc c ^ x.1.val * c ^ y.1.val * (a ^ x.2.val * a ^ y.2.val)
      = c ^ x.1.val * (c ^ y.1.val * a ^ x.2.val) * a ^ y.2.val := by group
    _ = c ^ x.1.val * (a ^ x.2.val * c ^ y.1.val) * a ^ y.2.val := by rw [← h]
    _ = _ := by group

theorem kap_zero : kap a c 0 = 1 := by simp [kap]


theorem kap_neg (x : ZMod 3 × ZMod 3) : kap a c (-x) = (kap a c x)⁻¹ := by
  have h0 : x + -x = 0 := add_neg_cancel x
  have := kap_add hca ha3 hc3 x (-x)
  rw [h0, kap_zero hca ha3 hc3] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem kap_inj (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hnot : c ∉ Subgroup.zpowers a)
    {x y : ZMod 3 × ZMod 3} (h : kap a c x = kap a c y) : x = y := by
  have h1 : kap a c (x - y) = 1 := by
    have h0 : x - y + y = x := sub_add_cancel x y
    have := kap_add hca ha3 hc3 (x - y) y
    rw [h0, h] at this
    have h2 : kap a c (x - y) * kap a c y = 1 * kap a c y := by rw [← this, one_mul]
    exact mul_right_cancel h2
  have h2 := pow_mul_pow_eq_one ha1 hc1 ha3 hc3 hnot (i := ((x - y).1.val : ℤ))
    (j := ((x - y).2.val : ℤ)) (by
      rw [zpow_natCast, zpow_natCast]; exact h1)
  have hlt1 := ZMod.val_lt (x - y).1
  have hlt2 := ZMod.val_lt (x - y).2
  have h3 : (x - y).1.val = 0 := by omega
  have h4 : (x - y).2.val = 0 := by omega
  have h5 : x - y = 0 :=
    Prod.ext (by simpa using (ZMod.val_eq_zero _).1 h3) (by simpa using (ZMod.val_eq_zero _).1 h4)
  exact sub_eq_zero.1 h5

theorem mem_D_iff {x : G} : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c ↔
    ∃ v : ZMod 3 × ZMod 3, x = kap a c v := by
  let R : Subgroup G :=
    { carrier := Set.range (kap a c)
      one_mem' := ⟨0, kap_zero hca ha3 hc3⟩
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, kap_add hca ha3 hc3 x y⟩
      inv_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨-x, kap_neg hca ha3 hc3 x⟩ }
  constructor
  · intro hx
    have h10 : (1 : ZMod 3).val = 1 := rfl
    have ha : a ∈ R := ⟨(0, 1), by simp [kap, h10]⟩
    have hc : c ∈ R := ⟨(1, 0), by simp [kap, h10]⟩
    have hxR : x ∈ R := (sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hc) : _ ≤ R) hx
    obtain ⟨v, hv⟩ := hxR
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, rfl⟩
    unfold kap
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) _)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) _)

@[expose] def Acts (a c g : G) (f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3) : Prop :=
  ∀ x, kap a c (f x) = g * kap a c x * g⁻¹

theorem acts_exists {g : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) : Set G)) :
    ∃ f, Acts a c g f := by
  have : ∀ x : ZMod 3 × ZMod 3, ∃ y, kap a c y = g * kap a c x * g⁻¹ := by
    intro x
    have hx : kap a c x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      (mem_D_iff hca ha3 hc3).2 ⟨x, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hg _).1 hx
    obtain ⟨y, hy⟩ := (mem_D_iff hca ha3 hc3).1 this
    exact ⟨y, hy.symm⟩
  choose f hf using this
  exact ⟨f, hf⟩

variable (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hnot : c ∉ Subgroup.zpowers a)
include ha1 hc1 hnot

theorem acts_unique {g : G} {f f' : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (h : Acts a c g f)
    (h' : Acts a c g f') : f = f' := by
  funext x
  exact kap_inj hca ha3 hc3 ha1 hc1 hnot ((h x).trans (h' x).symm)

theorem acts_mul {g h' : G} {f f' : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (hf : Acts a c g f)
    (hf' : Acts a c h' f') : Acts a c (g * h') (f ∘ f') := by
  intro x
  show kap a c (f (f' x)) = _
  rw [hf, hf']
  group

theorem acts_one : Acts a c (1 : G) id := by
  intro x; simp

theorem acts_add {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (hf : Acts a c g f)
    (x y : ZMod 3 × ZMod 3) : f (x + y) = f x + f y := by
  apply kap_inj hca ha3 hc3 ha1 hc1 hnot
  rw [kap_add hca ha3 hc3, hf, hf, hf, kap_add hca ha3 hc3]
  group

theorem acts_id_iff {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (hf : Acts a c g f) :
    f = id ↔ ∀ δ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c, g * δ = δ * g := by
  constructor
  · rintro rfl δ hδ
    obtain ⟨v, rfl⟩ := (mem_D_iff hca ha3 hc3).1 hδ
    have := hf v
    simp only [id] at this
    calc g * kap a c v = (g * kap a c v * g⁻¹) * g := by group
      _ = kap a c v * g := by rw [← this]
  · intro h
    funext x
    apply kap_inj hca ha3 hc3 ha1 hc1 hnot
    rw [hf]
    have := h (kap a c x) ((mem_D_iff hca ha3 hc3).2 ⟨x, rfl⟩)
    simp only [id]
    calc g * kap a c x * g⁻¹ = (kap a c x * g) * g⁻¹ := by rw [← this]
      _ = kap a c x := by group

theorem kap_mem_zpowers_c_iff (v : ZMod 3 × ZMod 3) :
    kap a c v ∈ Subgroup.zpowers c ↔ v.2 = 0 := by
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hv
    have h1 : c ^ (v.1.val - n) * a ^ (v.2.val : ℤ) = 1 := by
      rw [zpow_sub, hn]
      simp only [kap, ← zpow_natCast]
      have e : a ^ (-(v.2.val : ℤ)) * c ^ (-(v.1.val : ℤ)) =
          c ^ (-(v.1.val : ℤ)) * a ^ (-(v.2.val : ℤ)) :=
        (Commute.zpow_zpow (show Commute a c from hca.symm) _ _).eq
      calc c ^ (v.1.val : ℤ) * (c ^ (v.1.val : ℤ) * a ^ (v.2.val : ℤ))⁻¹ * a ^ (v.2.val : ℤ)
          = c ^ (v.1.val : ℤ) * (a ^ (-(v.2.val : ℤ)) * c ^ (-(v.1.val : ℤ))) *
              a ^ (v.2.val : ℤ) := by group
        _ = c ^ (v.1.val : ℤ) * (c ^ (-(v.1.val : ℤ)) * a ^ (-(v.2.val : ℤ))) *
              a ^ (v.2.val : ℤ) := by rw [e]
        _ = 1 := by group
    have h2 := (pow_mul_pow_eq_one ha1 hc1 ha3 hc3 hnot h1).2
    have h3 := ZMod.val_lt v.2
    have : v.2.val = 0 := by omega
    exact (ZMod.val_eq_zero _).1 this
  · intro hv
    have : kap a c v = c ^ v.1.val := by
      simp [kap, hv]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _

theorem kap_mem_zpowers_a_iff (v : ZMod 3 × ZMod 3) :
    kap a c v ∈ Subgroup.zpowers a ↔ v.1 = 0 := by
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hv
    have h1 : c ^ (v.1.val : ℤ) * a ^ (v.2.val - n) = 1 := by
      rw [zpow_sub, hn]
      simp only [kap, zpow_natCast]
      have hac : ∀ m : ℕ, a ^ m * c ^ v.1.val = c ^ v.1.val * a ^ m := fun m =>
        (Commute.pow_pow (show Commute a c from hca.symm) m v.1.val).eq
      group
    have h2 := (pow_mul_pow_eq_one ha1 hc1 ha3 hc3 hnot h1).1
    have h3 := ZMod.val_lt v.1
    have : v.1.val = 0 := by omega
    exact (ZMod.val_eq_zero _).1 this
  · intro hv
    have : kap a c v = a ^ v.2.val := by
      simp [kap, hv]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _

end DAction

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
