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

open scoped Pointwise

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

variable {G : Type*} [Group G]

section Coset

variable {C : Subgroup G} {r : G}

theorem conj_pow_mem (hrC : ∀ x ∈ C, r * x * r⁻¹ ∈ C) :
    ∀ (j : ℕ), ∀ x ∈ C, r ^ j * x * (r ^ j)⁻¹ ∈ C
  | 0 => fun x hx => by simpa using hx
  | j + 1 => fun x hx => by
    have e : r ^ (j + 1) * x * (r ^ (j + 1))⁻¹ = r * (r ^ j * x * (r ^ j)⁻¹) * r⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact hrC _ (conj_pow_mem hrC j x hx)

theorem inv_eq_pow_orderOf_sub_one' [Finite G] (x : G) : x⁻¹ = x ^ (orderOf x - 1) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]

theorem exists_mul_pow_of_mem_closure [Finite G] (hrC : ∀ x ∈ C, r * x * r⁻¹ ∈ C) {b : G}
    (hb : b ∈ Subgroup.closure ((C : Set G) ∪ {r})) : ∃ c ∈ C, ∃ j : ℕ, b = c * r ^ j := by
  induction hb using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨1, C.one_mem, 1, by simp⟩
  | inv_mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x⁻¹, C.inv_mem hx, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, C.one_mem, orderOf x - 1, by rw [one_mul, inv_eq_pow_orderOf_sub_one']⟩
  | one => exact ⟨1, C.one_mem, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c₁, hc₁, j₁, rfl⟩ := hx
    obtain ⟨c₂, hc₂, j₂, rfl⟩ := hy
    refine ⟨c₁ * (r ^ j₁ * c₂ * (r ^ j₁)⁻¹), C.mul_mem hc₁ (conj_pow_mem hrC j₁ c₂ hc₂), j₁ + j₂,
      ?_⟩
    rw [pow_add]; group

theorem conj_mem_coset [Finite G] (hrC : ∀ x ∈ C, r * x * r⁻¹ ∈ C) {b c : G}
    (hb : b ∈ Subgroup.closure ((C : Set G) ∪ {r})) (hc : c ∈ C) :
    b * (c * r) * b⁻¹ * r⁻¹ ∈ C := by
  obtain ⟨c', hc', j, rfl⟩ := exists_mul_pow_of_mem_closure hrC hb
  have e : c' * r ^ j * (c * r) * (c' * r ^ j)⁻¹ * r⁻¹ =
      c' * (r ^ j * c * (r ^ j)⁻¹) * (r * c'⁻¹ * r⁻¹) := by group
  rw [e]
  exact C.mul_mem (C.mul_mem hc' (conj_pow_mem hrC j c hc)) (hrC _ (C.inv_mem hc'))

theorem pow_mem_iff_three_dvd (hr3 : r ^ 3 ∈ C) (hrnC : r ∉ C) (j : ℕ) (hj : r ^ j ∈ C) :
    3 ∣ j := by
  have hq : r ^ j = (r ^ 3) ^ (j / 3) * r ^ (j % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hs : r ^ (j % 3) ∈ C := by
    have := C.mul_mem (C.inv_mem (C.pow_mem hr3 (j / 3))) hj
    rwa [hq, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have h3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : j % 3
  · exact Nat.dvd_of_mod_eq_zero h
  · exact absurd (by simpa using hs) hrnC
  · exfalso; apply hrnC
    have := C.mul_mem hr3 (C.inv_mem hs)
    rwa [show r ^ 3 * (r ^ 2)⁻¹ = r by group] at this

theorem exists_conj_eq_mul_zpowers [Finite G] {w c : G} (hw : orderOf w = 3) (hwC : w ∈ C)
    (hrw : r * w = w * r) (hCw : ∀ x ∈ C, x * w = w * x)
    (hP : ∀ P : Subgroup G, P ≤ C → IsPGroup 3 P → P ≤ Subgroup.zpowers w)
    (hrC : ∀ x ∈ C, r * x * r⁻¹ ∈ C) (hr3 : r ^ 3 ∈ Subgroup.zpowers w) (hrnC : r ∉ C)
    (hc : c ∈ C) (hy3 : (c * r) ^ 3 = 1) :
    ∃ b : G, ∃ z ∈ Subgroup.zpowers w, b * (c * r) * b⁻¹ = r * z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.closure ((C : Set G) ∪ {r}) with hBdef
  have hCB : C ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hrB : r ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hyB : c * r ∈ B := B.mul_mem (hCB hc) hrB
  have hZC : Subgroup.zpowers w ≤ C := (Subgroup.zpowers_le).2 hwC
  have hr3C : r ^ 3 ∈ C := hZC hr3
  have hwcent : ∀ x ∈ B, x * w = w * x := by
    intro x hx
    obtain ⟨c', hc', j, rfl⟩ := exists_mul_pow_of_mem_closure hrC hx
    have hrjw : r ^ j * w = w * r ^ j := ((Commute.pow_left hrw j)).eq
    calc c' * r ^ j * w = c' * (r ^ j * w) := by group
      _ = c' * (w * r ^ j) := by rw [hrjw]
      _ = c' * w * r ^ j := by group
      _ = w * c' * r ^ j := by rw [hCw c' hc']
      _ = w * (c' * r ^ j) := by group
  let Z : Subgroup B := (Subgroup.zpowers w).subgroupOf B
  have hZn : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.zpowers w := hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn'
    show ((g * n * g⁻¹ : B) : G) ∈ Subgroup.zpowers w
    have hgw : (g : G) * w ^ k = w ^ k * g := ((Commute.zpow_right (hwcent g g.2) k)).eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk]
    rw [hgw, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers w k
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hzpow3 : ∀ z ∈ Subgroup.zpowers w, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have hZp : IsPGroup 3 Z := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have h := hzpow3 _ (Subgroup.mem_subgroupOf.1 g.2)
    simpa using h
  have hr9 : r ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by norm_num, pow_mul]; exact hzpow3 _ hr3
  have hrp : IsPGroup 3 (Subgroup.zpowers (⟨r, hrB⟩ : B)) := by
    refine fun g => ⟨2, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_pow, ← hk, Subgroup.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((3 ^ 2 : ℕ) : ℤ) = 9 by norm_num,
      show (r ^ (9 : ℤ)) = r ^ (9 : ℕ) from zpow_natCast r 9, hr9, one_zpow]
  have hyp : IsPGroup 3 (Subgroup.zpowers (⟨c * r, hyB⟩ : B)) := by
    refine fun g => ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_pow, ← hk, Subgroup.coe_zpow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  obtain ⟨P, hrP⟩ := hrp.exists_le_sylow
  have hZP : Z ≤ P := hZp.le_sylow_of_normal P
  obtain ⟨P', hyP'⟩ := hyp.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B P' P
  have hbyP : b * ⟨c * r, hyB⟩ * b⁻¹ ∈ (P : Subgroup B) := by
    have h1 : (⟨c * r, hyB⟩ : B) ∈ (P' : Subgroup B) := hyP' (Subgroup.mem_zpowers _)
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj b) (P' : Subgroup B) h1
    have h3 : ((b • P' : Sylow 3 B) : Subgroup B) = MulAut.conj b • (P' : Subgroup B) := rfl
    rw [← h3, hb] at h2
    simpa [MulAut.smul_def] using h2
  set p : B := b * ⟨c * r, hyB⟩ * b⁻¹ with hp
  obtain ⟨c', hc', j, hpj⟩ := exists_mul_pow_of_mem_closure hrC p.2
  have hc'P : (⟨c', hCB hc'⟩ : B) ∈ (P : Subgroup B) := by
    have hrj : (⟨r, hrB⟩ : B) ^ j ∈ (P : Subgroup B) :=
      Subgroup.pow_mem _ (hrP (Subgroup.mem_zpowers _)) j
    have := Subgroup.mul_mem _ hbyP (Subgroup.inv_mem _ hrj)
    convert this using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [hpj]; group
  have hc'Z : c' ∈ Subgroup.zpowers w := by
    have hle : ((P : Subgroup B).map B.subtype) ⊓ C ≤ Subgroup.zpowers w :=
      hP _ inf_le_right ((P.isPGroup'.map B.subtype).to_inf_left)
    exact hle ⟨⟨⟨c', hCB hc'⟩, hc'P, rfl⟩, hc'⟩
  have hcos := conj_mem_coset hrC b.2 hc
  have hcos' : (p : G) * r⁻¹ ∈ C := by
    rw [hp]; simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcos
  rw [hpj] at hcos'
  have hrj1 : r ^ j * r⁻¹ ∈ C := by
    have := C.mul_mem (C.inv_mem (hZC hc'Z)) hcos'
    rwa [show c'⁻¹ * (c' * r ^ j * r⁻¹) = r ^ j * r⁻¹ by group] at this
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hrnC (by simpa using C.inv_mem hrj1)
  obtain ⟨i, hi⟩ : 3 ∣ (j - 1) := by
    refine pow_mem_iff_three_dvd hr3C hrnC (j - 1) ?_
    have e : r ^ j = r ^ (j - 1) * r := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0)]
    rwa [show r ^ j * r⁻¹ = r ^ (j - 1) by rw [e]; group] at hrj1
  have hj : j = 3 * i + 1 := by omega
  refine ⟨b, c' * (r ^ 3) ^ i, Subgroup.mul_mem _ hc'Z (Subgroup.pow_mem _ hr3 i), ?_⟩
  have hcomm : c' * r = r * c' := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'Z
    exact ((Commute.zpow_left hrw.symm k)).eq
  calc b * (c * r) * b⁻¹ = (p : G) := by rw [hp]; rfl
    _ = c' * r ^ j := hpj
    _ = c' * r * (r ^ 3) ^ i := by rw [hj, ← pow_mul, pow_succ', mul_assoc]
    _ = r * (c' * (r ^ 3) ^ i) := by rw [hcomm, mul_assoc]

end Coset

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
