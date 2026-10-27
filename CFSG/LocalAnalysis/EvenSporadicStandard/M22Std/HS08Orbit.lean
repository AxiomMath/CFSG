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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

noncomputable def conjOrb (N : Subgroup G) (x : G) : Finset G :=
  Finset.univ.filter fun y => ∃ n ∈ N, y = n * x * n⁻¹

theorem mem_conjOrb {N : Subgroup G} {x y : G} : y ∈ conjOrb N x ↔ ∃ n ∈ N, y = n * x * n⁻¹ := by
  simp [conjOrb]

theorem self_mem_conjOrb (N : Subgroup G) (x : G) : x ∈ conjOrb N x :=
  mem_conjOrb.2 ⟨1, N.one_mem, by simp⟩

theorem conj_mem_conjOrb {N : Subgroup G} {x y n : G} (hn : n ∈ N) (hy : y ∈ conjOrb N x) :
    n * y * n⁻¹ ∈ conjOrb N x := by
  obtain ⟨m, hm, rfl⟩ := mem_conjOrb.1 hy
  exact mem_conjOrb.2 ⟨n * m, N.mul_mem hn hm, by group⟩

theorem conjOrb_invariant {N : Subgroup G} {x y n : G} (hn : n ∈ N) :
    y ∈ conjOrb N x ↔ n * y * n⁻¹ ∈ conjOrb N x := by
  refine ⟨conj_mem_conjOrb hn, fun hy => ?_⟩
  have := conj_mem_conjOrb (N.inv_mem hn) hy
  simpa [mul_assoc] using this

theorem conjOrb_eq_of_mem {N : Subgroup G} {x y : G} (hy : y ∈ conjOrb N x) :
    conjOrb N y = conjOrb N x := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hz
    exact conj_mem_conjOrb hn hy
  · intro hz
    obtain ⟨m, hm, rfl⟩ := mem_conjOrb.1 hy
    obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hz
    exact mem_conjOrb.2 ⟨n * m⁻¹, N.mul_mem hn (N.inv_mem hm), by group⟩

theorem card_conjOrb_mul (N : Subgroup G) (x : G) :
    (conjOrb N x).card * Nat.card ↥(N ⊓ centralizer ({x} : Set G)) = Nat.card N := by
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (y : G), n • y = (n : G) * y * (n : G)⁻¹ := fun n y => rfl
  have h1 := MulAction.index_stabilizer N x
  have h2 := (MulAction.stabilizer N x).card_mul_index
  have horb : (MulAction.orbit N x).ncard = (conjOrb N x).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_conjOrb, hsmul]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstab : Nat.card (MulAction.stabilizer N x) = Nat.card ↥(N ⊓ centralizer ({x} : Set G)) := by
    have : MulAction.stabilizer N x = (centralizer ({x} : Set G)).subgroupOf N := by
      ext n
      simp only [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc (n : G) * x = ((n : G) * x * (n : G)⁻¹) * (n : G) := by group
          _ = x * (n : G) := by rw [h]
      · intro h
        calc (n : G) * x * (n : G)⁻¹ = (x * (n : G)) * (n : G)⁻¹ := by rw [h]
          _ = x := by group
    rw [this, ← Subgroup.inf_subgroupOf_right]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      centralizer ({x} : Set G) ⊓ N ≤ N)).toEquiv).trans ?_
    rw [inf_comm]
  rw [horb] at h1
  rw [hstab, h1] at h2
  rw [mul_comm]
  exact h2

omit [Fintype G] in
theorem card_filter_pair (t : G) (ht2 : t * t = 1) (F : Finset G) (hF : ∀ x ∈ F, t * x ∈ F)
    (X : Finset G) {c : ℕ}
    (hc : ∀ x ∈ F, (if x ∈ X then 1 else 0) + (if t * x ∈ X then 1 else 0) = c) :
    2 * (F.filter (· ∈ X)).card = F.card * c := by
  have h1 : ∑ x ∈ F, (if x ∈ X then 1 else 0) = (F.filter (· ∈ X)).card :=
    (Finset.card_filter (· ∈ X) F).symm
  have h2 : ∑ x ∈ F, (if t * x ∈ X then 1 else 0) = ∑ x ∈ F, (if x ∈ X then 1 else 0) := by
    refine Finset.sum_nbij' (fun x => t * x) (fun x => t * x) (fun x hx => hF x hx)
      (fun x hx => hF x hx) (fun x _ => ?_) (fun x _ => ?_) (fun x _ => rfl)
    · rw [← mul_assoc, ht2, one_mul]
    · rw [← mul_assoc, ht2, one_mul]
  calc 2 * (F.filter (· ∈ X)).card
      = ∑ x ∈ F, (if x ∈ X then 1 else 0) + ∑ x ∈ F, (if t * x ∈ X then 1 else 0) := by
        rw [h2, h1]; ring
    _ = ∑ x ∈ F, ((if x ∈ X then 1 else 0) + (if t * x ∈ X then 1 else 0)) :=
        (Finset.sum_add_distrib).symm
    _ = F.card * c := by
        rw [Finset.sum_congr rfl hc]
        simp

omit [Fintype G] in
theorem exists_pair_count (N : Subgroup G) (t : G) (ht2 : t * t = 1) (F : Finset G)
    (hF : ∀ x ∈ F, t * x ∈ F) (hF0 : F.Nonempty)
    (hTrans : ∀ x ∈ F, ∀ y ∈ F,
      ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y))
    (X : Finset G) (hX : ∀ n ∈ N, n * t = t * n → ∀ x, x ∈ X ↔ n * x * n⁻¹ ∈ X) :
    ∃ c : ℕ, c ≤ 2 ∧ (∀ x ∈ F, (if x ∈ X then 1 else 0) + (if t * x ∈ X then 1 else 0) = c) ∧
      2 * (F.filter (· ∈ X)).card = F.card * c := by
  obtain ⟨x₀, hx₀⟩ := hF0
  set c : ℕ := (if x₀ ∈ X then 1 else 0) + (if t * x₀ ∈ X then 1 else 0) with hcdef
  have hall : ∀ x ∈ F, (if x ∈ X then 1 else 0) + (if t * x ∈ X then 1 else 0) = c := by
    intro x hx
    obtain ⟨n, hn, hnt, h⟩ := hTrans x₀ hx₀ x hx
    have hnt' : n * (t * x₀) * n⁻¹ = t * (n * x₀ * n⁻¹) := by
      calc n * (t * x₀) * n⁻¹ = (n * t) * x₀ * n⁻¹ := by group
        _ = (t * n) * x₀ * n⁻¹ := by rw [hnt]
        _ = t * (n * x₀ * n⁻¹) := by group
    have e1 : x₀ ∈ X ↔ n * x₀ * n⁻¹ ∈ X := hX n hn hnt x₀
    have e2 : t * x₀ ∈ X ↔ t * (n * x₀ * n⁻¹) ∈ X := by
      rw [← hnt']; exact hX n hn hnt (t * x₀)
    rw [hcdef]
    rcases h with h | h
    · rw [h] at e1 e2
      simp only [e1, e2]
    · rw [h] at e1 e2
      have : t * (t * x) = x := by rw [← mul_assoc, ht2, one_mul]
      rw [this] at e2
      simp only [e1, e2]
      ring
  refine ⟨c, ?_, hall, card_filter_pair t ht2 F hF X hall⟩
  rw [hcdef]
  split_ifs <;> omega

omit [Fintype G] in
theorem even_card_of_mul_right (V : Finset G) (y : G) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hV : ∀ x ∈ V, x * y ∈ V) : Even V.card := by
  have hiff : ∀ x : G, x ∈ V ↔ x * y ∈ V := fun x =>
    ⟨hV x, fun h => by simpa [mul_assoc, hy2] using hV _ h⟩
  let σ : Equiv.Perm V := Equiv.subtypeEquiv (Equiv.mulRight y) hiff
  have hσx : ∀ x : V, ((σ x : V) : G) = x * y := fun x => rfl
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext x
    rw [pow_one, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    show (((σ (σ x) : V)) : G) = x
    rw [hσx, hσx, mul_assoc, hy2, mul_one]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) (σ := σ) hσ
  have hsupp : σ.supportᶜ = ∅ := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.notMem_empty,
      iff_false]
    intro h
    have h' : (x : G) * y = x := by rw [← hσx, h]
    exact hy1 (by simpa using h')
  rw [hsupp, Finset.card_empty, Fintype.card_coe] at hmod
  exact even_iff_two_dvd.2 ((Nat.modEq_zero_iff_dvd).1 hmod.symm)

end CFSG.EvenSporadicStandard.M22Std
