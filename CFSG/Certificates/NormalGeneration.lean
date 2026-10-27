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

public noncomputable section

namespace CFSG.Certificates

variable {G : Type*} [Group G] [Finite G]

@[expose] def conjugateGenerated (x : G) {r : ℕ} (g : Fin r → G) : Subgroup G :=
  Subgroup.closure (Set.range fun i => (g i)⁻¹ * x * g i)

theorem full_order_conjugates_normally_generate (x : G) {r : ℕ} (g : Fin r → G)
    (hcard : Nat.card (conjugateGenerated x g) = Nat.card G) :
    conjugateGenerated x g = ⊤ ∧ Subgroup.normalClosure ({x} : Set G) = ⊤ := by
  have htop : conjugateGenerated x g = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  refine ⟨htop, top_le_iff.mp ?_⟩
  rw [← htop]
  change Subgroup.closure (Set.range fun i => (g i)⁻¹ * x * g i) ≤
    Subgroup.normalClosure ({x} : Set G)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change (g i)⁻¹ * x * g i ∈ Subgroup.normalClosure ({x} : Set G)
  have hx : x ∈ Subgroup.normalClosure ({x} : Set G) :=
    Subgroup.subset_normalClosure (by simp)
  simpa only [inv_inv] using
    (inferInstance : (Subgroup.normalClosure ({x} : Set G)).Normal).conj_mem x hx (g i)⁻¹

theorem exists_prime_order_mem_subgroup (N : Subgroup G) (hN : N ≠ ⊥) :
    ∃ (p : ℕ) (x : G), p.Prime ∧ p ∣ Nat.card G ∧ x ∈ N ∧ orderOf x = p := by
  have hcard : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card N ≠ 1)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdiv
  exact ⟨p, x, hp, hdiv.trans (Subgroup.card_subgroup_dvd_card N), x.property,
    by simpa only [Subgroup.orderOf_coe] using hx⟩

theorem prime_order_normal_test [Nontrivial G] (representatives : Set G)
    (hprime : ∀ r ∈ representatives, (orderOf r).Prime)
    (hcover : ∀ x : G, (orderOf x).Prime →
      ∃ r ∈ representatives, ∃ g : G,
        Subgroup.zpowers x = (Subgroup.zpowers r).map (MulAut.conj g).toMonoidHom)
    (hgenerate : ∀ r ∈ representatives, Subgroup.normalClosure ({r} : Set G) = ⊤) :
    IsSimpleGroup G := by
  constructor
  intro N hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    obtain ⟨p, x, hp, _, hx, horder⟩ := exists_prime_order_mem_subgroup N hN
    obtain ⟨r, hr, g, heq⟩ := hcover x (by rwa [horder])
    have hzp : Subgroup.zpowers x ≤ N := Subgroup.zpowers_le.mpr hx
    have hconj : g * r * g⁻¹ ∈ N := by
      apply hzp
      rw [heq]
      exact Subgroup.mem_map.mpr ⟨r, Subgroup.mem_zpowers r, rfl⟩
    have hrN : r ∈ N := by
      have h := hnormal.conj_mem (g * r * g⁻¹) hconj g⁻¹
      have he : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by group
      rwa [he] at h
    have hle : Subgroup.normalClosure ({r} : Set G) ≤ N :=
      Subgroup.normalClosure_le_normal (by simpa using hrN)
    rw [hgenerate r hr] at hle
    exact top_le_iff.mp hle

end CFSG.Certificates
