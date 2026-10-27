module

public import CFSG.ClassicalInvolution.Asc77.AscP1Transfer
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

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

variable {G : Type} [Group G] [Finite G]

theorem false_of_transfer [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x) (S : Sylow 2 G)
    {P : Subgroup G} (hPn : (S : Subgroup G) ≤ Subgroup.normalizer (P : Set G))
    (hab : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ P)
    {a : G} (haS : a ∈ (S : Subgroup G)) (haP : a ∉ P) (ha2 : a * a = 1)
    (hfus : ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → (g⁻¹ * a * g)⁻¹ * a ∈ P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥(S : Subgroup G) := P.subgroupOf (S : Subgroup G) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn s => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hPn s.2) n).mp hn
    simpa using this
  let _ : CommGroup (↥(S : Subgroup G) ⧸ N) :=
    { (inferInstance : Group (↥(S : Subgroup G) ⧸ N)) with
      mul_comm := by
        intro u v
        induction u using QuotientGroup.induction_on with
        | H x =>
          induction v using QuotientGroup.induction_on with
          | H y =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
              Subgroup.mem_subgroupOf]
            have h1 := hab _ (y⁻¹).2 _ (x⁻¹).2
            simpa [mul_assoc] using h1 }
  let ϕ : ↥(S : Subgroup G) →* ↥(S : Subgroup G) ⧸ N := QuotientGroup.mk' N
  have ha1 : a ≠ 1 := fun h => haP (h ▸ P.one_mem)
  have hϕa : ϕ ⟨a, haS⟩ ≠ 1 := by
    intro h
    apply haP
    have := (QuotientGroup.eq_one_iff (N := N) _).mp h
    rwa [hN, Subgroup.mem_subgroupOf] at this
  have ha2' : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact ha2) ha1, pow_one])
  have hodd : Odd (S : Subgroup G).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  have hϕ2 : ϕ ⟨a, haS⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haS⟩ : ↥(S : Subgroup G)) ^ 2 = 1 := Subtype.ext (by simp [_root_.sq, ha2])
    rw [this, map_one]
  have hV := Asc77.transfer_apply_ne_one ϕ a haS ha2' hϕa hodd fun g n hg => by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have e : a ^ (k + k) = 1 := by rw [← two_mul, pow_mul, _root_.sq, ha2, one_pow]
      have e2 : (⟨g⁻¹ * a ^ (k + k) * g, hg⟩ : ↥(S : Subgroup G)) = 1 :=
        Subtype.ext (by simp [e])
      rw [e2, map_one, ← two_mul, pow_mul, hϕ2, one_pow]
    · have e : a ^ (2 * k + 1) = a := by
        rw [pow_succ, pow_mul, _root_.sq, ha2, one_pow, one_mul]
      have hg' : g⁻¹ * a * g ∈ (S : Subgroup G) := by rwa [e] at hg
      have e2 : (⟨g⁻¹ * a ^ (2 * k + 1) * g, hg⟩ : ↥(S : Subgroup G)) = ⟨g⁻¹ * a * g, hg'⟩ :=
        Subtype.ext (by simp only [e])
      rw [e2, pow_succ, pow_mul, hϕ2, one_pow, one_mul]
      refine (QuotientGroup.eq (s := N)).mpr ?_
      rw [hN, Subgroup.mem_subgroupOf]
      simpa using hfus g hg'
  set V := MonoidHom.transfer ϕ with hVdef
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V.ker with h | h
  · obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have hinj : Function.Injective V := (MonoidHom.ker_eq_bot_iff V).mp h
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  · apply hV
    have : a ∈ V.ker := h ▸ Subgroup.mem_top a
    exact this

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
