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

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

theorem exists_mem_central_mod {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {A B : Subgroup P} [A.Normal] [B.Normal] (hAB : A < B) :
    ∃ x ∈ B, x ∉ A ∧ ∀ g : P, g * x * g⁻¹ * x⁻¹ ∈ A := by
  classical
  have hnil : Group.IsNilpotent (P ⧸ A) := (hP.to_quotient A).isNilpotent
  set Bq : Subgroup (P ⧸ A) := B.map (QuotientGroup.mk' A) with hBq
  have : Bq.Normal := Subgroup.Normal.map inferInstance (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
  obtain ⟨b, hbB, hbA⟩ := IsConcreteLE.exists_of_lt hAB
  have hne : Bq ≠ ⊥ := by
    intro h
    apply hbA
    have : (QuotientGroup.mk' A b) ∈ Bq := Subgroup.mem_map_of_mem _ hbB
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff b).mp this
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨q, hq⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcen
  obtain ⟨x, hxB, hxq⟩ := Subgroup.mem_map.mp q.2.1
  refine ⟨x, hxB, ?_, ?_⟩
  · intro hxA
    apply hq
    apply Subtype.ext
    simp only [Subgroup.coe_one]
    rw [← hxq]
    exact (QuotientGroup.eq_one_iff x).mpr hxA
  · intro g
    have hcz : (q.1 : P ⧸ A) ∈ Subgroup.center (P ⧸ A) := q.2.2
    have h1 := Subgroup.mem_center_iff.mp hcz (QuotientGroup.mk' A g)
    rw [← QuotientGroup.eq_one_iff]
    have : QuotientGroup.mk' A (g * x * g⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hxq]
      calc QuotientGroup.mk' A g * (q.1 : P ⧸ A) * (QuotientGroup.mk' A g)⁻¹ * (q.1 : P ⧸ A)⁻¹
          = (QuotientGroup.mk' A g * (q.1 : P ⧸ A)) * (QuotientGroup.mk' A g)⁻¹ *
            (q.1 : P ⧸ A)⁻¹ := by rfl
        _ = 1 := by rw [h1]; group
    exact this

theorem mul_pow_three_of_comm {G : Type*} [Group G] {x y c : G} (h : y * x = x * y * c)
    (hcx : c * x = x * c) (hcy : c * y = y * c) : (x * y) ^ 3 = x ^ 3 * y ^ 3 * c ^ 3 := by
  have h2 : y * y * x = x * (y * y) * (c * c) := by
    calc y * y * x = y * (y * x) := by rw [mul_assoc]
      _ = y * (x * y * c) := by rw [h]
      _ = (y * x) * y * c := by simp only [mul_assoc]
      _ = (x * y * c) * y * c := by rw [h]
      _ = x * y * (c * y) * c := by simp only [mul_assoc]
      _ = x * y * (y * c) * c := by rw [hcy]
      _ = x * (y * y) * (c * c) := by simp only [mul_assoc]
  calc (x * y) ^ 3 = x * y * (x * y) * (x * y) := by simp only [pow_succ, pow_zero, one_mul]
    _ = x * (y * x) * y * (x * y) := by simp only [mul_assoc]
    _ = x * (x * y * c) * y * (x * y) := by rw [h]
    _ = x * x * y * (c * y) * (x * y) := by simp only [mul_assoc]
    _ = x * x * y * (y * c) * (x * y) := by rw [hcy]
    _ = x * x * (y * y) * (c * x) * y := by simp only [mul_assoc]
    _ = x * x * (y * y) * (x * c) * y := by rw [hcx]
    _ = x * x * (y * y * x) * c * y := by simp only [mul_assoc]
    _ = x * x * (x * (y * y) * (c * c)) * c * y := by rw [h2]
    _ = x * x * x * (y * y) * (c * c * c) * y := by simp only [mul_assoc]
    _ = x ^ 3 * y ^ 3 * c ^ 3 := by
        have hc3 : c ^ 3 * y = y * c ^ 3 := ((Commute.pow_left (show Commute c y from hcy)) 3).eq
        have e : x * x * x * (y * y) * (c * c * c) * y = x ^ 3 * y ^ 2 * (c ^ 3 * y) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [e, hc3]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]


theorem exists_mem_central_mod_of_normalizes {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {M A B : Subgroup G} [Finite M] (hM : IsPGroup p M) (hBM : B ≤ M)
    (hA : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B)
    (hAB : A < B) :
    ∃ x ∈ B, x ∉ A ∧ ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ A := by
  have hnA : (A.subgroupOf M).Normal := ⟨fun a ha g => by
    have := hA g.1 g.2 a.1 ha
    exact this⟩
  have hnB : (B.subgroupOf M).Normal := ⟨fun a ha g => by
    have := hB g.1 g.2 a.1 ha
    exact this⟩
  obtain ⟨b, hbB, hbA⟩ := IsConcreteLE.exists_of_lt hAB
  have hlt : A.subgroupOf M < B.subgroupOf M := by
    refine lt_of_le_of_ne (fun a ha => ?_) (fun h => ?_)
    · exact (Subgroup.mem_subgroupOf.mpr (hAB.le (Subgroup.mem_subgroupOf.mp ha)))
    · apply hbA
      have : (⟨b, hBM hbB⟩ : M) ∈ B.subgroupOf M := hbB
      rw [← h] at this
      exact this
  obtain ⟨x, hxB, hxA, hxc⟩ := exists_mem_central_mod hM hlt
  refine ⟨x.1, hxB, hxA, fun m hm => ?_⟩
  have := hxc ⟨m, hm⟩
  exact this

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
