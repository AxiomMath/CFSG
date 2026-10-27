module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_index_two [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    (S : Sylow 2 G) {H : Subgroup G}
    (hHn : ∀ s ∈ (S : Subgroup G), ∀ q ∈ (S : Subgroup G) ⊓ H, s * q * s⁻¹ ∈ H)
    (hidx : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a ∉ H → b ∉ H → a⁻¹ * b ∈ H)
    {u : G} (huS : u ∈ (S : Subgroup G)) (huH : u ∉ H) (hu2 : u * u = 1) :
    ∃ g : G, g⁻¹ * u * g ∈ (S : Subgroup G) ⊓ H ∧
      ∀ c ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : ∀ s ∈ (S : Subgroup G), ∀ q ∈ (S : Subgroup G) ⊓ H,
      s * q * s⁻¹ ∈ (S : Subgroup G) ⊓ H := fun s hs q hq =>
    ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hq.1) ((S : Subgroup G).inv_mem hs),
      hHn s hs q hq⟩
  have hcyc : ∃ b ∈ (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∃ k : ℤ,
      (b ^ k)⁻¹ * s ∈ (S : Subgroup G) ⊓ H := by
    refine ⟨u, huS, fun s hs => ?_⟩
    by_cases hsH : s ∈ H
    · exact ⟨0, by rw [zpow_zero, inv_one, one_mul]; exact ⟨hs, hsH⟩⟩
    · refine ⟨1, ?_⟩
      rw [zpow_one]
      exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem huS) hs, hidx u huS s hs huH hsH⟩
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ (S : Subgroup G) →
      g⁻¹ * u ^ (2 * k) * g ∈ (S : Subgroup G) ⊓ H := by
    intro g k _
    have e : u ^ (2 * k) = 1 := by rw [pow_mul, sq, hu2, one_pow]
    rw [e, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := (S : Subgroup G))
      (Q := (S : Subgroup G) ⊓ H) S.isPGroup' S.not_dvd_index hQn hcyc huS (fun h => huH h.2) hb
      (fun g hg _ => by
        by_cases h : g⁻¹ * u * g ∈ H
        · exact Or.inl ⟨hg, h⟩
        · exact Or.inr ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem huS) hg,
            hidx u huS _ hg huH h⟩) with
    ⟨N, hN, hNcyc, -, huN⟩ | ⟨g, hgQ, -, hgC⟩
  · exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := G ⧸ N)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (x : G ⧸ N))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (y : G ⧸ N))
      have hc : ((x * y : G) : G ⧸ N) = ((y * x : G) : G ⧸ N) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hi, ← hj, zpow_mul_comm]
      rw [QuotientGroup.eq, h, Subgroup.mem_bot] at hc
      calc x * y = x * y * ((x * y)⁻¹ * (y * x)) := by rw [hc, mul_one]
        _ = y * x := by group
    · exact huN (h ▸ Subgroup.mem_top u)
  · exact ⟨g, hgQ, hgC⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
