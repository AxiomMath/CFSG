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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open MulAction

theorem ncard_four_le {G : Type*} (a b c d : G) : ({a, b, c, d} : Set G).ncard ≤ 4 := by
  classical
  have : ({a, b, c, d} : Set G) = ↑({a, b, c, d} : Finset G) := by simp
  rw [this, Set.ncard_coe_finset]
  exact Finset.card_le_four

theorem ncard_two_le {G : Type*} (a b : G) : ({a, b} : Set G).ncard ≤ 2 := by
  classical
  have : ({a, b} : Set G) = ↑({a, b} : Finset G) := by simp
  rw [this, Set.ncard_coe_finset]
  exact Finset.card_le_two

theorem card_le_of_stabilizer {G α : Type*} [Group G] [MulAction G α] [Finite G] (a : α)
    {T : Set α} (hT : ∀ g : G, g • a ∈ T) (hTfin : T.Finite) {m n : ℕ} (hm : T.ncard ≤ m)
    (hn : Nat.card (stabilizer G a) ≤ n) : Nat.card G ≤ m * n := by
  have h1 := Subgroup.card_mul_index (stabilizer G a)
  rw [index_stabilizer] at h1
  have h2 : (orbit G a).ncard ≤ T.ncard :=
    Set.ncard_le_ncard (by rintro _ ⟨g, rfl⟩; exact hT g) hTfin
  rw [← h1]
  calc Nat.card (stabilizer G a) * (orbit G a).ncard ≤ n * m :=
        Nat.mul_le_mul hn (h2.trans hm)
    _ = m * n := Nat.mul_comm _ _

theorem card_le_eight {G : Type*} [Group G] [Finite G] (z : G) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hcomm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = z)
    (hnc : ∀ g : G, g ≠ 1 → g ≠ z → g * g = z) : Nat.card G ≤ 8 := by
  by_cases hall : ∀ g : G, g = 1 ∨ g = z
  · have : (Set.univ : Set G) ⊆ {1, z} := fun g _ => by
      rcases hall g with h | h <;> simp [h]
    have h2 : (Set.univ : Set G).ncard ≤ ({1, z} : Set G).ncard :=
      Set.ncard_le_ncard this (Set.toFinite _)
    have h3 : ({1, z} : Set G).ncard ≤ 2 := ncard_two_le 1 z
    rw [Set.ncard_univ] at h2
    omega
  · push Not at hall
    obtain ⟨g, hg1, hgz⟩ := hall
    have hgg := hnc g hg1 hgz
    have hginv : g * (g * z) = 1 := by
      rw [← mul_assoc, hgg, hzz]
    have hstab : Nat.card (stabilizer (ConjAct G) g) ≤ 4 := by
      have hinj : Function.Injective
          (fun x : stabilizer (ConjAct G) g => ConjAct.ofConjAct (x : ConjAct G)) :=
        fun x y h => Subtype.ext (ConjAct.ofConjAct.injective h)
      have hmem : ∀ x : stabilizer (ConjAct G) g,
          ConjAct.ofConjAct (x : ConjAct G) ∈ ({1, z, g, g * z} : Set G) := by
        intro x
        have hx := x.2
        rw [mem_stabilizer_iff, ConjAct.smul_def] at hx
        set h := ConjAct.ofConjAct (x : ConjAct G) with hh
        have hc : g * h = h * g := by
          have : h * g * h⁻¹ = g := hx
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this.symm
        by_contra hne
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
        obtain ⟨hn1, hnz, hng, hngz⟩ := hne
        by_cases hgh : g * h = 1 ∨ g * h = z
        · rcases hgh with e | e
          · apply hngz
            calc h = g⁻¹ := eq_inv_of_mul_eq_one_right e
              _ = g * z := (eq_inv_of_mul_eq_one_right hginv).symm
          · apply hng
            have : h = g⁻¹ * z := by rw [← e]; group
            rw [this, (eq_inv_of_mul_eq_one_right hginv).symm]
            calc g * z * z = g * (z * z) := by rw [mul_assoc]
              _ = g := by rw [hzz, mul_one]
        · push Not at hgh
          have h1 := hnc (g * h) hgh.1 hgh.2
          have h2 := hnc h hn1 hnz
          have : g * h * (g * h) = g * g * (h * h) := by
            calc g * h * (g * h) = g * (h * g) * h := by simp only [mul_assoc]
              _ = g * (g * h) * h := by rw [hc]
              _ = g * g * (h * h) := by simp only [mul_assoc]
          rw [h1, hgg, h2] at this
          exact hz1 (this.trans hzz)
      have hsub : (Set.range fun x : stabilizer (ConjAct G) g =>
          ConjAct.ofConjAct (x : ConjAct G)) ⊆ ({1, z, g, g * z} : Set G) := by
        rintro _ ⟨x, rfl⟩; exact hmem x
      have hc4 : ({1, z, g, g * z} : Set G).ncard ≤ 4 := by
        exact ncard_four_le _ _ _ _
      calc Nat.card (stabilizer (ConjAct G) g) = (Set.range fun x : stabilizer (ConjAct G) g =>
            ConjAct.ofConjAct (x : ConjAct G)).ncard := by
            rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
        _ ≤ ({1, z, g, g * z} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 4 := hc4
    have hT : ∀ x : ConjAct G, x • g ∈ ({g, z * g} : Set G) := by
      intro x
      rw [ConjAct.smul_def]
      set h := ConjAct.ofConjAct x
      rcases hcomm h g with e | e
      · left
        calc h * g * h⁻¹ = (h * g * h⁻¹ * g⁻¹) * g := by group
          _ = g := by rw [e, one_mul]
      · right
        calc h * g * h⁻¹ = (h * g * h⁻¹ * g⁻¹) * g := by group
          _ = z * g := by rw [e]
    have hT2 : ({g, z * g} : Set G).ncard ≤ 2 := ncard_two_le _ _
    have hcc : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
    have : Finite (ConjAct G) := Finite.of_equiv G ConjAct.toConjAct.toEquiv
    rw [← hcc]
    calc Nat.card (ConjAct G) ≤ 2 * 4 :=
          card_le_of_stabilizer (G := ConjAct G) g hT (Set.toFinite _) hT2 hstab
      _ = 8 := by norm_num

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
