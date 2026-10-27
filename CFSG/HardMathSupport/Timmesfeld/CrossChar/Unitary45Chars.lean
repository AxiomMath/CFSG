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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {G : Type*} [Group G] {K : Type*} [Field K]

theorem no_three_equal_chars [Finite G] (hG : Nat.card G = 27) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (c : Fin n → G →* Kˣ) (hc : ∀ k x, c k x ^ 3 = 1)
    (hfaith : ∀ x, (∀ k, c k x = 1) → x = 1) (hdet : ∀ x, ∏ k, c k x = 1)
    {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ¬ (c i = c j ∧ c i = c l) := by
  classical
  rintro ⟨hj, hl⟩
  have hn4 : 4 ≤ n := by omega
  have hn5 : n ≤ 5 := by omega
  have h3 : ({i, j, l} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hjl]
    simp [hij, hil]
  obtain ⟨m, hm⟩ : ∃ m, m ∉ ({i, j, l} : Finset (Fin n)) := by
    by_contra hcon
    push Not at hcon
    have : ({i, j, l} : Finset (Fin n)) = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at h3
    omega
  have hmi : m ≠ i := fun h => hm (by simp [h])
  have hmj : m ≠ j := fun h => hm (by simp [h])
  have hml : m ≠ l := fun h => hm (by simp [h])
  set S : Finset (Fin n) := insert m {i, j, l} with hS
  have h4 : S.card = 4 := by rw [hS, Finset.card_insert_of_notMem hm, h3]
  have hcomp : ∀ k k' : Fin n, k ∉ S → k' ∉ S → k = k' := by
    intro k k' hk hk'
    have hsub : (Finset.univ \ S).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
        Fintype.card_fin, h4]
      omega
    exact Finset.card_le_one.1 hsub k (by simpa using hk) k' (by simpa using hk')
  have hroot : ∀ x, c m x ∈ (rootsOfUnity 3 K) := fun x => (mem_rootsOfUnity _ _).2 (hc m x)
  have hrooti : ∀ x, c i x ∈ (rootsOfUnity 3 K) := fun x => (mem_rootsOfUnity _ _).2 (hc i x)
  let Φ : G → rootsOfUnity 3 K × rootsOfUnity 3 K := fun x => (⟨c i x, hrooti x⟩, ⟨c m x, hroot x⟩)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have e1 : c i x = c i y := congrArg (fun p => (p.1 : Kˣ)) hxy
    have e2 : c m x = c m y := congrArg (fun p => (p.2 : Kˣ)) hxy
    set z : G := x * y⁻¹ with hz
    have hcz : ∀ k, c k z = c k x * (c k y)⁻¹ := fun k => by rw [hz, map_mul, map_inv]
    have hzi : c i z = 1 := by rw [hcz, e1, mul_inv_cancel]
    have hzm : c m z = 1 := by rw [hcz, e2, mul_inv_cancel]
    have hzj : c j z = 1 := by rw [← congrFun (congrArg DFunLike.coe hj) z, hzi]
    have hzl : c l z = 1 := by rw [← congrFun (congrArg DFunLike.coe hl) z, hzi]
    have hzS : ∀ k ∈ S, c k z = 1 := by
      intro k hk
      rw [hS] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hzm
      · exact hzi
      · exact hzj
      · exact hzl
    have hall : ∀ k, c k z = 1 := by
      intro k
      by_cases hk : k ∈ S
      · exact hzS k hk
      · have : ∏ k', c k' z = c k z := by
          refine Finset.prod_eq_single_of_mem k (Finset.mem_univ k) fun k' _ hk' => hzS k' ?_
          by_contra hk''
          exact hk' (hcomp k' k hk'' hk)
        rw [← this]
        exact hdet z
    have hz1 : z = 1 := hfaith z hall
    exact mul_inv_eq_one.1 hz1
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, hG] at hcard
  have h9 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.CrossChar
