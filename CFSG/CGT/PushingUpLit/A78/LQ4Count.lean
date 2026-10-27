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

public section

namespace CFSG.CGT.PushingUpLit.A78

open scoped commutatorElement

theorem card_map_mul_card_ker_inf {J : Type*} [Group J] {K : Type*} [Group K] (ε : J →* K)
    (H : Subgroup J) : Nat.card (H.map ε) * Nat.card ↥(ε.ker ⊓ H) = Nat.card H := by
  rw [← Subgroup.relIndex_ker]
  exact Subgroup.relIndex_mul_card ε.ker H

theorem card_mul_le_of_elementarySection {S : Type*} [Group S] [Finite S] (J : Subgroup S)
    [J.Normal] {K : Type*} [Group K] (ε : J →* K) (hK : ∀ k : K, k ^ 2 = 1) (X Y : Subgroup S)
    (hYX : Y ≤ X) (hsq : ∀ x ∈ X, x ^ 2 ∈ Y) (hcomm : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ Y)
    (xs : List S) (hxs : ∀ x ∈ xs, x ∈ X) :
    Nat.card X * Nat.card (Subgroup.map ε (Subgroup.closure
        {j : J | ∃ n ∈ (X ⊓ J).subgroupOf J, ∃ x ∈ xs, (j : S) = ⁅(n : S), x⁆})) *
      Nat.card (Subgroup.closure {j : J | ∃ n ∈ (X ⊓ J).subgroupOf J, j = n ^ 2}) ≤
    Nat.card Y * J.relIndex X * Nat.card (Subgroup.map ε ((X ⊓ J).subgroupOf J)) *
      Nat.card ε.ker := by
  set N : Subgroup J := (X ⊓ J).subgroupOf J with hN
  set Cset : Set J := {j : J | ∃ n ∈ N, ∃ x ∈ xs, (j : S) = ⁅(n : S), x⁆} with hCset
  set Qset : Set J := {j : J | ∃ n ∈ N, j = n ^ 2} with hQset
  set Cj : Subgroup J := Subgroup.closure Cset with hCj
  set Q : Subgroup J := Subgroup.closure Qset with hQ
  set M : Subgroup J := Subgroup.closure (Cset ∪ Qset) with hM
  have hCM : Cj ≤ M := Subgroup.closure_mono Set.subset_union_left
  have hQM : Q ≤ M := Subgroup.closure_mono Set.subset_union_right
  have hnX : ∀ n ∈ N, (n : S) ∈ X := fun n hn => (Subgroup.mem_subgroupOf.1 hn).1
  have hMN : M ≤ N := by
    refine (Subgroup.closure_le _).2 (Set.union_subset ?_ ?_)
    · rintro j ⟨n, hn, x, hx, hj⟩
      refine Subgroup.mem_subgroupOf.2 ⟨?_, j.2⟩
      rw [hj]
      exact hYX (hcomm _ (hnX n hn) x (hxs x hx))
    · rintro j ⟨n, hn, rfl⟩
      exact N.pow_mem hn 2
  have hMY : M.map J.subtype ≤ Y := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 (Set.union_subset ?_ ?_)
    · rintro j ⟨n, hn, x, hx, hj⟩
      change (j : S) ∈ Y
      rw [hj]
      exact hcomm _ (hnX n hn) x (hxs x hx)
    · rintro j ⟨n, hn, rfl⟩
      change ((n ^ 2 : J) : S) ∈ Y
      rw [Subgroup.coe_pow]
      exact hsq _ (hnX n hn)
  have hQker : Q ≤ ε.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro j ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, hK]
  have hA := card_map_mul_card_ker_inf ε N
  have hMc := card_map_mul_card_ker_inf ε M
  have hfin : Finite ↥(M.map ε) :=
    Finite.of_surjective (fun m : M => (⟨ε m, ⟨m, m.2, rfl⟩⟩ : M.map ε))
      (by rintro ⟨y, m, hm, rfl⟩; exact ⟨⟨m, hm⟩, rfl⟩)
  have h1 : Nat.card (Cj.map ε) ≤ Nat.card (M.map ε) :=
    Subgroup.card_le_of_le (Subgroup.map_mono hCM)
  have h2 : Nat.card Q ≤ Nat.card ↥(ε.ker ⊓ M) := Subgroup.card_le_of_le (le_inf hQker hQM)
  have h3 : Nat.card ↥(ε.ker ⊓ N) ≤ Nat.card ε.ker := Subgroup.card_le_of_le inf_le_left
  have h4 : Nat.card M ≤ Nat.card Y := by
    have e : Nat.card (M.map J.subtype) = Nat.card M :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective J)
    rw [← e]
    exact Subgroup.card_le_of_le hMY
  have h5 : Nat.card X = J.relIndex X * Nat.card N := by
    have := Subgroup.relIndex_mul_card J X
    rw [inf_comm] at this
    rw [← this]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  calc Nat.card X * Nat.card (Cj.map ε) * Nat.card Q
      = J.relIndex X * (Nat.card (N.map ε) * Nat.card ↥(ε.ker ⊓ N)) * Nat.card (Cj.map ε) *
        Nat.card Q := by rw [h5, ← hA]
    _ ≤ J.relIndex X * (Nat.card (N.map ε) * Nat.card ε.ker) * Nat.card (M.map ε) *
        Nat.card ↥(ε.ker ⊓ M) := by gcongr
    _ = J.relIndex X * Nat.card (N.map ε) * Nat.card ε.ker * Nat.card M := by
        rw [← hMc]; ring
    _ ≤ J.relIndex X * Nat.card (N.map ε) * Nat.card ε.ker * Nat.card Y := by gcongr
    _ = Nat.card Y * J.relIndex X * Nat.card (N.map ε) * Nat.card ε.ker := by ring

end CFSG.CGT.PushingUpLit.A78
