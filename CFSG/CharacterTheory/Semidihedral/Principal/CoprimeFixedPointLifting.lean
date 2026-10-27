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

public section

namespace CFSG.Semidihedral.Principal

universe u v

namespace CoprimeFixedPoint

variable {A : Type u} {G : Type v} [Group A] [Group G]

@[expose, instance_reducible] def subsetAction (α : A →* MulAut G) (S : Set G)
    (hS : ∀ a : A, ∀ x ∈ S, α a x ∈ S) : MulAction A S where
  smul a x := ⟨α a x, hS a x x.2⟩
  one_smul x := Subtype.ext (by
    change α 1 (x : G) = x
    rw [map_one]
    rfl)
  mul_smul a b x := Subtype.ext (by
    change α (a * b) (x : G) = α a (α b x)
    rw [map_mul]
    rfl)

theorem exists_fixed_of_invariant [Finite G] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A)
    (α : A →* MulAut G) (S : Set G) (hS : ∀ a : A, ∀ x ∈ S, α a x ∈ S)
    (hcard : ¬ p ∣ Nat.card S) : ∃ c ∈ S, ∀ a : A, α a c = c := by
  let := subsetAction α S hS
  obtain ⟨c, hc⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  refine ⟨c, c.2, fun a => ?_⟩
  have h1 : a • c = c := hc a
  exact congrArg Subtype.val h1

end CoprimeFixedPoint

open CoprimeFixedPoint

theorem coprime_invariant_coset_fixed {A : Type u} {G : Type v} [Group A] [Group G] [Finite A]
    [Finite G] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (α : A →* MulAut G) (H : Subgroup G)
    (hcop : ¬ p ∣ Nat.card H) (g : G) :
    ((∀ a : A, ∀ x : G, x * g⁻¹ ∈ H → α a x * g⁻¹ ∈ H) →
        ∃ c : G, c * g⁻¹ ∈ H ∧ ∀ a : A, α a c = c) ∧
      ((∀ a : A, ∀ x : G, g⁻¹ * x ∈ H → g⁻¹ * α a x ∈ H) →
        ∃ c : G, g⁻¹ * c ∈ H ∧ ∀ a : A, α a c = c) := by
  constructor
  · intro hinv
    have hcard : Nat.card {x : G | x * g⁻¹ ∈ H} = Nat.card H := Nat.card_congr
      { toFun := fun x => ⟨x.1 * g⁻¹, x.2⟩
        invFun := fun h => ⟨h.1 * g, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun h => Subtype.ext (by simp) }
    obtain ⟨c, hc, hfix⟩ := exists_fixed_of_invariant p hA α {x : G | x * g⁻¹ ∈ H}
      (fun a x hx => hinv a x hx) (hcard ▸ hcop)
    exact ⟨c, hc, hfix⟩
  · intro hinv
    have hcard : Nat.card {x : G | g⁻¹ * x ∈ H} = Nat.card H := Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * x.1, x.2⟩
        invFun := fun h => ⟨g * h.1, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun h => Subtype.ext (by simp) }
    obtain ⟨c, hc, hfix⟩ := exists_fixed_of_invariant p hA α {x : G | g⁻¹ * x ∈ H}
      (fun a x hx => hinv a x hx) (hcard ▸ hcop)
    exact ⟨c, hc, hfix⟩

namespace CoprimeFixedPoint

variable {A : Type u} {G : Type v} [Group A] [Group G]

theorem map_eq (α : A →* MulAut G) (N : Subgroup G) (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N)
    (a : A) : N.map ((α a : G ≃* G) : G →* G) = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact hN a n hn
  · intro n hn
    refine ⟨α a⁻¹ n, hN a⁻¹ n hn, ?_⟩
    change α a (α a⁻¹ n) = n
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] noncomputable def quotientAction (α : A →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) : A →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N (α a) (map_eq α N hN a)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change ((α 1 x : G) : G ⧸ N) = (x : G ⧸ N)
      rw [map_one]
      rfl
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change ((α (a * b) x : G) : G ⧸ N) = ((α a (α b x) : G) : G ⧸ N)
      rw [map_mul]
      rfl

theorem quotientAction_mk (α : A →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) (a : A) (x : G) :
    quotientAction α N hN a (x : G ⧸ N) = ((α a x : G) : G ⧸ N) := rfl

end CoprimeFixedPoint

theorem coprime_fixed_point_lifting {A : Type u} {G : Type v} [Group A] [Group G] [Finite A]
    [Finite G] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (α : A →* MulAut G) (N : Subgroup G)
    [N.Normal] (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) (hcop : ¬ p ∣ Nat.card N) :
    {q : G ⧸ N | ∀ a : A, quotientAction α N hN a q = q} =
      (QuotientGroup.mk' N) '' {c : G | ∀ a : A, α a c = c} := by
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hinv : ∀ a : A, ∀ x : G, g⁻¹ * x ∈ N → g⁻¹ * α a x ∈ N := by
      intro a x hx
      have hfix : ((α a g : G) : G ⧸ N) = (g : G ⧸ N) := hq a
      have h1 : g⁻¹ * α a g ∈ N := by
        have h2 := QuotientGroup.eq.mp hfix.symm
        exact h2
      have h3 : α a (g⁻¹ * x) ∈ N := hN a _ hx
      have h4 : g⁻¹ * α a x = (g⁻¹ * α a g) * α a (g⁻¹ * x) := by
        rw [map_mul, map_inv]
        group
      rw [h4]
      exact Subgroup.mul_mem _ h1 h3
    obtain ⟨c, hc, hfix⟩ := (coprime_invariant_coset_fixed p hA α N hcop g).2 hinv
    exact ⟨c, hfix, (QuotientGroup.eq.mpr hc).symm⟩
  · rintro ⟨c, hc, rfl⟩ a
    change ((α a c : G) : G ⧸ N) = (c : G ⧸ N)
    rw [hc a]

end CFSG.Semidihedral.Principal
