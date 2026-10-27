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

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

theorem top_of_sup_central {G : Type} [Group G] (R Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hsup : R ⊔ Z = ⊤) (hperf : commutator G = ⊤) : R = ⊤ := by
  have hmem : ∀ g : G, g ∈ R ⊔ Z := fun g => by rw [hsup]; exact Subgroup.mem_top g
  have hZn : Z.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hZ hn) g
    rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hdec : ∀ g : G, ∃ u ∈ R, ∃ z ∈ Z, u * z = g := fun g => Subgroup.mem_sup_of_normal_right.1 (hmem g)
  have hnorm : R.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := hdec g
    have hz' := Subgroup.mem_center_iff.1 (hZ hz)
    have : u * z * n * (u * z)⁻¹ = u * n * u⁻¹ := by
      calc u * z * n * (u * z)⁻¹ = u * (z * n) * z⁻¹ * u⁻¹ := by group
        _ = u * (n * z) * z⁻¹ * u⁻¹ := by rw [← hz' n]
        _ = u * n * u⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hu hn) (inv_mem hu)
  have hle : commutator G ≤ R := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨u, hu, z, hz, rfl⟩ := hdec a
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec b
    rw [← QuotientGroup.eq_one_iff]
    have hmu : (QuotientGroup.mk u : G ⧸ R) = 1 := (QuotientGroup.eq_one_iff u).2 hu
    have hmv : (QuotientGroup.mk v : G ⧸ R) = 1 := (QuotientGroup.eq_one_iff v).2 hv
    have hzw : z * w = w * z := (Subgroup.mem_center_iff.1 (hZ hz) w).symm
    have hc : (QuotientGroup.mk z : G ⧸ R) * QuotientGroup.mk w =
        QuotientGroup.mk w * QuotientGroup.mk z := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hzw]
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmu, hmv,
      one_mul, inv_one]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hc
  rw [eq_top_iff, ← hperf]; exact hle

theorem exists_lift_aut {G L : Type} [Group G] [Finite G] [Group L] (π : G →* L)
    (hsurj : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center G)
    (hperf : commutator G = ⊤)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* G), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G →* E, ∀ g, p (s g) = g)
    (φ : MulAut L) : ∃ ψ : MulAut G, ∀ x, π (ψ x) = φ (π x) := by
  classical
  let P : Subgroup (G × G) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.snd G G)) ((φ : L →* L).comp (π.comp (MonoidHom.fst G G)))
  let p : P →* G := (MonoidHom.fst G G).comp P.subtype
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨x', hx'⟩ := hsurj (φ (π x))
    exact ⟨⟨(x, x'), hx'⟩, rfl⟩
  have hpker : p.ker ≤ Subgroup.center P := by
    rintro ⟨⟨x, x'⟩, hx⟩ hk
    have hx1 : x = 1 := hk
    subst hx1
    have h1 : π x' = φ (π 1) := hx
    have hx'k : x' ∈ π.ker := by
      rw [MonoidHom.mem_ker, h1, map_one, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨y, y'⟩, -⟩
    apply Subtype.ext
    change (y * 1, y' * x') = (1 * y, x' * y')
    rw [mul_one, one_mul, Subgroup.mem_center_iff.1 (hcen hx'k) y']
  obtain ⟨s, hs⟩ := hsec P p hp hpker
  let ψ₀ : G →* G := (MonoidHom.snd G G).comp (P.subtype.comp s)
  have hψ₀ : ∀ x, π (ψ₀ x) = φ (π x) := by
    intro x
    have h1 : π (s x : G × G).2 = φ (π (s x : G × G).1) := (s x).2
    have h2 : (s x : G × G).1 = x := hs x
    change π (s x : G × G).2 = _
    rw [h1, h2]
  have hmapped : ψ₀.range ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx⟩ := hsurj (φ.symm (π g))
    have : π (ψ₀ x) = π g := by rw [hψ₀, hx]; simp
    have hmem : ψ₀ x * ((ψ₀ x)⁻¹ * g) = g := by group
    have hg1 : g ∈ ψ₀.range ⊔ π.ker := by
      rw [← hmem]
      refine mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right ?_)
      rw [MonoidHom.mem_ker, map_mul, map_inv, this, inv_mul_cancel]
    exact hg1
  have hRtop : ψ₀.range = ⊤ :=
    top_of_sup_central ψ₀.range π.ker hcen hmapped hperf
  have hsurj0 : Function.Surjective ψ₀ := MonoidHom.range_eq_top.1 hRtop
  have hinj0 : Function.Injective ψ₀ := Finite.injective_iff_surjective.2 hsurj0
  exact ⟨MulEquiv.ofBijective ψ₀ ⟨hinj0, hsurj0⟩, hψ₀⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
