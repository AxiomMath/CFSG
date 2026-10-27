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
public import Mathlib.RingTheory.LittleWedderburn
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

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Sel

open Function

theorem endo_comm_of_simple {A : Type} [CommGroup A] [Finite A] [Nontrivial A] {Γ : Type}
    [Group Γ] (ρ : Γ →* MulAut A)
    (hsimple : ∀ B : Subgroup A, (∀ g : Γ, ∀ b ∈ B, ρ g b ∈ B) → B = ⊥ ∨ B = ⊤)
    (φ ψ : A →* A) (hφ : ∀ g a, φ (ρ g a) = ρ g (φ a)) (hψ : ∀ g a, ψ (ρ g a) = ρ g (ψ a)) :
    ∀ a, φ (ψ a) = ψ (φ a) := by
  classical
  let ρa : Γ → AddMonoid.End (Additive A) := fun g => MonoidHom.toAdditive ((ρ g).toMonoidHom)
  let S : Set (AddMonoid.End (Additive A)) := Set.range ρa
  let E : Subring (AddMonoid.End (Additive A)) := Subring.centralizer S
  have hcomm : ∀ f : AddMonoid.End (Additive A), f ∈ E → ∀ g a,
      (MonoidHom.toAdditive.symm f) (ρ g a) = ρ g ((MonoidHom.toAdditive.symm f) a) := by
    intro f hf g a
    have h1 := (Subring.mem_centralizer_iff.mp hf) (ρa g) ⟨g, rfl⟩
    have h2 := DFunLike.congr_fun h1 (Additive.ofMul a)
    exact h2.symm
  have hinj : ∀ f : AddMonoid.End (Additive A), f ∈ E → f ≠ 0 → Injective f := by
    intro f hf hne
    let fm : A →* A := MonoidHom.toAdditive.symm f
    have hB : ∀ g : Γ, ∀ b ∈ fm.ker, ρ g b ∈ fm.ker := by
      intro g b hb
      rw [MonoidHom.mem_ker] at hb ⊢
      rw [hcomm f hf g b, hb, map_one]
    rcases hsimple fm.ker hB with h0 | h0
    · intro x y hxy
      have : Injective fm := (MonoidHom.ker_eq_bot_iff fm).mp h0
      exact Additive.toMul.injective (this (congrArg Additive.toMul hxy))
    · exfalso
      apply hne
      ext x
      have : fm (Additive.toMul x) = 1 := by
        have : Additive.toMul x ∈ fm.ker := by rw [h0]; trivial
        exact this
      exact congrArg Additive.ofMul this
  have : Nontrivial E := by
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    refine ⟨⟨0, 1, fun h => ha ?_⟩⟩
    have := DFunLike.congr_fun (congrArg Subtype.val h) (Additive.ofMul a)
    exact Additive.ofMul.injective this.symm
  have : NoZeroDivisors E := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases hb : b = 0
    · exact Or.inr hb
    · left
      have hb' : (b : AddMonoid.End (Additive A)) ≠ 0 := fun h => hb (Subtype.ext h)
      have hbs : Surjective (b : AddMonoid.End (Additive A)) :=
        Finite.injective_iff_surjective.mp (hinj b b.2 hb')
      apply Subtype.ext
      ext x
      obtain ⟨y, rfl⟩ := hbs x
      have := DFunLike.congr_fun (congrArg Subtype.val hab) y
      exact this
  have : Finite (AddMonoid.End (Additive A)) :=
    Finite.of_injective (fun f : AddMonoid.End (Additive A) => (f : Additive A → Additive A))
      DFunLike.coe_injective
  have : Finite E := inferInstance
  have : IsDomain E := NoZeroDivisors.to_isDomain E
  have hfield := Finite.isDomain_to_isField E
  intro a
  have hφE : (MonoidHom.toAdditive φ : AddMonoid.End (Additive A)) ∈ E :=
    Subring.mem_centralizer_iff (R := AddMonoid.End (Additive A)) |>.mpr (by
      rintro _ ⟨g, rfl⟩
      ext x
      exact (hφ g (Additive.toMul x)).symm)
  have hψE : (MonoidHom.toAdditive ψ : AddMonoid.End (Additive A)) ∈ E :=
    Subring.mem_centralizer_iff (R := AddMonoid.End (Additive A)) |>.mpr (by
      rintro _ ⟨g, rfl⟩
      ext x
      exact (hψ g (Additive.toMul x)).symm)
  have h := hfield.mul_comm ⟨_, hφE⟩ ⟨_, hψE⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun (congrArg Subtype.val h) (Additive.ofMul a))

end CFSG.CGT.PushingUpLit.CGT6.Diag.Sel
