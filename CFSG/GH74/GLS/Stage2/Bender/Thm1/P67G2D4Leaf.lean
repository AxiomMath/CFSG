module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneToral
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def G2D4InnerPlaneGen : Prop := D4PlaneToral

@[expose] def D4OuterThree : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), orderOf φ = 3 →
      φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      (∀ F₀ : Subgroup ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ), F₀.Normal →
        (∀ x y : F₀, x * y = y * x) → F₀ = ⊥) ∧
      ∀ ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), Odd (orderOf ζ) →
        Nat.Coprime (orderOf ζ) 3 → ζ * φ = φ * ζ →
        (∀ c ∈ CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ, ζ c = c) → ζ = 1

end CFSG.GH74.GLS.Stage2.Bender.Thm1
