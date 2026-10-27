module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Levi
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Data
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)

section Hyp

variable (K : Type) [Field K] [Finite K]

@[expose] def LeviSelfDual : Prop :=
  ∀ (y : (Coord → K) ≃ₗ[K] (Coord → K)), OddOrderIsometry (quadPlus 4 K) 3 y →
    ∀ {h : K[X]}, h ∈ primaryFactors y.toLinearMap → h ≠ X - 1 → h = reciprocalPolynomial h →
      primaryMultiplicity y.toLinearMap h = 2 →
      ∃ A B : HypPair (quadPlus 4 K), A.Orth B ∧
        Submodule.span K {A.e, A.f, B.e, B.f} = orbitSpace y.toLinearMap h ∧
        specialBlock (quadPlus 4 K) y h = leviV (quadPlus 4 K) A.e B.e A.f B.f

@[expose] def LeviFixed : Prop :=
  ∀ (y : (Coord → K) ≃ₗ[K] (Coord → K)), OddOrderIsometry (quadPlus 4 K) 3 y → Nat.card K ≠ 2 →
    ∀ A B : HypPair (quadPlus 4 K), A.Orth B →
      Submodule.span K {A.e, A.f, B.e, B.f} = fixedSpace y →
        supportedFixedDerived (quadPlus 4 K) y =
          leviV (quadPlus 4 K) A.e B.e A.f B.f ⊔ leviV (quadPlus 4 K) A.e B.f A.f B.e

@[expose] def SixNotL2 : Prop :=
  ∀ {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W),
    (polarBilin R).Nondegenerate → finrank K W = 6 → ringChar K ≠ 3 → ∀ {r : ℕ}, 64 ≤ r →
      ¬ IsTypeL2 r ↥(orthDerived R)

end Hyp


end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
