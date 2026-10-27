module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagGlue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis (repA)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def HeisClassA {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) :
    Prop :=
  ∃ (b : Fin Tag.E6.rank → ZMod 3) (t : WeylGroup Tag.E6),
    (∀ β, β ∈ rootCharKernel a ↔ β ∈ kernelRoots (triChar b)) ∧
    (∀ v, triPairing b (t • v) = triPairing repA v) ∧
    t⁻¹ * w * t ∈ charStabilizer (triChar repA) ∧
    triPairing repA (e6Shift (t⁻¹ * w * t)) ≠ 0

@[expose] def E6HeisFrameFixedEltA : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → ∀ F : E6HeisenbergFrame K E,
        HeisClassA F.a F.w →
        ∃ v : ModGL Tag.E6 (AlgebraicClosure K),
          v ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧ v ≠ 1 ∧ v ^ ringChar K = 1 ∧
          Units.map (entrywiseHom F.Fr) v = v ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₁ : ModGL Tag.E6 K)) ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₂ : ModGL Tag.E6 K))

@[expose] def TwE6HeisFrameFixedEltA : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ∀ F : TwE6HeisenbergFrame K σ (ℓ ^ f) E, HeisClassA F.a F.w →
        ∃ v : ModGL TwistTag.E6.tag (AlgebraicClosure K),
          v ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧ v ≠ 1 ∧ v ^ ℓ = 1 ∧
          twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr v = v ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (F.g₁ : ModGL TwistTag.E6.tag K)) ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (F.g₂ : ModGL TwistTag.E6.tag K))

end CFSG.LieType.SeitzGeneration.ExcWideThree
