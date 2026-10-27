module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ReeF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.Classical2
  CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.LieType.Universal.Spin

set_option linter.unusedSectionVars false

@[expose] def PSUTwoThreeBalance : Prop :=
  LocalTwoCrossFamAt 3 .twistedA fun idx =>
    ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA m q ∧ q.card = 2

@[expose] def SpTwoThreeBalance : Prop :=
  LocalTwoCrossFamAt 3 .B fun idx =>
    ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ 3 ≤ r ∧ q.card = 2

@[expose] def OrthTwoThreeInnerBalance : Prop :=
  (∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid), q.card = 2 →
      InnerPlaneBalance 3 (CatT ⟨.D r q, hv⟩)) ∧
    ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
      q.card = 2 → InnerPlaneBalance 3 (CatT ⟨.twistedD r q, hv⟩)

@[expose] def D4TrialityPlaneThreeBalance : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      (∃ t ∈ D, t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K)) →
      D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K) ≤
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) →
      ∀ H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (matrixProjectiveDerived
          (coordinateQuadPlus 4 K)))) → localDeltaIn 3 H D = ⊥

section E6Heisenberg


@[expose] def E6DiagIsotropic (K : Type) [Field K] (K₁ : IntermediateField K (AlgebraicClosure K))
    [Finite K₁] (D : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  ∀ x y : ↥(e6Data_valid.minGroup K₁),
    (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
      ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
        (baseChangeGL (algebraMap K K₁)) →
    (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
      ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
        (baseChangeGL (algebraMap K K₁)) →
    x * y = y * x

@[expose] def E6HeisenbergDiagThreeBalance : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → Nat.card K ≠ 2 → Nat.card K ≠ 4 →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), D ≤ e6Inndiag K → IsElemAbelian 3 D →
        Nat.card D = 3 ^ 2 → ¬ E6DiagIsotropic K K₁ D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
          localDeltaIn 3 H D = ⊥

@[expose] def TwistedE6DiagIsotropic (K : Type) [Field K] (σ : K ≃+* K)
    (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (D : Subgroup (MulAut (twistedE6RootGroup K σ))) : Prop :=
  ∀ x y : ↥(e6Data_valid.minGroup K₁),
    (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
      ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (algebraMap K K₁)) →
    (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
      ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (algebraMap K K₁)) →
    x * y = y * x

@[expose] def TwistedE6HeisenbergDiagThreeBalance : Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)),
        D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
        ¬ TwistedE6DiagIsotropic K σ K₁ D →
        ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
          localDeltaIn 3 H D = ⊥

@[expose] def TwistedE6TwoDiagMeetsInn : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)),
      D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → Nat.card D = 3 ^ 2 →
      ∃ d ∈ D, d ∈ innerAut (twistedE6RootGroup K σ) ∧ d ≠ 1

end E6Heisenberg

@[expose] def TriD4InnerThreeBalance : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex .trialityD4 q).Valid), q.p ≠ 3 →
    InnerPlaneBalance 3 (CatT ⟨excIndex .trialityD4 q, hv⟩)

section TriD4Outer


abbrev TriD4OuterThreeBalance : Prop := TrialityThreeRest

end TriD4Outer

section ReeF4Rows


abbrev ReeF4InnerThreeBalance : Prop := ReeF4InnerPlaneBalanceLow 3

abbrev ReeF4InnerFiveBalance : Prop := ReeF4InnerPlaneBalanceLow 5

end ReeF4Rows

@[expose] def InnerPlaneBalanceFive (k : LieFamily) (R : ℕ → Prop) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid), q.p ≠ 5 → R q.card →
    InnerPlaneBalance 5 (CatT ⟨excIndex k q, hv⟩)

@[expose] def E7InnerFiveOne : Prop := InnerPlaneBalanceFive .E7 fun n => 5 ∣ n - 1

@[expose] def E7InnerFiveTwo : Prop := InnerPlaneBalanceFive .E7 fun n => 5 ∣ n + 1

@[expose] def E6InnerFiveOne : Prop := InnerPlaneBalanceFive .E6 fun n => 5 ∣ n - 1

@[expose] def TwistedE6InnerFiveTwo : Prop := InnerPlaneBalanceFive .twistedE6 fun n => 5 ∣ n + 1

@[expose] def F4InnerFiveFour : Prop := InnerPlaneBalanceFive .F4 fun n => 5 ∣ n ^ 2 + 1

@[expose] def E6InnerFiveFour : Prop := InnerPlaneBalanceFive .E6 fun n => 5 ∣ n ^ 2 + 1

@[expose] def TwistedE6InnerFiveFour : Prop :=
  InnerPlaneBalanceFive .twistedE6 fun n => 5 ∣ n ^ 2 + 1

@[expose] def E7InnerFiveFour : Prop := InnerPlaneBalanceFive .E7 fun n => 5 ∣ n ^ 2 + 1

@[expose] def E8InnerFiveFour : Prop := InnerPlaneBalanceFive .E8 fun n => 5 ∣ n ^ 2 + 1

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
