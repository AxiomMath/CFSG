module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open CFSG.Quasithin CFSG.QuasithinUnique.Setup

@[expose] def OddPrimeCoreExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W), Function.Injective ρ → CFSG.pCore 2 X = ⊥ →
    ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ R A : Subgroup X, IsPGroup r R → R.Normal →
      CFSG.IsElementaryAbelian 2 A → CFSG.RankThree.FFModules.IsBestOffender ρ A → ⁅R, A⁆ = ⊥

@[expose] def ComponentSectionProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W), Function.Injective ρ → CFSG.pCore 2 X = ⊥ →
    ∀ A : Subgroup X, CFSG.IsElementaryAbelian 2 A →
      CFSG.RankThree.FFModules.IsBestOffender ρ A →
    ∀ K : Subgroup X, CFSG.Open.IsComponentOf K ⊤ → ⁅K, A⁆ ≠ ⊥ →
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V) (f : ↥K →* MulAut V) (E : Subgroup (MulAut V)),
      (∀ v : V, v * v = 1) ∧ f.range ≠ ⊥ ∧ X1.IsIrrOn f.range ∧
      E ≤ Subgroup.normalizer (f.range : Set (MulAut V)) ∧ E ≠ ⊥ ∧ IsElemAbelian2 E ∧
      IsQuadratic E ∧ Nat.card V ≤ Nat.card E * Nat.card (fixV E)

@[expose] def L34ExclusionProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ L E : Subgroup (MulAut V), X1.IsIrrOn L → AGLEmbedding.IsLinThreeFour ↥L →
      E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E * Nat.card (fixV E) < Nat.card V

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
