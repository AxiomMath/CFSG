module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section LongRoot


@[expose] def twE6RootSubgroup (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (β : Fin TwistTag.E6.tag.rank → ℤ) : Subgroup (twistedE6RootGroup K σ) :=
  (rootSubgroup TwistTag.E6.tag K β).comap (twistedE6RootGroup K σ).subtype

@[expose] def IsTwE6LongRootPair (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (X Xm : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ g : twistedE6RootGroup K σ,
    X = (twE6RootSubgroup K σ e6HighestRoot).map (MulAut.conj g).toMonoidHom ∧
    Xm = (twE6RootSubgroup K σ (-e6HighestRoot)).map (MulAut.conj g).toMonoidHom

@[expose] def twE6LongRootSL2 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X Xm : Subgroup (twistedE6RootGroup K σ)) : Subgroup (twistedE6RootGroup K σ) :=
  Subgroup.closure ((X : Set (twistedE6RootGroup K σ)) ∪ (Xm : Set (twistedE6RootGroup K σ)))

@[expose] def twE6LongRootTorus {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X Xm : Subgroup (twistedE6RootGroup K σ)) : Subgroup (twistedE6RootGroup K σ) :=
  twE6LongRootSL2 X Xm ⊓ Subgroup.normalizer (X : Set (twistedE6RootGroup K σ)) ⊓
    Subgroup.normalizer (Xm : Set (twistedE6RootGroup K σ))

@[expose] def twE6LongRootParabolic {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X : Subgroup (twistedE6RootGroup K σ)) : Subgroup (twistedE6RootGroup K σ) :=
  Subgroup.normalizer (X : Set (twistedE6RootGroup K σ))

@[expose] def twE6LongRootRadical {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X : Subgroup (twistedE6RootGroup K σ)) : Subgroup (twistedE6RootGroup K σ) :=
  (CFSG.pCore (ringChar K) (twE6LongRootParabolic X)).map (twE6LongRootParabolic X).subtype

@[expose] def twE6LongRootLevi {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X Xm : Subgroup (twistedE6RootGroup K σ)) : Subgroup (twistedE6RootGroup K σ) :=
  ⁅Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)),
    Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ))⁆

@[expose] def TwE6LongRootParabolicStructure : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm →
      X ≤ twE6LongRootRadical X

@[expose] def TwE6LongRootIrreducible : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm →
      ∀ M : Subgroup (twistedE6RootGroup K σ), X ≤ M → M ≤ twE6LongRootRadical X →
        (∀ g ∈ twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm,
          M.map (MulAut.conj g).toMonoidHom = M) →
        M = X ∨ M = twE6LongRootRadical X

@[expose] def TwE6LongRootGenerates : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm →
      ∃ n ∈ twE6LongRootSL2 X Xm,
        Subgroup.closure ((twE6LongRootRadical X : Set (twistedE6RootGroup K σ)) ∪
          ((twE6LongRootRadical X).map (MulAut.conj n).toMonoidHom :
            Set (twistedE6RootGroup K σ))) = ⊤

end LongRoot

end CFSG.LieType.SeitzGeneration.ExcWideThree
