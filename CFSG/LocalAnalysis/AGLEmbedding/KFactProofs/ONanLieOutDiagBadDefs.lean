module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsLie
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroPerf
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg

@[expose] def LastNodeOnly {Y : Type} [Group Y] (L J : Subgroup Y) {F : Type} [Field F]
    [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)
    (π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L) : Prop :=
  Subgroup.normalizer (((posUnipotent (rootDatum hF n)).map π : Subgroup (↥L ⧸ Subgroup.center ↥L))
      : Set (↥L ⧸ Subgroup.center ↥L)) ≤ quotImage L J ∧
    (∀ i : Fin (n / 2), i.val + 1 < n / 2 →
      ¬ (rankOne (rootDatum hF n).rootGroup i).map π ≤ quotImage L J) ∧
    ∃ i : Fin (n / 2), ¬ i.val + 1 < n / 2 ∧
      (rankOne (rootDatum hF n).rootGroup i).map π ≤ quotImage L J

@[expose] def DiagLeviBad : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2),
    Even n → 5 ∣ n →
    ∀ π : SU (unitaryInvolution F 2 2) n →* ↥L ⧸ Subgroup.center ↥L,
      Function.Surjective π → π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 2) n) →
      LastNodeOnly L J hF n π →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ 5 = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      (∀ T : Subgroup Y, IsSylowTwoOf T L →
          5 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y))) →
      (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
      ∃ X : Subgroup Y, X ≤ J ∧ Open.IsQuasisimple ↥X ∧ 5 ∣ Nat.card X ∧
        ∀ φ : ↥X →* alternatingGroup (Fin 5), ¬ φ.ker ≤ Subgroup.center ↥X

end CFSG.AGLEmbedding.LieOut
