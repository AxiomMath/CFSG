module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

@[expose] def EndKnownGroupsInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → Blueprint.Catalog X →
    ∀ (z t : X) (K P D : Subgroup X), IsTwoComponentAt z K →
      (∀ K₂ : Subgroup X, IsTwoComponentAt z K₂ → K₂ = K) →
      IsSimpleGroup (K ⧸ pPrimeCore 2 K) → FooteFamilyType K →
      IsEmpty (X ≃* K ⧸ pPrimeCore 2 K) → IsSylowOf 2 P K → t ∈ P → orderOf t = 2 →
      z * t = t * z → z ∈ D → D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K →
      P ≤ centralizer (D : Set X) → AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D →
      Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) →
      (∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup X, IsTwoComponentAt b Y ∧ P ≤ Y ∧
        Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)) →
      ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set X))

end CFSG.ComponentClassification.Foote5
