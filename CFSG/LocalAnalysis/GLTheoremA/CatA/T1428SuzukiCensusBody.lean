module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem suzuki_census_body (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    ∀ η : MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived _ →
      η ^ 3 = 1 → η ≠ 1 →
      ∀ r : ℕ, Odd r → 1 < r →
      ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group,
        CFSG.Open.IsComponentOf J₁ (fixSubgroup η) → CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₃ (fixSubgroup η) → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
        catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
        catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
        catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) →
        (catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group
            (S10.isU6n r) ∧
          ∀ M : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group,
            CFSG.Open.IsComponentOf M (fixSubgroup η) →
              catalogIs (↥M ⧸ Subgroup.center ↥M) (S10.isL2n r)) ∨
        catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group (T1428.isD4n r) := by
  intro η hη hη3 hη1
  exact absurd ⟨η, hη, hη3, hη1⟩ (suzuki_catalogue_no_order_three m hv)

end CFSG.LocalAnalysis.GLTheoremA
