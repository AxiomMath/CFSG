module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Malle.Proving.E8CubeOrders
public import CFSG.LieType.SeitzGeneration.UnitaryHyperRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem nonempty_mulEquiv_of_centralizer_eq_bot {Y : Type*} [Group Y] {K : Subgroup Y}
    {G : Type*} [Group G] (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (e : K ⧸ Subgroup.center K ≃* G) : Nonempty (K ≃* G) := by
  have hZ : Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzC : (z : Y) ∈ Subgroup.centralizer (K : Set Y) :=
      Subgroup.mem_centralizer_iff.2 fun k hk =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
    rw [hC, Subgroup.mem_bot] at hzC
    exact (Subgroup.mem_bot).2 (Subtype.ext hzC)
  exact ⟨((QuotientGroup.quotientBot (G := K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩

end CFSG.AGLEmbedding
