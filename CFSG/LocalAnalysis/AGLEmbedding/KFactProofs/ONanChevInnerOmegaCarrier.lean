module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmegaData
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

theorem statedScalars_zmod_two : StatedScalars ι8 (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  have : u = 1 := Subsingleton.elim _ _
  rw [this, map_one]
  exact Subgroup.one_mem _

noncomputable def om8EquivProj : Om8 ≃* projOmegaPlus 4 (GaloisField 2 1) :=
  (((QuotientGroup.quotientMulEquivOfEq (by
    rw [statedScalars_zmod_two]
    exact Subgroup.bot_subgroupOf _)).trans QuotientGroup.quotientBot).symm).trans
    (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
      (CFSG.Adapters.RankTwoModelTransports.glCongr f2)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega f2
        (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.statedQuadPlus_comp f2 4))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars f2)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.projImage_statedOmegaPlus_eq_projOmegaPlus 4 _))

theorem liftableNormalizerGen_D4Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Census.bridgeOmega8PlusTwo q hv hp he
  exact ((OmegaData.liftableNormalizerGen_Om8 omegaData_ok).of_mulEquiv om8EquivProj).of_mulEquiv
    e.symm

end CFSG.AGLEmbedding
