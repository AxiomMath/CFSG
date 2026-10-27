module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerUnitaryData5
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerUnitaryData6
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.RankTwoModelTransports
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

theorem liftableNormalizerGen_twistedA5Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  have h6 : LiftableNormalizerGen (StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4)) :=
    (UnitaryData.liftableNormalizerGen_of_ok (by norm_num) unitaryData6_ok).of_mulEquiv
      (unitaryPSUEquiv unitaryFieldData_F4 (n := 6) (by norm_num))
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := he
  exact LiftableNormalizerGen.of_mulEquiv
    ((CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 _ hv).trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr CFSG.Fischer.F4.equivGaloisField.symm)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU _ 6 (2 ^ 1))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars _))).symm h6

theorem liftableNormalizerGen_twistedA4Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 4 q, hv⟩) := by
  have h5 : LiftableNormalizerGen (StatedProj (StatedSU 5 (2 ^ 1) CFSG.Fischer.F4)) :=
    (UnitaryData.liftableNormalizerGen_of_ok (by norm_num) unitaryData5_ok).of_mulEquiv
      (unitaryPSUEquiv unitaryFieldData_F4 (n := 5) (by norm_num))
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := he
  exact LiftableNormalizerGen.of_mulEquiv
    ((CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 _ hv).trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr CFSG.Fischer.F4.equivGaloisField.symm)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU _ 5 (2 ^ 1))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars _))).symm h5

end CFSG.AGLEmbedding
