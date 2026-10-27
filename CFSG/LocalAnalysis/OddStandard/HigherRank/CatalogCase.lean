module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.NotInChev2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.FixedComponent
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Blueprint CFSG.Yardstones.M0362f3a873a3

theorem oddLieType_of_catalog_of_not_inChev2
    (hP1 : ComponentClassification.GS82PumpInputs.ChevOddPumpLeaf)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (hcat : Catalog G) (hlie : OddLieType (L ⧸ center L))
    (hL2 : ¬ L2OrReeLieQuotient (L ⧸ center L)) (hnot : ¬ GH74.GLS.InChev2 (L ⧸ center L)) :
    OddLieType G := by
  have hstd : CFSG.Open.standardComponentIsStandard L := hS.standard
  obtain ⟨t, ht, ht2⟩ := exists_involution_of_standard hstd
  have hpf := properFixedComponent_of_standard hS ht ht2
  obtain ⟨r, hr, hr2, hchev⟩ := exists_isSimpleChevalleyOver_of_oddLieType hstd hlie
  have hnot' := not_inChev2_fusionZStar_of_standard hstd hnot
  rcases hP1 G hS.simple hS.nonab hcat (MulAut.conj t) L hpf r hr hr2 hchev hnot' with
    ⟨⟨τ, n, f, hm⟩, -⟩ | ⟨-, h17⟩
  · exact oddLieType_of_lieModel_of_ne_two hm hr hr2
  · exact absurd (Or.inl ⟨17, 1,
      (lieModel_fusionZStar_iff_of_standard hstd .PSL 2 17 1).2 h17⟩) hL2

section


theorem oddLieType_of_catalog
    (hP1 : ComponentClassification.GS82PumpInputs.ChevOddPumpLeaf)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (hcat : Catalog G) (hlie : OddLieType (L ⧸ center L))
    (hF3 : ¬ SmallF3LieQuotient (L ⧸ center L)) (hL2 : ¬ L2OrReeLieQuotient (L ⧸ center L))
    (hA6 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6))) : OddLieType G :=
  oddLieType_of_catalog_of_not_inChev2 hP1 hS hcat hlie hL2 (not_inChev2 hlie hF3 hL2 hA6)

end

end CFSG.OddStandard.HigherRank
