module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10HS
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3Alt8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3L44
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {A B C D : Subgroup G}

theorem CSide.setup_of_firstHalf (hs : LocalSetting G L z) (hF : FirstHalfData L z A B C D) :
    CSide.Setup L A C z :=
  ⟨hs, hF.pair.1, hF.sextet, hF.cData, hF.c_elem⟩

theorem not_layerD_alt10 (hs : LocalSetting G L z) (hB : OctadType L B) (hb : OctadBasics L B)
    (hD : NData B z D) (hA8 : Alt8Data L B) :
    ¬ Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃* alternatingGroup (Fin 10)) :=
  not_nonempty_layer_alt10 (LayerD.orderOf_zt hs hB.1 hD)
    (LayerD.psi_range_equiv hs hB.1 hb hD hA8) (LayerD.centralizer_quot_eq hs hB.1 hb hD)
    (mem_centralizer_iff.2 (by
      rintro _ ⟨y, rfl⟩
      exact LayerD.psi_comm hs hB.1 hD y))

theorem not_layerD_hs
    (hs : LocalSetting G L z) (hB : OctadType L B) (hb : OctadBasics L B)
    (hD : NData B z D) (hA8 : Alt8Data L B) :
    ¬ IsSporadic (egaLayer (egQD D ⧸ fusionOddCore (egQD D))) .HS :=
  not_isSporadic_layer_hs (LayerD.orderOf_zt hs hB.1 hD)
    (LayerD.psi_range_equiv hs hB.1 hb hD hA8) (LayerD.centralizer_quot_eq hs hB.1 hb hD)
    (mem_centralizer_iff.2 (by
      rintro _ ⟨y, rfl⟩
      exact LayerD.psi_comm hs hB.1 hD y))

theorem layerC_A6A6
    (hIso : HarrisSolomonZ2S6IsoK) (hKC : CFSG.SectionRank.IsKGroupCat (egQD C))
    (hR : Ega81Residue) (hZ : fusionZStar G = ⊥)
    (hstd : standardComponentIsStandard L) (hs : LocalSetting G L z)
    (hF : FirstHalfData L z A B C D) :
    Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) := by
  obtain ⟨σ, hσ, hA, hk⟩ := sym6Data_of_type hF.pair.sextet
  have h := CSide.cLayerDisjIso hIso hKC (CSide.setup_of_firstHalf hs hF) σ hσ hA hk
  rcases h with h | h | h | h | h | h | h | h
  · exact (hR.cA6 G L z hZ hstd hs A B C D hF h).elim
  · exact h
  · exact (hR.cA8 G L z hZ hstd hs A B C D hF h).elim
  · exact (hR.cU42 G L z hZ hstd hs A B C D hF h).elim
  · exact (hR.cL52 G L z hZ hstd hs A B C D hF h).elim
  · exact (hR.cU52 G L z hZ hstd hs A B C D hF h).elim
  · exact (hR.cSp44 G L z hZ hstd hs A B C D hF h).elim
  · exact (hR.cU43 G L z hZ hstd hs A B C D hF h).elim

theorem red_of_residue
    (hAut : AtlasL44Aut) (hRank : AtlasL44ThreeRank) (hFix : AtlasL44FixedPoints)
    (hR : Ega81Residue) : Ega81Lemmas214to217Red := by
  intro hIso G _ _ L z hKS hZ hstd hs A B C D hF hLD
  have hA8 := alt8Data_of_type hF.pair.octad
  have h10 := not_layerD_alt10 hs hF.pair.octad hF.octad hF.nData hA8
  have hHS := not_layerD_hs hs hF.pair.octad hF.octad hF.nData hA8
  have hrank : HasElemAbThree81 (egQD D ⧸ fusionOddCore (egQD D)) :=
    hR.cStruct G L z hZ hstd hs A B C D hF
      (layerC_A6A6 hIso (hF.cData.isKGroupCat_egQD hKS) hR hZ hstd hs hF)
  rcases hLD with h | h | h | h | h
  · exact (not_hasElemAbThree81_of_layer_alt8 (LayerD.orderOf_zt hs hF.pair.octad.1 hF.nData)
      (LayerD.psi_range_equiv hs hF.pair.octad.1 hF.octad hF.nData hA8)
      (LayerD.centralizer_quot_eq hs hF.pair.octad.1 hF.octad hF.nData)
      (mem_centralizer_iff.2 (by
        rintro _ ⟨y, rfl⟩
        exact LayerD.psi_comm hs hF.pair.octad.1 hF.nData y)) h hrank).elim
  · exact hR.dPos G L z hZ hstd hs A B C D hF h
  · exact (h10 h).elim
  · exact (not_hasElemAbThree81_of_layer_L44 hAut hRank hFix
      (LayerD.orderOf_zt hs hF.pair.octad.1 hF.nData)
      (LayerD.psi_range_equiv hs hF.pair.octad.1 hF.octad hF.nData hA8)
      (LayerD.centralizer_quot_eq hs hF.pair.octad.1 hF.octad hF.nData)
      (mem_centralizer_iff.2 (by
        rintro _ ⟨y, rfl⟩
        exact LayerD.psi_comm hs hF.pair.octad.1 hF.nData y)) h hrank).elim
  · exact (hHS h).elim

end CFSG.EvenSporadicStandard.M24Std
