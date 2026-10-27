module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Cores
public import CFSG.LocalAnalysis.OddStandard.SmallF3.CatalogLie
public import CFSG.LocalAnalysis.OddStandard.SmallF3.CatalogSporadic
public import CFSG.LocalAnalysis.OddStandard.AltNoHe

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3Interfaces

theorem smallF3LieQuotient_of_omegaQuotient {Q : Type} [Group Q] (h : SmallF3OmegaQuotient Q) :
    SmallF3LieQuotient Q := by
  unfold SmallF3OmegaQuotient at h
  unfold SmallF3LieQuotient
  rcases h with h | h | h | h | h | h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))

section Certified


theorem oddLieType_of_catalog {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) (hQ : SmallF3LieQuotient (L ⧸ center L))
    (hcat : Blueprint.Catalog G) : OddLieType G := by
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hS.nonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · obtain ⟨m, -, ⟨eL⟩⟩ :=
      CFSG.OddStandard.exists_mulEquiv_alternatingGroup_of_standard e hS.standard
    exact (not_nonempty_mulEquiv_alternatingGroup hQ m ⟨eL⟩).elim
  · obtain ⟨τ, n, r, f, hm⟩ := exists_lieModel_of_classicalRep_or_exceptionalRep (.inl hcl)
    exact oddLieType_of_lieModel_of_standard hS.standard hm
  · obtain ⟨τ, n, r, f, hm⟩ := exists_lieModel_of_classicalRep_or_exceptionalRep (.inr hex)
    exact oddLieType_of_lieModel_of_standard hS.standard hm
  · exact (not_sporadicRep_of_standard hS hQ hsp).elim

theorem smallF3L33Block_of_core (h : SmallF3L33Core) : SmallF3L33Block := by
  unfold SmallF3L33Block
  intro G _ _ L hC hm
  by_cases hcat : Blueprint.Catalog G
  · exact oddLieType_of_catalog hC.toStandardSetting
      (by unfold SmallF3LieQuotient; exact Or.inl hm) hcat
  · exact (h G L hC hcat hm).elim

theorem smallF3U33Block_of_core (h : SmallF3U33Core) : SmallF3U33Block := by
  unfold SmallF3U33Block
  intro G _ _ L hC hm
  by_cases hcat : Blueprint.Catalog G
  · exact oddLieType_of_catalog hC.toStandardSetting
      (by unfold SmallF3LieQuotient; exact Or.inr (Or.inl hm)) hcat
  · exact (h G L hC hcat hm).elim

theorem smallF3OmegaBlock_of_core (h : SmallF3OmegaCore) : SmallF3OmegaBlock := by
  unfold SmallF3OmegaBlock
  intro G _ _ L hC hQ
  by_cases hcat : Blueprint.Catalog G
  · exact oddLieType_of_catalog hC.toStandardSetting
      (smallF3LieQuotient_of_omegaQuotient hQ) hcat
  · exact (h G L hC hcat hQ).elim

end Certified

end CFSG.OddStandard.SmallF3
