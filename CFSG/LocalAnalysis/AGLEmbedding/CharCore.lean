module

public import CFSG.Open.GLBDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Quasithin.Background.C1Basic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem maxTwoLocal_normalizer_eq_of_le_normalizer {H C : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) = H :=
  hH.2 _ ⟨C, hC, hC2, rfl⟩ hHC

theorem le_normalizer_of_characteristic_pCoreOf {H C : Subgroup G} (hCS : C ≤ pCoreOf 2 H)
    (hchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic) :
    H ≤ Subgroup.normalizer (C : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := pCoreOf 2 H) (C.subgroupOf (pCoreOf 2 H))
  rw [Subgroup.map_subgroupOf_eq_of_le hCS] at h
  exact (localGroup_le_normalizer_pCoreOf 2 H).trans h

theorem maxTwoLocal_normalizer_char_eq {H C : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hCS : C ≤ pCoreOf 2 H) (hC : C ≠ ⊥) (hchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic) :
    Subgroup.normalizer (C : Set G) = H :=
  maxTwoLocal_normalizer_eq_of_le_normalizer hH hC ((pCoreOf_isPGroup 2 H).to_le hCS)
    (le_normalizer_of_characteristic_pCoreOf hCS hchar)

theorem maxTwoLocal_cgsIn_eq_inf {H : Subgroup G} (hH : GLBIsMaxTwoLocal H) (X : Subgroup G) :
    CFSG.Quasithin.cgsIn X (pCoreOf 2 H) = X ⊓ H := by
  apply le_antisymm
  · exact iSup_le fun C => iSup_le fun hCS => iSup_le fun hC => iSup_le fun hchar =>
      inf_le_inf_left X (maxTwoLocal_normalizer_char_eq hH hCS hC hchar).le
  · have h := CFSG.Quasithin.inf_normalizer_le_cgsIn (H := X) (twoLocal_pCoreOf_ne_bot H hH.1)
    rwa [← maxTwoLocal_eq_normalizer_pCoreOf H hH] at h

theorem maxTwoLocal_cgsIn_lt {H X : Subgroup G} (hH : GLBIsMaxTwoLocal H) (hXH : ¬ X ≤ H) :
    CFSG.Quasithin.cgsIn X (pCoreOf 2 H) < X := by
  rw [maxTwoLocal_cgsIn_eq_inf hH]
  exact lt_of_le_of_ne inf_le_left fun h => hXH (inf_eq_left.mp h)

end CFSG.AGLEmbedding
