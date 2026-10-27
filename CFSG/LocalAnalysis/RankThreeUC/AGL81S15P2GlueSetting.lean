module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2MBlock
import CFSG.Quasithin.H13.NQCatA314ShortMap
import CFSG.Quasithin.Background.SimsD1TransBlock
import CFSG.Quasithin.H13.NQS1312H
import CFSG.Quasithin.H13.LocDblCriterion

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.AGLEmbedding
open KFactsPair CFSG.Open

theorem noXBlock_subgroupOf_of_noXBlock {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hNB : ∀ B : Subgroup X, B ≤ M → IsSubnormal B M → InClassXBlock B → False) :
    ∀ Y : Subgroup ↥M, IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hY hB
  have h1 : IsSubnormal (Y.map M.subtype) M := by
    have h := IsSubnormal.map M.subtype hY
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  refine hNB (Y.map M.subtype) (Subgroup.map_subtype_le Y) h1 ⟨?_, ?_⟩
  · exact CFSG.QuasithinUnique.Setup.Wreath.IsShort2.map_of_injective _
      M.subtype_injective hB.1
  · rcases hB.2 with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact Or.inl ⟨n, hn,
        CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective' _ M.subtype_injective h⟩
    · exact Or.inr ⟨n, hn, (CFSG.Quasithin.SimsD1.TransBlock.isAltType_map_iff _
        M.subtype_injective Y (2 * n + 1)).mpr h⟩

theorem gnSetting_subgroupOf_of_noXBlock {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (hX : GNSetting X T) (hTM : T ≤ M)
    (hNB : ∀ B : Subgroup X, B ≤ M → IsSubnormal B M → InClassXBlock B → False) :
    GNSetting ↥M (T.subgroupOf M) where
  kGroup := CFSG.IsKGroup.subgroup hX.kGroup M
  sylow := CFSG.Quasithin.H13.LocDbl.isSylowTwoOf_subgroupOf_top
    (CFSG.Quasithin.H13.U3.NLine.isSylowTwoOf_of_le_top hX.sylow hTM)
  charTwo := CFSG.AGLEmbeddingD2.McLaughlin.charTwo_top_of_le hX.charTwo
    ((CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans hTM) le_top
  noXBlock := noXBlock_subgroupOf_of_noXBlock hNB

theorem gnSetting_oddHull_sup_gnImg {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {Ls P₂ : Subgroup (X ⧸ gnC T)}
    (he : Nonempty (↥Ls ≃* alternatingGroup (Fin 10))) (hP₂ : P₂ ≤ Ls)
    (hshape : IsTwoFourSFive P₂)
    (hTP : gnImg T T ≤ Subgroup.normalizer (P₂ : Set (X ⧸ gnC T))) :
    GNSetting ↥((oddHull P₂ ⊔ gnImg T T).comap (toStar T))
      (T.subgroupOf ((oddHull P₂ ⊔ gnImg T T).comap (toStar T))) := by
  refine gnSetting_subgroupOf_of_noXBlock hX ?_
    (noXBlock_oddHull_sup_gnImg hX he hP₂ hshape hTP)
  intro t ht
  exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (toStar T) ht))

end CFSG.LocalAnalysis.RankThreeUC.S15
