module

public import CFSG.CGT.HaradaParrott80.Smith
public import CFSG.RankThree.GF2n.Item310BridgesLie
public import CFSG.Adapters.ClassicalCatalogLinearUnitary

public section

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique CFSG.RankThree.GF2n

theorem Setting.inCatalog_of_not_le
    (hS : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP)
    {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
    (hH1 : H1Natural m) (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)}
    (ha1 : a ≠ 1) (ha : quadQ m (Multiplicative.toAdd (S.beta a)) = 0)
    (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G := by
  rcases Setting.smithList_of_not_le hS S hH1 hC ha1 ha hnot with ⟨-, h⟩ | ⟨-, h⟩
  · rcases h with h | h | h | h | h | h | h | h | h | h
    · exact CFSG.ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 6 2 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact CFSG.ClassicalModels.statedClassicalModel_PSU_inCatalog G 6 2 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact pOmegaPlusBridge G 4 2 1 le_rfl (statedClassicalModel_of_lieModel (by decide) h)
    · exact pOmegaMinusBridge G 4 2 1 le_rfl (statedClassicalModel_of_lieModel (by decide) h)
    · exact chevalleyEvenBridge_trialityD4 G 1
        (chevalleyExceptionalModel_of_lieModel (by decide) h)
    · exact pOmegaPlusBridge G 4 3 1 le_rfl (statedClassicalModel_of_lieModel (by decide) h)
    · exact sporadicBridge_Co2 G h
    · exact sporadicBridge_Co1 G h
    · exact sporadicBridge_Th G h
    · exact sporadicBridge_HN G h
  · rcases h with h | h | h | h | h | h
    · exact CFSG.ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 8 2 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact CFSG.ClassicalModels.statedClassicalModel_PSU_inCatalog G 8 2 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact pOmegaPlusBridge G 5 2 1 (by norm_num) (statedClassicalModel_of_lieModel (by decide) h)
    · exact pOmegaMinusBridge G 5 2 1 (by norm_num) (statedClassicalModel_of_lieModel (by decide) h)
    · exact sporadicBridge_J4 G h
    · exact sporadicBridge_Fi24Prime G h

end CFSG.CGT.Harada80
