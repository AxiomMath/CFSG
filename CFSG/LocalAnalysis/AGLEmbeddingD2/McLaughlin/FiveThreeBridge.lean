module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem normalizer_omegaOneCenter_le (hA : Asc81bHyp M S) :
    M ⊓ Subgroup.normalizer (omegaOneCenterOf S : Set G) ≤ Subgroup.normalizer (S : Set G) := by
  have hS2 : IsPGroup 2 S := by
    rw [hA.twoRadical.2.2]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hne : omegaOneCenterOf S ≠ ⊥ :=
    Setup.omegaOneCenterOf_ne_bot hS2 hA.twoRadical.2.1
  have hle : M ⊓ Subgroup.normalizer (omegaOneCenterOf S : Set G) ≤ cgsIn M S :=
    le_iSup₂_of_le (f := fun (C : Subgroup G) (_ : C ≤ S) => ⨆ (_ : C ≠ ⊥)
      (_ : (C.subgroupOf S).Characteristic), M ⊓ Subgroup.normalizer (C : Set G))
      (omegaOneCenterOf S) (Setup.omegaOneCenterOf_le S)
      (le_iSup₂_of_le (f := fun (_ : omegaOneCenterOf S ≠ ⊥)
        (_ : ((omegaOneCenterOf S).subgroupOf S).Characteristic) =>
          M ⊓ Subgroup.normalizer (omegaOneCenterOf S : Set G)) hne
        (Setup.characteristic_omegaOneCenterOf S) le_rfl)
  rw [hA.cgs] at hle
  exact hle.trans inf_le_right

theorem not_le_centralizer_omegaOneCenter (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) :
    ¬ L ≤ Subgroup.centralizer (omegaOneCenterOf S : Set G) := fun h =>
  hL.not_le_normalizer ((le_inf hL.le (h.trans (Subgroup.centralizer_le_normalizer _))).trans
    (normalizer_omegaOneCenter_le hA))

theorem not_le_centralizer_mModule (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) :
    ¬ L ≤ Subgroup.centralizer (mModule M S : Set G) := fun h =>
  not_le_centralizer_omegaOneCenter hA hL
    (h.trans (Subgroup.centralizer_le (omegaOneCenterOf_le_mModule M S)))

end CFSG.AGLEmbeddingD2.McLaughlin
