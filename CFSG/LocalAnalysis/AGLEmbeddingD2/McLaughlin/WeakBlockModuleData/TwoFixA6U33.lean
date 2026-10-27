module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTRFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem pairBlockFixed_of_A6U33 (hCF : CitedFive) (hU33 : U33Atlas) {G : Type} [Group G]
    [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hrow : IsA6OrU33 ↥(barM M L))
    {y : G} (hy : y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H)) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have hpr := hctx.pair
  have hVMe : IsElemAbelian 2 (Quasithin.omegaOneCenterOf (pCoreOf 2 M)) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hMV : M ≤ Subgroup.normalizer
      ((Quasithin.omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_of_characteristic_pCoreOf
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hVXV : mModule M (pCoreOf 2 H) ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M) :=
    mModule_le hpr.omegaOneCenter_le.1 hMV
  have hV : y ∈ mModule M (pCoreOf 2 H) := omegaOneCenterOf_le_mModule M (pCoreOf 2 H) hy
  have hV2 : ∀ x ∈ mModule M (pCoreOf 2 H), x ^ 2 = 1 := fun x hx => hVMe.2 x (hVXV hx)
  have hVc : ∀ a ∈ mModule M (pCoreOf 2 H), ∀ b ∈ mModule M (pCoreOf 2 H), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, hVXV ha⟩ ⟨b, hVXV hb⟩)
  have hLV : L ≤ Subgroup.normalizer ((mModule M (pCoreOf 2 H) : Subgroup G) : Set G) :=
    hL.le.trans (normalizer_mModule M _)
  have hJ := not_commutator_thompsonJ_le hpr hL
  rcases hrow with he | hU
  · obtain ⟨e⟩ := he
    have h6 := (hCF G M (pCoreOf 2 H) L hpr.isKGroup.1 hpr.asc81bHyp hL hJ (Or.inl ⟨e⟩)).2.1
      ⟨e⟩
    exact three_dvd_of_socleLE_alt_six hL.le hLV hV2 hVc e h6 hV
  · have h33 := (hCF G M (pCoreOf 2 H) L hpr.isKGroup.1 hpr.asc81bHyp hL hJ
      (Or.inr (Or.inr hU))).2.2 hU
    exact three_dvd_of_socleLE_u33 hU33 hL.le hLV hV2 hVc hU h33 hV

end CFSG.AGLEmbeddingD2.McLaughlin
