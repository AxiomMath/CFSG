module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Holds
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockG25
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockPermProd
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduce
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Orders
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactBlockNoL33U35L37HeRankFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      ⁅V, V⁆ = V → ∀ (U : Type) [Group U] [Finite U] [IsSimpleGroup U] (ψ : ↥V →* U),
        Function.Surjective ψ → ¬ IsL33U35L37HeOrder (Nat.card U)

@[expose] def KFactBlockNoG25RankFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      ⁅V, V⁆ = V → ∀ (U : Type) [Group U] [Finite U] [IsSimpleGroup U] (ψ : ↥V →* U),
        Function.Surjective ψ → ¬ IsG25Order (Nat.card U)

section Reduce

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
variable {O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
variable {V : Subgroup G}
variable {U : Type} [Group U] [Finite U] [IsSimpleGroup U]

theorem kFactBlockNoL33_nineThreeEight_rankFree {N r : ℕ}
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃*
      (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))))
    (hO : O ≤ blockParabolic M S L)
    (hPO : blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hV : barM M V ≤ blockParabolic M S L)
    (hPVO : blockParabolic M S L ≤
      Subgroup.normalizer ((barM M V ⊔ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V) (h3U : 3 ∣ Nat.card U)
    {ψ' : ↥(barM M V) →* U} (hψ' : Function.Surjective ψ')
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False :=
  LeviBlock.false_of_permProd_quotient_of_normal_section (P := blockParabolic M S L)
    (W := barM M V) (O := O) hO hV hPO hPVO hOc (commutator_barM_eq_self hVM hVV) e h3U
    (fun hc => LeviBlock.card_alternatingGroup_not_isL33U35L37HeOrder r (hc ▸ hd))
    (fun hc => LeviBlock.card_alternatingGroup_not_isL33U35L37HeOrder (N - 2 * r) (hc ▸ hd))
    (ψ'.comp (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom)
    (hψ'.comp (MulEquiv.surjective _))

theorem kFactBlockNoG25_nineThreeEight_rankFree {N r : ℕ}
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃*
      (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))))
    (hO : O ≤ blockParabolic M S L)
    (hPO : blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hV : barM M V ≤ blockParabolic M S L)
    (hPVO : blockParabolic M S L ≤
      Subgroup.normalizer ((barM M V ⊔ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V) (h3U : 3 ∣ Nat.card U)
    {ψ' : ↥(barM M V) →* U} (hψ' : Function.Surjective ψ')
    (hd : IsG25Order (Nat.card U)) : False :=
  LeviBlock.false_of_permProd_quotient_of_normal_section (P := blockParabolic M S L)
    (W := barM M V) (O := O) hO hV hPO hPVO hOc (commutator_barM_eq_self hVM hVV) e h3U
    (fun hc => LeviBlock.card_alternatingGroup_not_isG25Order r (hc ▸ hd))
    (fun hc => LeviBlock.card_alternatingGroup_not_isG25Order (N - 2 * r) (hc ▸ hd))
    (ψ'.comp (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom)
    (hψ'.comp (MulEquiv.surjective _))

end Reduce

theorem kFactBlockNoL33U35L37HeRankFree_of (hTPL : CitedBlockTransvectionPL)
    (hA7 : CitedBlockAltSevenPL) (hC : KFactCompParabNoL33U35L37He) :
    KFactBlockNoL33U35L37HeRankFree := by
  intro G _ _ M S L hK hA hL h93 hX hS O V hVM hO hV hPO hOc hPVO hVV U _ _ _ ψ hψ hd
  have h3U : 3 ∣ Nat.card U := LeviBlock.three_dvd_of_isL33U35L37HeOrder hd
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_surj_barM h3U hVM ψ hψ
  have hU : Nat.card U ∣ Nat.card (blockParabolic M S L) :=
    (Subgroup.card_dvd_of_surjective hψ').trans (Subgroup.card_dvd_of_le hV)
  rcases h93 with h1 | h2 | h3c | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact kFactBlockNoL33_nineThreeTwo hC hA hL hS h2 hO hPO hOc hV hPVO hVM hVV hψ' hd
  · rcases hTPL G M S L hK hA hL hX hS h3c with
      ⟨k, d', hk, ⟨q', hq', hdq'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact kFactBlockNoL33_nineThreeThree_sp hk hq' hdq' e hO hPO hOc hV hPVO h3U hψ' hU hd
    · exact kFactBlockNoL33_nineThreeThree_perm hn e hU hd
  · exact kFactBlockNoL33_nineThreeFour h4 hU hd
  · exact kFactBlockNoL33_nineThreeFive hA7 hK hA hL hX hS h5 hU hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact kFactBlockNoL33_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact kFactBlockNoL33_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, N, r, -, -, -, -, -, -, e, -, -⟩ := h8
    exact kFactBlockNoL33_nineThreeEight_rankFree e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd

theorem kFactBlockNoG25RankFree_of (hTPL : CitedBlockTransvectionPL)
    (hA7 : CitedBlockAltSevenPL) (hC : KFactCompParabNoG25) :
    KFactBlockNoG25RankFree := by
  intro G _ _ M S L hK hA hL h93 hX hS O V hVM hO hV hPO hOc hPVO hVV U _ _ _ ψ hψ hd
  have h3U : 3 ∣ Nat.card U := LeviBlock.three_dvd_of_isG25Order hd
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_surj_barM h3U hVM ψ hψ
  have hU : Nat.card U ∣ Nat.card (blockParabolic M S L) :=
    (Subgroup.card_dvd_of_surjective hψ').trans (Subgroup.card_dvd_of_le hV)
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact kFactBlockNoG25_nineThreeTwo hC hA hL hS h2 hO hPO hOc hV hPVO hVM hVV hψ' hd
  · rcases hTPL G M S L hK hA hL hX hS h3 with
      ⟨k, d', hk, ⟨q', hq', hdq'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact kFactBlockNoG25_nineThreeThree_sp hk hq' hdq' e hO hPO hOc hV hPVO h3U hψ' hU hd
    · exact kFactBlockNoG25_nineThreeThree_perm hn e hU hd
  · exact kFactBlockNoG25_nineThreeFour h4 hU hd
  · exact kFactBlockNoG25_nineThreeFive hA7 hK hA hL hX hS h5 hU hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact kFactBlockNoG25_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact kFactBlockNoG25_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, N, r, -, -, -, -, -, -, e, -, -⟩ := h8
    exact kFactBlockNoG25_nineThreeEight_rankFree e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd

theorem kFactBlockNoL33U35L37HeRankFree_holds :
    KFactBlockNoL33U35L37HeRankFree := by
  have hTPL : CitedBlockTransvectionPL :=
    citedBlockTransvectionPL_of_type
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  have hA7 : CitedBlockAltSevenPL := citedBlockAltSevenPL_holds
  exact kFactBlockNoL33U35L37HeRankFree_of hTPL hA7 kFactCompParabNoL33U35L37He_holds

theorem kFactBlockNoG25RankFree_holds :
    KFactBlockNoG25RankFree := by
  have hTPL : CitedBlockTransvectionPL :=
    citedBlockTransvectionPL_of_type
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  have hA7 : CitedBlockAltSevenPL := citedBlockAltSevenPL_holds
  exact kFactBlockNoG25RankFree_of hTPL hA7 kFactCompParabNoG25_holds

end CFSG.AGLEmbedding
