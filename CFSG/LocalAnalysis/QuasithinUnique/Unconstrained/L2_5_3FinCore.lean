module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinShape
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

@[expose] def RadicalNormalizerCharTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K → ComponentList M S z K →
        ∀ R : Subgroup G, R ≤ conjJoin H K → IsPGroup 2 R →
          (∀ L : Subgroup G, IsComponentIn L H → L ≤ conjJoin H K →
            ¬ R ≤ Subgroup.centralizer (L : Set G)) →
          pCoreOf 2 (conjJoin H K ⊓ Subgroup.normalizer (R : Set G)) = R →
            CharTwo (conjJoin H K ⊓ Subgroup.normalizer (R : Set G))

@[expose] def RadicalCharacteristic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K → ComponentList M S z K →
        ∀ R : Subgroup G, R ≤ conjJoin H K → IsPGroup 2 R → radicalOf M H K ≤ R →
          Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (radicalOf M H K : Set G)

theorem lemma253Core (h252 : Lemma252) (hF1 : RadicalNormalizerCharTwo)
    (hF2 : RadicalCharacteristic) : Lemma253Core := by
  intro G _ _ T M H S z U HU hs ht hHn hmaxP hUS hmaxU hexists hBe hI
  obtain ⟨K, hK⟩ := hexists
  obtain ⟨k, B, hB, hH⟩ := hHn
  obtain ⟨hbang, -, -, -, hQU, hzQ⟩ := upair_saturation hs.setting ht B hB hH hmaxP hUS
  have hcl : ∀ L : Subgroup G, IsComponentIn L H → ComponentList M S z L :=
    fun L hL => h252 G T M H S z hs ht L hL
  have hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L :=
    fun L hL => (hcl L hL).2.1
  obtain ⟨hDS, hDcen, d, hdD, hdact⟩ := dShape hs ht hinn hK
  have hHD : H ≤ Subgroup.normalizer (conjJoin H K : Set G) := le_normalizer_conjJoin H K
  have hDH : conjJoin H K ≤ H := conjJoin_le_self hK.1
  have hHUH : HU ≤ H := hmaxP.1.2
  have hHUD : HU ≤ Subgroup.normalizer (conjJoin H K : Set G) := hHUH.trans hHD
  have hHUN : HU ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hQ2 : IsPGroup 2 (pCoreOf 2 HU) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hQH : pCoreOf 2 HU ≤ H :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 HU).trans hHUH
  have hQD : pCoreOf 2 HU ≤ Subgroup.normalizer (conjJoin H K : Set G) := hQH.trans hHD
  have hR02 : IsPGroup 2 ↥(pCoreOf 2 HU ⊓ conjJoin H K) := hQ2.to_le inf_le_left
  have hHUR0 : HU ≤ Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf HU _ _ hHUN hHUD
  have hY2 : IsPGroup 2 ↥(conjJoin H K ⊓
      (pCoreOf 2 HU ⊔ Subgroup.centralizer (conjJoin H K : Set G))) :=
    isPGroup_inf_sup_centralizer hQ2 hQD hDcen
  have hHUY : HU ≤ Subgroup.normalizer ((conjJoin H K ⊓
      (pCoreOf 2 HU ⊔ Subgroup.centralizer (conjJoin H K : Set G)) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf HU _ _ hHUD
      (le_normalizer_sup hHUN (hHUD.trans (normalizer_le_normalizer_centralizer _)))
  have hYQ : conjJoin H K ⊓ (pCoreOf 2 HU ⊔ Subgroup.centralizer (conjJoin H K : Set G)) ≤
      pCoreOf 2 HU := hbang _ (inf_le_left.trans hDH) hY2 hHUY
  have hzc : z * d⁻¹ ∈ Subgroup.centralizer (conjJoin H K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hdact x hx
    calc x * (z * d⁻¹) = z * (z⁻¹ * x * z) * d⁻¹ := by group
      _ = z * (d⁻¹ * x * d) * d⁻¹ := by rw [h]
      _ = (z * d⁻¹) * x := by group
  have hdY : d ∈ pCoreOf 2 HU ⊔ Subgroup.centralizer (conjJoin H K : Set G) := by
    have h1 : d = (z * d⁻¹)⁻¹ * z := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hzc))
      (Subgroup.mem_sup_left hzQ)
  have hdR0 : d ∈ pCoreOf 2 HU ⊓ conjJoin H K := ⟨hYQ ⟨hdD, hdY⟩, hdD⟩
  have hnot : ∀ L : Subgroup G, IsComponentIn L H → L ≤ conjJoin H K →
      ¬ pCoreOf 2 HU ⊓ conjJoin H K ≤ Subgroup.centralizer (L : Set G) := by
    intro L hL hLD hcent
    have hdL : d ∈ Subgroup.centralizer (L : Set G) := hcent hdR0
    refine false_of_centralizes (hcl L hL).2.2.1 (Unc25G2.isComponentIn_ne_bot hL) (fun x hx => ?_)
    have h1 : z⁻¹ * x * z = d⁻¹ * x * d := hdact x (hLD hx)
    have h2 : d * x = x * d := (Subgroup.mem_centralizer_iff.mp hdL x hx).symm
    have h3 : d⁻¹ * x * d = x := by
      calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
        _ = d⁻¹ * (d * x) := by rw [h2]
        _ = x := by group
    rw [h3] at h1
    calc z * x = z * (z⁻¹ * x * z) := by rw [h1]
      _ = x * z := by group
  have hN0rad : pCoreOf 2 (conjJoin H K ⊓
      Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) =
      pCoreOf 2 HU ⊓ conjJoin H K := by
    apply le_antisymm
    · have hPN0 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (conjJoin H K ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G))
      have hHUN0 : HU ≤ Subgroup.normalizer ((conjJoin H K ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) :
            Subgroup G) : Set G) :=
        CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf HU _ _ hHUD
          (hHUR0.trans Subgroup.le_normalizer)
      have hHUP := hHUN0.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _)
      have hPQ := hbang _ (hPN0.trans (inf_le_left.trans hDH))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) hHUP
      exact le_inf hPQ (hPN0.trans inf_le_left)
    · exact le_pCoreOf_of_normal_pGroup (le_inf inf_le_right Subgroup.le_normalizer) inf_le_right
        hR02
  by_cases hM : conjJoin H K ⊓
      Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) ≤ M
  ·
    exfalso
    have hR0M : pCoreOf 2 HU ⊓ conjJoin H K ≤ M :=
      (inf_le_left.trans (hQU.trans hUS)).trans ht.le_M
    have hrad : pCoreOf 2 ((M ⊓ conjJoin H K) ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) =
        pCoreOf 2 HU ⊓ conjJoin H K := by
      have heq : (M ⊓ conjJoin H K) ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) =
          conjJoin H K ⊓
            Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) := by
        ext x
        constructor
        · rintro ⟨⟨_, hxD⟩, hxN⟩
          exact ⟨hxD, hxN⟩
        · rintro ⟨hxD, hxN⟩
          exact ⟨⟨hM ⟨hxD, hxN⟩, hxD⟩, hxN⟩
      rw [heq]
      exact hN0rad
    have hle : radicalOf M H K ≤ pCoreOf 2 HU ⊓ conjJoin H K :=
      pCoreOf_le_of_radical (le_inf hR0M inf_le_right) hR02 hrad
    exact hI K hK (hHUR0.trans (hF2 G T M H S z hs ht K hK (hBe K hK) (hcl K hK) _ inf_le_right
      hR02 hle))
  ·
    have hUU1 : U ≤ S ⊓ Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) :=
      le_inf hUS (hmaxP.1.1.2.1.trans hHUR0)
    have hU1_2 : IsPGroup 2 ↥(S ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) :=
      ht.sylow.isPGroup.to_le inf_le_left
    have hconf := hmaxP.1.1.1.of_le hU1_2 hUU1
    have hSD : S ≤ Subgroup.normalizer (conjJoin H K : Set G) := ht.le_H.trans hHD
    have hDSnorm : conjJoin H K ⊔ S ≤ Subgroup.normalizer (conjJoin H K : Set G) :=
      sup_le Subgroup.le_normalizer hSD
    have hN0H1 : conjJoin H K ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) ≤
        (conjJoin H K ⊔ S) ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) :=
      inf_le_inf_right _ le_sup_left
    have hH1N0 : (conjJoin H K ⊔ S) ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((conjJoin H K ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G) :
            Subgroup G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
        (inf_le_left.trans hDSnorm) (inf_le_right.trans Subgroup.le_normalizer)
    have hcharN0 := hF1 G T M H S z hs ht K hK (hBe K hK) (hcl K hK) _ inf_le_right hR02 hnot
      hN0rad
    have hcharH1 := charTwo_of_normal_of_quotient hN0H1 hH1N0 hcharN0 (fun x hx => by
      obtain ⟨j, hj⟩ := exists_pow_mem_of_mem_sup ht.sylow.isPGroup hSD hx.1
      exact ⟨j, hj, Subgroup.pow_mem _ hx.2 _⟩)
    have hR0ne : pCoreOf 2 HU ⊓ conjJoin H K ≠ ⊥ := by
      intro hbot
      refine hnot K hK (le_conjJoin_self H K) ?_
      rw [hbot]
      exact bot_le
    have hcore : pCoreOf 2 ((conjJoin H K ⊔ S) ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) ≠ ⊥ := by
      intro hbot
      have h : pCoreOf 2 HU ⊓ conjJoin H K ≤ pCoreOf 2 ((conjJoin H K ⊔ S) ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) :=
        le_pCoreOf_of_normal_pGroup
          (le_inf (inf_le_right.trans le_sup_left) Subgroup.le_normalizer) inf_le_right hR02
      rw [hbot] at h
      exact hR0ne (le_bot_iff.mp h)
    have hpair : IsWitnessPair M (S ⊓
        Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G))
        ((conjJoin H K ⊔ S) ⊓
          Subgroup.normalizer ((pCoreOf 2 HU ⊓ conjJoin H K : Subgroup G) : Set G)) :=
      ⟨hconf, inf_le_inf_right _ le_sup_right, hcore, hcharH1, fun h => hM (hN0H1.trans h)⟩
    exact ⟨K, _, _, hK, hpair, inf_le_left.trans (sup_le hDS le_sup_right),
      fun hU V hV => (hmaxU hU V hV).trans (Subgroup.card_le_of_le hUU1)⟩

end CFSG.QuasithinUnique.Fin253
