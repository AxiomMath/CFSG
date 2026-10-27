module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open CFSG.AGLEmbedding
  CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def layerPreimage (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ((rankThreeLayer (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p))).comap
    (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype

@[expose] def GL83LayerLemma (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        layerPreimage p (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M

theorem normalizer_zpowers_ne_top (hS : D1Global G) {z : G} (hz1 : z ≠ 1) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≠ ⊤ := by
  intro htop
  have hn : (zpowers z).Normal := normalizer_eq_top_iff.1 htop
  have := hS.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers z) with h | h
  · exact hz1 (zpowers_eq_bot.1 h)
  · obtain ⟨a, b, hab⟩ := hS.nonab
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (h ▸ mem_top a)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (h ▸ mem_top b)
    exact hab ((Commute.zpow_zpow_self z i j).eq)

theorem le_of_layer_le_of_not_isPConstrained (hS : D1Global G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) (hHtop : H ≠ ⊤) {z : G} (hzH : z ∈ H)
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) (hzn : (zpowers (⟨z, hzH⟩ : H)).Normal)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained p H) (hEM : layerPreimage p H ≤ M) : H ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  have hcon' : ¬ HasPrimeConstraint (G := H) p := fun h =>
    hcon (isPConstrained_of_hasPrimeConstraint h)
  obtain ⟨K, hKc, -, -, hKp, -, -⟩ :=
    isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H hHtop p hprime hcon'
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hEbn : (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  have hdvd : p ∣ Nat.card (rankThreeLayer (⊤ : Subgroup (H ⧸ O))) :=
    hKp.trans (Subgroup.card_dvd_of_le (le_sSup hKc))
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvd
  set E : Subgroup G := layerPreimage p H with hE
  have hEH : E ≤ H := map_subtype_le _
  have hHE : H ≤ normalizer (E : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hSE : (P : Subgroup G) ⊓ E ≠ ⊥ := by
    intro hbot
    apply hinf
    rw [eq_bot_iff]
    rintro t ⟨htP, htE⟩
    have htP' : (t : G) ∈ (P : Subgroup G) := by
      rw [Sylow.coe_subtype] at htP
      exact htP
    have : (t : G) ∈ (P : Subgroup G) ⊓ E := ⟨htP', t, htE, rfl⟩
    rw [hbot, mem_bot] at this
    exact mem_bot.2 (Subtype.ext this)
  have hzE : z ∈ E := hext.mem_of_inf_ne_bot hprime hodd hPD (hPH.trans hHE) hSE hzD hz1 hzc hzp
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hzbE : π zH ∈ rankThreeLayer (⊤ : Subgroup (H ⧸ O)) := by
    obtain ⟨h, hh, hhz⟩ := hzE
    have : h = zH := Subtype.ext hhz
    rw [this] at hh
    exact hh
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzHord : orderOf zH = p := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hzbord : orderOf (π zH) = p := orderOf_mk_of_coprime hprime O hO hzHord
  have hzb1 : π zH ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzbord
    exact hprime.one_lt.ne hzbord
  have hzbp : (π zH) ^ p = 1 := by
    have := pow_orderOf_eq_one (π zH)
    rwa [hzbord] at this
  have hzbn : (zpowers (π zH)).Normal := by
    rw [← MonoidHom.map_zpowers]
    exact hzn.map π (QuotientGroup.mk'_surjective O)
  set Pbar : Sylow p (H ⧸ O) :=
    (P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective O) with hPbardef
  have hPbar : (Pbar : Subgroup (H ⧸ O)) = ((P : Subgroup G).subgroupOf H).map π := by
    rw [hPbardef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrankY : 2 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ E) := by
    have h1 := two_le_pRank_inf_layer hodd Pbar hzbE hzbn hzb1 hzbp
    have h2 : (Pbar : Subgroup (H ⧸ O)) ⊓ rankThreeLayer (⊤ : Subgroup (H ⧸ O)) =
        (((P : Subgroup G).subgroupOf H) ⊓
          (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map π := by
      rw [hPbar]
      ext x
      constructor
      · rintro ⟨⟨t, htP, rfl⟩, hxL⟩
        exact ⟨t, ⟨htP, hxL⟩, rfl⟩
      · rintro ⟨t, ⟨htP, htL⟩, rfl⟩
        exact ⟨⟨t, htP, rfl⟩, htL⟩
    rw [h2, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      Subgroup.map_inf _ _ H.subtype H.subtype_injective, map_subgroupOf_eq_of_le hPH] at h1
    exact h1
  exact hext.le_of_normal_of_two_le_pRank hprime hPD hPH hEH hHE hEM hrankY

theorem normalizer_zpowers_le_of_layerLemma (hS : D1Global G) (h23 : GL83LayerLemma G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained p
      (normalizer ((zpowers z : Subgroup G) : Set G))) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≤ M := by
  have hzH : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := le_normalizer (mem_zpowers z)
  exact le_of_layer_le_of_not_isPConstrained hS hp hext hPD
    (le_normalizer_zpowers_of_le_centralizer hzc) (normalizer_zpowers_ne_top hS hz1) hzH hzD hz1
    hzc hzp (normal_zpowers_subtype_mk z hzH) hcon
    (h23 p hp P M D hext hPD z hzD hz1 hzc hzp)

end CFSG.LocalAnalysis.RankFourTheoremC
