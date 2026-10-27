module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerGeneration
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.hasPrimeConstraint_centralizer_of_five_le (hS : Setting G)
    (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : (P : Subgroup G) ≤ normalizer (D : Set G)) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) :
    HasPrimeConstraint (G := centralizer ({z} : Set G)) p := by
  by_contra hcon
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨hM, -, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    hext.center_le_centralizer hprime hodd hD hzZ
  have hzD : z ∈ D := map_subtype_le _ hzZ
  have hzp : z ^ p = 1 := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z hzD
  set H := centralizer ({z} : Set G) with hHdef
  have hPH : (P : Subgroup G) ≤ H := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hHtop : H ≠ ⊤ := fun htop => hS.normalizer_zpowers_ne_top hz1
    (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers z))
  have hzH : z ∈ H := mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨K, hKc, -, -, hKp, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H hHtop p
      hprime hcon
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hEbn : (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  have hdvd : p ∣ Nat.card (rankThreeLayer (⊤ : Subgroup (H ⧸ O))) :=
    hKp.trans (Subgroup.card_dvd_of_le (le_sSup hKc))
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvd
  set E : Subgroup G := ((rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map H.subtype with hE
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
  have hzE : z ∈ E :=
    hext.mem_of_inf_ne_bot_of_not_isMulCommutative hprime hodd hD (hPH.trans hHE) hSE hzD hzc
      hzp
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hzbE : π zH ∈ rankThreeLayer (⊤ : Subgroup (H ⧸ O)) := by
    obtain ⟨h, hh, hhz⟩ := hzE
    have : h = zH := Subtype.ext hhz
    rw [this] at hh
    exact hh
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzHord : orderOf zH = p := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hzbord : orderOf (π zH) = p :=
    CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO hzHord
  have hzb1 : π zH ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzbord
    exact hprime.one_lt.ne hzbord
  have hzn : (zpowers zH).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcomm : g * zH = zH * g :=
      Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
    have hconj : g * zH * g⁻¹ = zH := by rw [hcomm, mul_inv_cancel_right]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [← conj_zpow, hconj]
    exact hn
  have hzbn : (zpowers (π zH)).Normal := by
    rw [← MonoidHom.map_zpowers]
    exact hzn.map π (QuotientGroup.mk'_surjective O)
  set Pbar : Sylow p (H ⧸ O) :=
    (P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective O) with hPbardef
  have hPbar : (Pbar : Subgroup (H ⧸ O)) = ((P : Subgroup G).subgroupOf H).map π := by
    rw [hPbardef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrankPbar : CFSG.Open.pRank p (Pbar : Subgroup (H ⧸ O)) = 3 := by
    rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      map_subgroupOf_eq_of_le hPH]
    exact hP3
  have hrankTop : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) = 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hprime Pbar).symm.trans
      hrankPbar
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O) :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hcore : primeComplementCore (G := H ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  exact hzb1 (hKF1.eq_one_of_mem_layer hprime hp5 hHtop hcat hcore hrankTop.le hzbE hzbn)

@[expose] def CentralizerGenerationThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, p = 3 → ∀ (P : Sylow p G) (M D : Subgroup G),
    ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ¬ CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := centralizer ({z} : Set G)) p →
        ∀ E : Subgroup G, E ≤ (P : Subgroup G) → IsElemAbelian p E → Nat.card E = p ^ 3 →
          centralizer ({z} : Set G) ≤
            CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({z} : Set G)) ⊔
              (⨆ (y : G) (_ : y ∈ E) (_ : y ∉ zpowers z),
                centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G))

theorem centralizerGeneration_of_three (hS : Setting G) (hKF1 : KF1At G)
    (h : CentralizerGenerationThree G) : CentralizerGeneration G := by
  intro p hp P M D hext hPD z hzZ hz1 hcon
  by_cases hp3 : p = 3
  · exact h p hp hp3 P M D hext hPD z hzZ hz1 hcon
  · exfalso
    have hprime := sigmaA_prime p hp
    have hodd := sigmaA_odd p hp
    have hp5 : 5 ≤ p := by
      have h2 := hprime.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hprime (by decide)
      omega
    exact hcon (hext.hasPrimeConstraint_centralizer_of_five_le hS hKF1 hp hp5 hPD hzZ hz1)

end CFSG.LocalAnalysis.RankThreeTheoremC
