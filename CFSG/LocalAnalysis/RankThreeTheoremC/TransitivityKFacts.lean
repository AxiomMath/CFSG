module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SchurMultiplierRankFact : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) → p ∣ Nat.card (Subgroup.center L) →
      4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def KF1At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ H : Subgroup G, H ≠ ⊤ → ∀ (O : Subgroup H) [O.Normal]
    (K : Subgroup (H ⧸ O)), CFSG.Open.IsQuasisimple K →
      CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) → IsPGroup p (Subgroup.center K) →
      p ∣ Nat.card (Subgroup.center K) → 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)

@[expose] def IsNonabelianPlane (p : ℕ) {X : Type*} [Group X] [Finite X] (P D : Subgroup X) :
    Prop :=
  D ≤ P ∧ ¬ IsMulCommutative D ∧ (∀ x ∈ D, x ^ p = 1) ∧
    CFSG.Open.pRank p (D ⊔ (P ⊓ centralizer (D : Set X))) ≤ 2

@[expose] def ZLayerWeakCoreFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    primeComplementCore (G := X) 3 = ⊥ → ∀ (P : Sylow 3 X) (z : X),
      CFSG.Open.pRank 3 (P : Subgroup X) = 3 → orderOf z = 3 → (zpowers z).Normal →
      z ∈ centralizer ((P : Subgroup X) : Set X) → z ∈ rankThreeLayer (⊤ : Subgroup X) →
      IsCyclic (CFSG.pCore 3 X) →
      (∃ D : Subgroup X, (IsIsolatedPlane 3 (P : Subgroup X) D ∨
          IsNonabelianPlane 3 (P : Subgroup X) D) ∧ z ∈ D ∧
        ¬ (P : Subgroup X) ≤ normalizer (D : Set X)) →
      rankThreeLayer (⊤ : Subgroup X) ≤ rankThreeAschCore 2 3 (P : Subgroup X)

section Auxiliary

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.le_of_normal_of_two_le_pRank {p : ℕ} (hp : p.Prime) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {H E : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hEH : E ≤ H) (hHE : H ≤ normalizer (E : Set G)) (hEM : E ≤ M)
    (hrank : 2 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ E)) : H ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) H :=
    ⟨P.subtype hPH, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPH]⟩
  have hYsyl := hPsyl.inf_of_le_normalizer hEH hHE
  have hPY : (P : Subgroup G) ≤ normalizer (((P : Subgroup G) ⊓ E : Subgroup G) : Set G) :=
    le_trans (le_inf le_normalizer (hPH.trans hHE)) inf_normalizer_le_normalizer_inf
  have hN : normalizer (((P : Subgroup G) ⊓ E : Subgroup G) : Set G) ≤ M :=
    hext.normalizer_le_of_normal hPD inf_le_left hPY hrank
  exact (le_sup_normalizer_of_isSylowOf hHE hYsyl).trans (sup_le hEM hN)

theorem ExtremalObstruction.exists_plane_map {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O)) :
    (IsIsolatedPlane p (((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O))
        ((D.subgroupOf H).map (QuotientGroup.mk' O)) ∨
      IsNonabelianPlane p (((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O))
        ((D.subgroupOf H).map (QuotientGroup.mk' O))) ∧
    ¬ ((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O) ≤
      normalizer (((D.subgroupOf H).map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) :
        Set (H ⧸ O)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hDH : D ≤ H := hDP.trans hPH
  have hDHP : D.subgroupOf H ≤ (P : Subgroup G).subgroupOf H := fun x hx => hDP hx
  have hPp : IsPGroup p ((P : Subgroup G).subgroupOf H) := P.isPGroup'.comap_subtype
  have hDHp : IsPGroup p (D.subgroupOf H) := hPp.to_le hDHP
  have hrank : CFSG.Open.pRank p ((D.subgroupOf H).map (QuotientGroup.mk' O) ⊔
      (((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O) ⊓ centralizer
        (((D.subgroupOf H).map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)))) ≤ 2 := by
    refine (pRank_map_sup_inf_centralizer_le_pRank hp O hO hPp hDHP).trans ?_
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp H.subtype
      H.subtype_injective]
    refine le_trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp ?_)
      hext.product_rank_eq.le
    rw [Subgroup.map_sup]
    refine sup_le_sup (map_subgroupOf_eq_of_le hDH).le ?_
    refine le_inf ?_ ?_
    · exact (Subgroup.map_mono inf_le_left).trans (map_subgroupOf_eq_of_le hPH).le
    · refine (Subgroup.map_mono inf_le_right).trans ?_
      refine (CFSG.AGLEmbedding.map_subtype_centralizer_le _).trans ?_
      rw [map_subgroupOf_eq_of_le hDH]
  refine ⟨?_, ?_⟩
  · by_cases hDab : IsMulCommutative D
    · left
      obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hp hDab
      refine isIsolatedPlane_of_pRank_le_two hp (Subgroup.map_mono hDHP)
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
          (CFSG.AGLEmbedding.isElemAbelian_subgroupOf hDe H) _) ?_ hrank
      rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O hO hDHp,
        Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv, hDc]
    · right
      refine ⟨Subgroup.map_mono hDHP, ?_, ?_, hrank⟩
      · intro hc
        apply hDab
        rw [isMulCommutative_iff]
        intro a b
        have haH : (⟨a, hDH a.2⟩ : H) ∈ D.subgroupOf H := a.2
        have hbH : (⟨b, hDH b.2⟩ : H) ∈ D.subgroupOf H := b.2
        have hcomm := congrArg Subtype.val ((isMulCommutative_iff.mp hc)
          ⟨_, mem_map_of_mem (QuotientGroup.mk' O) haH⟩
          ⟨_, mem_map_of_mem (QuotientGroup.mk' O) hbH⟩)
        have hab := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp O hO hPp
          (mul_mem (hDHP haH) (hDHP hbH)) (mul_mem (hDHP hbH) (hDHP haH))
          (by rw [map_mul, map_mul]; exact hcomm)
        have hab' : (a : G) * b = b * a := congrArg Subtype.val hab
        exact Subtype.ext hab'
      · rintro _ ⟨d, hd, rfl⟩
        have hdp : (d : G) ^ p = 1 := (hext.pow_eq_one_and_commutator_mem hp hodd).1 d hd
        rw [← map_pow, show d ^ p = 1 from Subtype.ext hdp, map_one]
  · intro hle
    apply hPD
    have h1 := le_normalizer_of_map_le_normalizer_map hp O hO hPp hDHP hle
    intro g hg
    have hg' : (⟨g, hPH hg⟩ : H) ∈ normalizer ((D.subgroupOf H : Subgroup H) : Set H) :=
      h1 (show (⟨g, hPH hg⟩ : H) ∈ (P : Subgroup G).subgroupOf H from hg)
    have := Subgroup.le_normalizer_map H.subtype ⟨⟨g, hPH hg⟩, hg', rfl⟩
    rwa [map_subgroupOf_eq_of_le hDH] at this

theorem KF1At.eq_one_of_mem_layer {G : Type} [Group G] [Finite G] {p : ℕ} (hKF1 : KF1At G)
    (hp : p.Prime) (hp5 : 5 ≤ p) {H : Subgroup G} (hH : H ≠ ⊤) {O : Subgroup H} [O.Normal]
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O))
    (hcore : primeComplementCore (G := H ⧸ O) p = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) ≤ 3) {c : H ⧸ O}
    (hc : c ∈ rankThreeLayer (⊤ : Subgroup (H ⧸ O))) (hcn : (zpowers c).Normal) : c = 1 := by
  by_contra hc1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hKZ⟩ := exists_component_center_ne_bot_of_mem_layer hc hc1
    (fun e he => commute_of_mem_layer hcn he)
  have hpg : IsPGroup p (center K) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hp hcore hK
  have hdvd : p ∣ Nat.card (center K) := by
    have : Nontrivial (center K) := (nontrivial_iff_ne_bot _).2 hKZ
    obtain ⟨n, hn, hcard⟩ := hpg.nontrivial_iff_card.1 this
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hK.2.2
  have hcatK : CFSG.Open.IsCatalogGroup (K ⧸ center K) :=
    hcat K (center K) inferInstance hK.2.2.2 hnonab
  have h4 := hKF1 p hp hp5 H hH O K hK.2.2 hcatK hpg hdvd
  have hKX : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
  omega

theorem Setting.normalizer_zpowers_ne_top (hS : Setting G) {z : G} (hz1 : z ≠ 1) :
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

omit [Finite G] in
theorem normal_zpowers_subtype_mk (z : G)
    (hz : z ∈ normalizer ((zpowers z : Subgroup G) : Set G)) :
    (zpowers (⟨z, hz⟩ : normalizer ((zpowers z : Subgroup G) : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 g.2 z).1 (mem_zpowers z))
  have hg : g * ⟨z, hz⟩ * g⁻¹ = ⟨z, hz⟩ ^ m := Subtype.ext (by simpa using hm.symm)
  rw [← conj_zpow, hg, ← zpow_mul]
  exact mem_zpowers_iff.2 ⟨m * k, rfl⟩

theorem ExtremalObstruction.not_isPConstrained_cases (hS : Setting G)
    (hKF1 : KF1At G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hHtop : H ≠ ⊤) {z : G} (hzH : z ∈ H) (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hzn : (zpowers (⟨z, hzH⟩ : H)).Normal)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained p H) :
    (5 ≤ p → False) ∧ (ZLayerWeakCoreFact →
      IsCyclic (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype) → H ≤ M) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hM := hext.obstruction.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  have hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M := by
    have hcop : ¬ p ∣ Nat.card ((CFSG.pPrimeCore p H).map H.subtype) := by
      rw [card_map_of_injective H.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hprime).1 CFSG.pPrimeCore_coprime_card
    exact le_of_elemAbelian_normalizes hS hp hM hAP hA hAc hcop
      ((hAP.trans hPH).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype H _))
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) := primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    mem_subgroupOf.2 ⟨o.2, hKM ⟨o, ho, rfl⟩⟩
  have hcon' : ¬ HasPrimeConstraint (G := H) p := fun h =>
    hcon (isPConstrained_of_hasPrimeConstraint h)
  obtain ⟨K, hKc, -, -, hKp, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H hHtop p
      hprime hcon'
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hEbn : (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  have hdvd : p ∣ Nat.card (rankThreeLayer (⊤ : Subgroup (H ⧸ O))) :=
    hKp.trans (Subgroup.card_dvd_of_le (le_sSup hKc))
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvd
  set E : Subgroup G := ((rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map H.subtype with hE
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
  have hzbord : orderOf (π zH) = p :=
    CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO hzHord
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
  have hrankPbar : CFSG.Open.pRank p (Pbar : Subgroup (H ⧸ O)) = 3 := by
    rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      map_subgroupOf_eq_of_le hPH]
    exact hP3
  have hzbc : π zH ∈ centralizer ((Pbar : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    rw [hPbar, mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have : t * zH = zH * t := Subtype.ext (mem_centralizer_iff.1 hzc (t : G) ht)
    show π t * π zH = π zH * π t
    rw [← map_mul, ← map_mul, this]
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O) :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hcore : primeComplementCore (G := H ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  have hrankTop : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) = 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hprime Pbar).symm.trans
      hrankPbar
  have h5 : 5 ≤ p → False := fun hp5 =>
    hzb1 (hKF1.eq_one_of_mem_layer hprime hp5 hHtop hcat hcore hrankTop.le hzbE hzbn)
  refine ⟨h5, fun hKF3 hRc => ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    have hcyc : IsCyclic (CFSG.pCore 3 (H ⧸ O)) := isCyclic_pCore_quotient (P.subtype hPH) hRc
    obtain ⟨hD, hDn⟩ := hext.exists_plane_map hprime hodd hPD hPH O hO
    rw [← hPbar] at hD hDn
    have hKF := hKF3 (H ⧸ O) hcat hcore Pbar (π zH) hrankPbar hzbord hzbn hzbc hzbE hcyc
      ⟨_, hD, mem_map_of_mem π (show zH ∈ D.subgroupOf H from hzD), hDn⟩
    have hW := CFSG.AGLEmbedding.weakCore_map_le_map_inf_of_coprime hprime P hM.2 le_rfl hPH O
      hO hOM
    rw [← hPbar] at hW
    have hEbX : rankThreeLayer (⊤ : Subgroup (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map π :=
      hKF.trans hW
    have hEM : E ≤ M := by
      rintro _ ⟨h, hh, rfl⟩
      have h1 : h ∈ (((H ⊓ M).subgroupOf H).map π).comap π := hEbX hh
      rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.2 hOM] at h1
      exact (mem_subgroupOf.1 h1).2
    have hrankY : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ E) := by
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
  · have hp5 : 5 ≤ p := by
      have h2 := hprime.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hprime (by decide)
      omega
    exact (h5 hp5).elim

theorem ExtremalObstruction.isPConstrained_of_five_le (hS : Setting G)
    (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hHtop : H ≠ ⊤) {z : G} (hzH : z ∈ H) (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hzn : (zpowers (⟨z, hzH⟩ : H)).Normal) : CFSG.ABGLocalTools.IsPConstrained p H := by
  by_contra hcon
  exact (hext.not_isPConstrained_cases hS hKF1 hp hPD hPH hHtop hzH hzD hz1 hzc hzp hzn hcon).1 hp5

end Auxiliary

end CFSG.LocalAnalysis.RankThreeTheoremC
