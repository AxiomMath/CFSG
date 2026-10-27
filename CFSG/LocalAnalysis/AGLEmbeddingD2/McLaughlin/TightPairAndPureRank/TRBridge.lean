module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement
open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

@[expose] def rhoX (M X₀ : Subgroup G) (h : X₀ ≤ M) : ↥X₀ →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion h)

omit [Finite G] in
theorem rhoX_ker_le {M X₀ T : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀) (hQT : pCoreOf 2 M ≤ T) :
    (rhoX M X₀ hXM).ker ≤ gnC (T.subgroupOf X₀) := by
  intro x hx
  apply pCoreOf_subgroupOf_le_gnC hXM hTX hQT
  rw [MonoidHom.mem_ker] at hx
  refine Subgroup.mem_subgroupOf.mpr ?_
  exact (mk_eq_one_iff_coe_mem_pCoreOf (⟨(x : G), hXM x.2⟩ : ↥M)).mp hx

omit [Finite G] in
theorem map_subgroupOf_rhoX {M X₀ L : Subgroup G} (hXM : X₀ ≤ M) (hLX : L ≤ X₀) :
    (L.subgroupOf X₀).map (rhoX M X₀ hXM) = barM M L := by
  unfold rhoX barM
  rw [← Subgroup.map_map]
  congr 1
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx)
  · intro hm
    exact ⟨⟨(m : G), hLX (Subgroup.mem_subgroupOf.mp hm)⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hm), rfl⟩

omit [Finite G] in
theorem perfect_subgroupOf {X₀ L : Subgroup G} (hLX : L ≤ X₀) (hp : ⁅L, L⁆ = L) :
    ⁅L.subgroupOf X₀, L.subgroupOf X₀⁆ = L.subgroupOf X₀ := by
  apply Subgroup.map_injective X₀.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLX, hp]

theorem blockStar_facts {M S X₀ T L : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hQT : pCoreOf 2 M ≤ T) (hL : IsWeakSBlock M S L) (hLX : L ≤ X₀)
    (hmove : ¬ L.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) :
    Open.IsQuasisimple ↥(gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)) ∧
      Nat.card (Subgroup.center ↥(gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))) ∣
        Nat.card (Subgroup.center ↥(barM M L)) ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
        ↥(gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)) ⧸
          Subgroup.center ↥(gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))) ∧
      (¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) →
        (3 ∣ Nat.card (barM M L) ↔ 3 ∣ Nat.card (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))) ∧
          Open.pRank 3 (barM M L) = Open.pRank 3 (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))) := by
  have hq : Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have e := map_subgroupOf_rhoX hXM hLX
  have hqB : Open.IsQuasisimple ↥((L.subgroupOf X₀).map (rhoX M X₀ hXM)) := by rw [e]; exact hq
  obtain ⟨φ, hφs, hφk⟩ := block_image (gnC (T.subgroupOf X₀)) (rhoX M X₀ hXM)
    (rhoX_ker_le hXM hTX hQT) hmove hqB
  obtain ⟨h1, h2, h3, h4⟩ := central_quotient_facts hqB φ hφs hφk
  rw [← e]
  refine ⟨h1, h2, h3, fun hZ => ?_⟩
  obtain ⟨h5, h6⟩ := h4 hZ
  refine ⟨h5, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup ((L.subgroupOf X₀).map (rhoX M X₀ hXM)),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))]
  exact h6

theorem blockStar_subnormal {M S X₀ T L : Subgroup G} (hXM : X₀ ≤ M) (hL : IsWeakSBlock M S L)
    (hLX : L ≤ X₀) :
    IsSubnormal (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)) ⊤ := by
  have h1 : IsSubnormal L X₀ := by
    have := isSubnormal_inf' hL.subnormal X₀
    rwa [inf_eq_left.mpr hLX, inf_eq_right.mpr hXM] at this
  have h2 : IsSubnormal (L.subgroupOf X₀) ⊤ :=
    (CFSG.Adapters.isSubnormal_top_iff _).mpr (isSubnormal_subgroupOf' h1)
  have h3 := cfsg_isSubnormal_map (QuotientGroup.mk' (gnC (T.subgroupOf X₀))) h2
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3

theorem blockStar_isComponent {M S X₀ T L : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hQT : pCoreOf 2 M ≤ T) (hL : IsWeakSBlock M S L) (hLX : L ≤ X₀)
    (hmove : ¬ L.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) :
    IsComponentOf (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)) ⊤ :=
  ⟨le_top, blockStar_subnormal hXM hL hLX, (blockStar_facts hXM hTX hQT hL hLX hmove).1⟩

theorem blockStar_ne {M S X₀ T L₁ L₂ : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hQT : pCoreOf 2 M ≤ T) (h₁ : IsWeakSBlock M S L₁) (h₂ : IsWeakSBlock M S L₂)
    (hne : barM M L₁ ≠ barM M L₂) (hL₁X : L₁ ≤ X₀) (hL₂X : L₂ ≤ X₀)
    (hmove₁ : ¬ L₁.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) :
    gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀) ≠ gnImg (T.subgroupOf X₀) (L₂.subgroupOf X₀) := by
  intro heq
  have hc : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
  have hcomm : ∀ a ∈ L₁.subgroupOf X₀, ∀ b ∈ L₂.subgroupOf X₀,
      QuotientGroup.mk' (gnC (T.subgroupOf X₀)) (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a ha b hb
    have hρ : rhoX M X₀ hXM (a * b * a⁻¹ * b⁻¹) = 1 := by
      have h1 : rhoX M X₀ hXM a ∈ barM M L₁ := by
        rw [← map_subgroupOf_rhoX hXM hL₁X]; exact ⟨a, ha, rfl⟩
      have h2 : rhoX M X₀ hXM b ∈ barM M L₂ := by
        rw [← map_subgroupOf_rhoX hXM hL₂X]; exact ⟨b, hb, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc h1) _ h2
      have hcm : rhoX M X₀ hXM a * rhoX M X₀ hXM b = rhoX M X₀ hXM b * rhoX M X₀ hXM a :=
        this.symm
      have h3 := (commutatorElement_eq_one_iff_mul_comm).mpr hcm
      simpa [commutatorElement_def, map_mul, map_inv] using h3
    exact (QuotientGroup.eq_one_iff _).mpr (rhoX_ker_le hXM hTX hQT hρ)
  have hbot : gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀) = ⊥ := by
    have hper := perfect_subgroupOf hL₁X h₁.perfect
    have hbot' : ⁅gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀),
        gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := hx
      rw [heq] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have h3 := hcomm a ha b hb
      have h4 : ⁅(QuotientGroup.mk' (gnC (T.subgroupOf X₀))) a,
          (QuotientGroup.mk' (gnC (T.subgroupOf X₀))) b⁆ = 1 := by
        simpa [commutatorElement_def, map_mul, map_inv] using h3
      exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm
    have hp' : ⁅gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀),
        gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀)⁆ =
        gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀) := by
      unfold gnImg
      rw [← Subgroup.map_commutator, hper]
    rwa [hp'] at hbot'
  apply hmove₁
  intro l hl
  have : QuotientGroup.mk' (gnC (T.subgroupOf X₀)) l ∈
      gnImg (T.subgroupOf X₀) (L₁.subgroupOf X₀) := ⟨l, hl, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff l).mp this

theorem blockStar_sylow {M S X₀ T L : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hL : IsWeakSBlock M S L) (hLX : L ≤ X₀) (hT2 : IsPGroup 2 T)
    (hSyl : IsSylowTwoOf T X₀) :
    IsSylowTwoOf (gnImg (T.subgroupOf X₀) (T.subgroupOf X₀) ⊓
      gnImg (T.subgroupOf X₀) (L.subgroupOf X₀))
      (gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)) := by
  have hTh2 : IsPGroup 2 ↥(T.subgroupOf X₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hS : IsSylowTwoOf (gnImg (T.subgroupOf X₀) (T.subgroupOf X₀)) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hTh2.of_surjective ((QuotientGroup.mk' (gnC (T.subgroupOf X₀))).subgroupMap _)
        (MonoidHom.subgroupMap_surjective _ _)
    · show ¬ 2 ∣ (gnImg (T.subgroupOf X₀) (T.subgroupOf X₀)).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro hd
      exact hSyl.2.2 (hd.trans (Subgroup.index_map_dvd (T.subgroupOf X₀) (QuotientGroup.mk'_surjective _)))
  have hsub : ((gnImg (T.subgroupOf X₀) (L.subgroupOf X₀)).subgroupOf ⊤).IsSubnormal :=
    isSubnormal_subgroupOf' (blockStar_subnormal (T := T) hXM hL hLX)
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS le_top hsub

omit [Finite G] in
theorem IsLThreeTwo.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsLThreeTwo Y) : IsLThreeTwo Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

omit [Finite G] in
theorem IsUThreeThree.of_mulEquiv' {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsUThreeThree Y) : IsUThreeThree Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

omit [Finite G] in
theorem IsDoublingList.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsDoublingList Y) : IsDoublingList Y' := by
  rcases h with h | hf | h
  · exact Or.inl (IsLThreeTwo.of_mulEquiv e h)
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (IsUThreeThree.of_mulEquiv' e h))

omit [Finite G] in
theorem IsClassicalTwoOrG2.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsClassicalTwoOrG2 Y) : IsClassicalTwoOrG2 Y' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

theorem doubling_of_trX (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverDoubling)
    (hK : KFactStrongThreeSolv) {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) (hXb : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    {L₁ L₂ T : Subgroup G} (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT : IsSylowTwoOf T (H ⊓ M)) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hQT : pCoreOf 2 M ≤ T) (hSyl : IsSylowTwoOf T (trX M L₁ L₂ T))
    (hmove₁ : ¬ L₁.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)))
    (hmove₂ : ¬ L₂.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)))
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (hZ₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₂)))
    (hcl₁ : IsClassicalTwoOrG2 (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)))
    (hcl₂ : IsClassicalTwoOrG2 (↥(barM M L₂) ⧸ Subgroup.center ↥(barM M L₂)))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂) :
    IsDoublingList (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) ∧
      IsDoublingList (↥(barM M L₂) ⧸ Subgroup.center ↥(barM M L₂)) := by
  have hpr := hctx.pair
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hN := normalizes_trJ h₁ h₂ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hXM : trX M L₁ L₂ T ≤ M := trX_le h₁.le h₂.le hTM
  have hTX : T ≤ trX M L₁ L₂ T := le_trX_right
  have hL₁X : L₁ ≤ trX M L₁ L₂ T := le_trJ_left.trans le_trX_left
  have hL₂X : L₂ ≤ trX M L₁ L₂ T := le_trJ_right.trans le_trX_left
  have hGNS := gnSetting_trX hXb hpr.maxTwoLocal_M hpr.isKGroup.1 hpr.charTwo.1 h₁ h₂ hT2 hN hTM hSyl
  have hC := not_three_dvd_gnC h₁ h₂ hne hk2 hT2 hTH hTM hQT hZ₁ hZ₂ hmove₁ hmove₂
  have hD := gnBound_of_pair hctx hK hT2 hTX hXM hNT
  have hc₁ := blockStar_isComponent hXM hTX hQT h₁ hL₁X hmove₁
  have hc₂ := blockStar_isComponent hXM hTX hQT h₂ hL₂X hmove₂
  have hne' := blockStar_ne hXM hTX hQT h₁ h₂ hne hL₁X hL₂X hmove₁
  obtain ⟨-, hd₁, ⟨e₁⟩, hf₁⟩ := blockStar_facts hXM hTX hQT h₁ hL₁X hmove₁
  obtain ⟨-, hd₂, ⟨e₂⟩, hf₂⟩ := blockStar_facts hXM hTX hQT h₂ hL₂X hmove₂
  obtain ⟨hdv₁, hrk₁⟩ := hf₁ hZ₁
  obtain ⟨hdv₂, hrk₂⟩ := hf₂ hZ₂
  have hr₁ : Open.pRank 3 (barM M L₁) = Open.pRank 3 L₁ :=
    pRank_barM_eq Nat.prime_three (by norm_num) M L₁ h₁.le
  have hr₂ : Open.pRank 3 (barM M L₂) = Open.pRank 3 L₂ :=
    pRank_barM_eq Nat.prime_three (by norm_num) M L₂ h₂.le
  have hZs₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(gnImg (T.subgroupOf (trX M L₁ L₂ T))
      (L₁.subgroupOf (trX M L₁ L₂ T)))) := fun h => hZ₁ (h.trans hd₁)
  have hZs₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(gnImg (T.subgroupOf (trX M L₁ L₂ T))
      (L₂.subgroupOf (trX M L₁ L₂ T)))) := fun h => hZ₂ (h.trans hd₂)
  have key := isDoublingList_of_gn_two hGN hCov hGNS hC hD hc₁ hc₂ hne'
    (IsClassicalTwoOrG2.of_mulEquiv e₁ hcl₁) (IsClassicalTwoOrG2.of_mulEquiv e₂ hcl₂)
    (blockStar_sylow hXM hTX h₁ hL₁X hT2 hSyl) (blockStar_sylow hXM hTX h₂ hL₂X hT2 hSyl)
    hZs₁ hZs₂ (hdv₁.mp h3₁) (hdv₂.mp h3₂) (by omega)
  exact ⟨IsDoublingList.of_mulEquiv e₁.symm key.1, IsDoublingList.of_mulEquiv e₂.symm key.2⟩

end CFSG.AGLEmbeddingD2.McLaughlin
