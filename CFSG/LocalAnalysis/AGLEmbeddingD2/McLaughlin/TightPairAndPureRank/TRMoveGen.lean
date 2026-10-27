module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRMove

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem exists_perfect_of_le_map {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {N : Subgroup X} {L' : Subgroup Y} (hL' : L' ≤ N.map f) (hperf : ⁅L', L'⁆ = L')
    (h3 : 3 ∣ Nat.card L') :
    ∃ D : Subgroup X, D ≤ N ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  obtain ⟨n, hn⟩ := CFSG.AGLEmbeddingD2.exists_iterCommutator_perfect N
  refine ⟨CFSG.AGLEmbeddingD2.iterCommutator N n, CFSG.AGLEmbeddingD2.iterCommutator_le N n,
    hn, ?_⟩
  have h1 : L' ≤ (CFSG.AGLEmbeddingD2.iterCommutator N n).map f := by
    rw [CFSG.AGLEmbeddingD2.iterCommutator_map]
    exact CFSG.AGLEmbeddingD2.le_iterCommutator_of_commutator_eq hperf hL' n
  exact h3.trans ((Subgroup.card_dvd_of_le h1).trans (Subgroup.card_map_dvd _ _))

@[expose] def RankImageOne : Prop :=
  ∀ {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B) (N : Subgroup A),
    Open.pRank 3 N ≤ 1 → Open.pRank 3 (N.map f) ≤ 1

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_of_barM {M L : Subgroup G} (hLM : L ≤ M) (h : 3 ∣ Nat.card (barM M L)) :
    3 ∣ Nat.card L := by
  refine h.trans ?_
  unfold barM
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  exact Subgroup.card_map_dvd _ _

theorem false_of_block_le_gnC (hGN : GlaubermanNilesInput)
    (hH29 : RankImageOne)
    {M S X₀ T La Lb : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀) (hQT : pCoreOf 2 M ≤ T)
    (hGNS : GNSetting ↥X₀ (T.subgroupOf X₀)) (hD : GNBound (T.subgroupOf X₀))
    (ha : IsWeakSBlock M S La) (hb : IsWeakSBlock M S Lb) (hne : barM M La ≠ barM M Lb)
    (haX : La ≤ X₀) (hbX : Lb ≤ X₀)
    (hZa : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M La)))
    (hZb : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M Lb)))
    (h3a : 3 ∣ Nat.card (barM M La)) (h3b : 3 ∣ Nat.card (barM M Lb))
    (hrank : 2 < Open.pRank 3 La + Open.pRank 3 Lb)
    (hla : La.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀))
    (hmoveb : ¬ Lb.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set T' := T.subgroupOf X₀ with hT'
  set C := gnC T' with hC
  have hT'ne : T' ≠ ⊥ := by
    intro hT
    apply hmoveb
    have := hGNS.subsingleton_of_eq_bot hT
    intro x _
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  obtain ⟨T₁, T₂, hpair, -, hthree, -⟩ := hGN ↥X₀ T' hGNS hT'ne
  have hT₁ : T₁ ≤ T' := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T')
  have hCT₁ : C ≤ Subgroup.centralizer (T₁ : Set ↥X₀) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htV : t ∈ gnV T' := Subgroup.subset_normalClosure (hpair.le_center ht)
    exact Subgroup.mem_centralizer_iff.mp hc t htV
  set N₁ : Subgroup ↥X₀ := Subgroup.normalizer (T₁ : Set ↥X₀) with hN₁
  have hCN : C ≤ N₁ := hCT₁.trans (Subgroup.centralizer_le_normalizer _)
  have hLaN : La.subgroupOf X₀ ≤ N₁ := hla.trans hCN
  have hperfa : ⁅La.subgroupOf X₀, La.subgroupOf X₀⁆ = La.subgroupOf X₀ :=
    perfect_subgroupOf haX ha.perfect
  have h3a' : 3 ∣ Nat.card (La.subgroupOf X₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe haX).toEquiv]
    exact three_dvd_card_of_barM ha.le h3a
  obtain ⟨-, hp₁⟩ := hD T₁ hpair.ne_bot₁ hT₁ hpair.char₁
  have hp₁' : 2 ≤ Open.pRank 3 N₁ → ∀ J : Subgroup ↥X₀, J ≤ N₁ → ⁅J, J⁆ = J →
      ¬ 3 ∣ Nat.card J := hp₁
  have hN1 : Open.pRank 3 N₁ ≤ 1 := by
    by_contra h
    push Not at h
    exact hp₁' (by omega) _ hLaN hperfa h3a'
  set ρ := rhoX M X₀ hXM with hρ
  have hker3 : ¬ 3 ∣ Nat.card ρ.ker := by
    have hker2 : IsPGroup 2 ρ.ker := by
      have hle : ρ.ker.map X₀.subtype ≤ pCoreOf 2 M := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : ρ x = 1 := hx
        exact (mk_eq_one_iff_coe_mem_pCoreOf (⟨(x : G), hXM x.2⟩ : ↥M)).mp hx'
      have hpg : IsPGroup 2 ↥(ρ.ker.map X₀.subtype) := (pCoreOf_isPGroup 2 M).to_le hle
      exact hpg.of_equiv (Subgroup.equivMapOfInjective ρ.ker X₀.subtype
        X₀.subtype_injective).symm
    exact not_three_dvd_card_of_isPGroup_two hker2
  have hrk : Open.pRank 3 (N₁.map ρ) ≤ Open.pRank 3 N₁ :=
    CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd h3 ρ hker3 N₁
  have hAeq : barM M La = (La.subgroupOf X₀).map ρ := (map_subgroupOf_rhoX hXM haX).symm
  have hBeq : barM M Lb = (Lb.subgroupOf X₀).map ρ := (map_subgroupOf_rhoX hXM hbX).symm
  have hcomp0 : ⁅barM M La, barM M Lb⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ ha.component hb.component hne
  have hbC : barM M Lb ≤ Subgroup.centralizer (barM M La : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mp ?_
    rw [Subgroup.commutator_comm]
    exact hcomp0
  have hpartner : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), D ≤ barM M Lb → D ≤ N₁.map ρ →
      3 ∣ Nat.card D → False := by
    intro D hDb hDN h3D
    have hAN : barM M La ≤ N₁.map ρ := hAeq ▸ Subgroup.map_mono hLaN
    have hc : ∀ x ∈ barM M La, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hbC (hDb hy)) x hx
    have hi : Nat.Coprime 3 (Nat.card (barM M La ⊓ D : Subgroup _)) := by
      rw [Nat.Prime.coprime_iff_not_dvd h3]
      intro hdvd
      apply hZa
      rw [← card_inf_centralizer_eq_card_center]
      refine hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hu.1, ?_⟩)
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => hc g hg u hu.2
    have := rank_ge_two_of_partner hAN hDN h3a h3D hc hi
    omega
  by_cases hA : Lb.subgroupOf X₀ ≤ N₁
  · exact hpartner (barM M Lb) le_rfl (hBeq ▸ Subgroup.map_mono hA) h3b
  have hcomp := blockStar_isComponent hXM hTX hQT hb hbX hmoveb
  obtain ⟨-, -, -, hf⟩ := blockStar_facts hXM hTX hQT hb hbX hmoveb
  obtain ⟨hdv, hrkb⟩ := hf hZb
  by_cases hBc : gnImg T' (Lb.subgroupOf X₀) ≤ gnImg T' (Subgroup.normalizer (T₂ : Set ↥X₀))
  ·
    obtain ⟨-, hp₂⟩ := hD T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂
    obtain ⟨Dp, hDN, hDp, hD3⟩ := exists_perfect_of_le_map (QuotientGroup.mk' C) hBc
      (perfect_of_isComponentOf hcomp) (hdv.mp h3b)
    have hN2 : Open.pRank 3 (Subgroup.normalizer (T₂ : Set ↥X₀)) ≤ 1 := by
      by_contra h
      push Not at h
      exact hp₂ (by omega) Dp hDN hDp hD3
    have h1 := hH29 (QuotientGroup.mk' C) _ hN2
    have h2 : Open.pRank 3 (gnImg T' (Lb.subgroupOf X₀)) ≤
        Open.pRank 3 ((Subgroup.normalizer (T₂ : Set ↥X₀)).map (QuotientGroup.mk' C)) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hBc
    have hrkb' : Open.pRank 3 (barM M Lb) = Open.pRank 3 (gnImg T' (Lb.subgroupOf X₀)) := hrkb
    have h4 : Open.pRank 3 (barM M Lb) = Open.pRank 3 Lb :=
      pRank_barM_eq h3 (by norm_num) M Lb hb.le
    have h5 : Open.pRank 3 (La.subgroupOf X₀) = Open.pRank 3 La := by
      rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3 X₀.subtype
        X₀.subtype_injective, Subgroup.map_subgroupOf_eq_of_le haX]
    have h6 : Open.pRank 3 (La.subgroupOf X₀) ≤ Open.pRank 3 N₁ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hLaN
    omega
  ·
    have hY : GNYComponent T' T₁ T₂ (gnImg T' (Lb.subgroupOf X₀)) := by
      refine ⟨hcomp, fun hle => hA ?_, hBc⟩
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hle ⟨x, hx, rfl⟩
      have hc : y⁻¹ * x ∈ C := by
        rw [← QuotientGroup.eq]
        exact hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact N₁.mul_mem ((Subgroup.centralizer_le_normalizer _) hy) (hCN hc)
    obtain ⟨h1, -⟩ := hthree _ hY
    obtain ⟨D, hD, hd3⟩ := exists_three_dvd_of_not_pElement_le h1
    obtain ⟨a, ha3⟩ := exists_prime_orderOf_dvd_card' 3 hd3
    have haD := hD a.2
    obtain ⟨n, hnN, hna⟩ := haD.1
    obtain ⟨l, hl, hla'⟩ := haD.2
    have hlN : l ∈ N₁ := by
      have hc : n⁻¹ * l ∈ C := by
        rw [← QuotientGroup.eq]
        exact hna.trans hla'.symm
      have : l = n * (n⁻¹ * l) := by group
      rw [this]
      exact N₁.mul_mem hnN (hCN hc)
    have hρl : ρ l ∈ barM M Lb := by
      rw [hBeq]
      exact ⟨l, hl, rfl⟩
    have hmk : orderOf (QuotientGroup.mk' C l) = 3 := by
      rw [hla']
      exact (Subgroup.orderOf_coe a).trans ha3
    have h3o : 3 ∣ orderOf (ρ l) := by
      by_contra hnd
      have hcop : Nat.Coprime 3 (orderOf (ρ l)) := (Nat.Prime.coprime_iff_not_dvd h3).mpr hnd
      have hker : l ^ orderOf (ρ l) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
      have hkC := rhoX_ker_le hXM hTX hQT hker
      have h1' : (QuotientGroup.mk' C l) ^ orderOf (ρ l) = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hkC
      have := orderOf_dvd_of_pow_eq_one h1'
      rw [hmk] at this
      exact (Nat.Prime.coprime_iff_not_dvd h3).mp hcop this
    refine hpartner (Subgroup.zpowers (ρ l)) ((Subgroup.zpowers_le).mpr hρl) ?_ ?_
    · exact (Subgroup.zpowers_le).mpr ⟨l, hlN, rfl⟩
    · rw [Nat.card_zpowers]
      exact h3o

theorem trBlocksMove_general (hGN : GlaubermanNilesInput) (hH29 : RankImageOne)
    (hK : KFactStrongThreeSolv) {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) (hXb : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    {L₁ L₂ T : Subgroup G} (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT : IsSylowTwoOf T (H ⊓ M)) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hQT : pCoreOf 2 M ≤ T) (hSyl : IsSylowTwoOf T (trX M L₁ L₂ T))
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (hZ₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₂)))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂) :
    ¬ L₁.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)) ∧
      ¬ L₂.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)) := by
  have hpr := hctx.pair
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hN := normalizes_trJ h₁ h₂ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hXM : trX M L₁ L₂ T ≤ M := trX_le h₁.le h₂.le hTM
  have hTX : T ≤ trX M L₁ L₂ T := le_trX_right
  have hL₁X : L₁ ≤ trX M L₁ L₂ T := le_trJ_left.trans le_trX_left
  have hL₂X : L₂ ≤ trX M L₁ L₂ T := le_trJ_right.trans le_trX_left
  have hGNS := gnSetting_trX hXb hpr.maxTwoLocal_M hpr.isKGroup.1 hpr.charTwo.1 h₁ h₂ hT2 hN hTM
    hSyl
  have hD := gnBound_of_pair hctx hK hT2 hTX hXM hNT
  have hT0 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hpr.maxTwoLocal_M.1
    exact eq_bot_iff.mpr (hQT.trans h.le)
  have hc : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
  constructor
  · intro h1
    by_cases h2 : L₂.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T))
    · exact false_of_both_le_gnC hTX hT2 hT0 hD hL₁X h₁.le h₂.le h₁.perfect hc hZ₁ h3₁ h3₂ hL₂X
        h1 h2
    · exact false_of_block_le_gnC hGN hH29 hXM hTX hQT hGNS hD h₁ h₂ hne hL₁X hL₂X hZ₁ hZ₂ h3₁
        h3₂ hrank h1 h2
  · intro h2
    by_cases h1 : L₁.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T))
    · exact false_of_both_le_gnC hTX hT2 hT0 hD hL₁X h₁.le h₂.le h₁.perfect hc hZ₁ h3₁ h3₂ hL₂X
        h1 h2
    · exact false_of_block_le_gnC hGN hH29 hXM hTX hQT hGNS hD h₂ h₁ hne.symm hL₂X hL₁X hZ₂ hZ₁
        h3₂ h3₁ (by omega) h2 h1

end Core

end CFSG.AGLEmbeddingD2.McLaughlin
