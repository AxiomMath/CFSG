module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSylow

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

section OneBlock

variable {W : Type*} [Group W]

theorem eq_one_of_three_pow_of_normal_one {L : Subgroup W} (hL : IsComponentOf L ⊤)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) {N : Subgroup W} (hN : N ≤ L)
    (hNn : ∀ x ∈ L, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN₁ : ¬ L ≤ N) {n : W} (hn : n ∈ N)
    (h3 : ∃ k : ℕ, n ^ 3 ^ k = 1) : n = 1 := by
  have hq : Open.IsQuasisimple ↥L := hL.2.2
  let N₁ : Subgroup ↥L := (N ⊓ L).subgroupOf L
  have hN₁n : N₁.Normal := ⟨fun x hx g => by
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, L.mul_mem (L.mul_mem g.2 x.2) (L.inv_mem g.2)⟩
    exact hNn g g.2 x (Subgroup.mem_subgroupOf.mp hx).1⟩
  have hle : N₁ ≤ Subgroup.center ↥L := by
    rcases CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.quasisimple_normal_le_center_or_eq_top'
      hq hN₁n with h | h
    · exact h
    · exfalso
      apply hN₁
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ N₁ := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
  have hnL : n ∈ L := hN hn
  have hcen : (⟨n, hnL⟩ : ↥L) ∈ Subgroup.center ↥L :=
    hle (Subgroup.mem_subgroupOf.mpr ⟨hn, hnL⟩)
  obtain ⟨k, hk⟩ := h3
  have hord1 : orderOf (⟨n, hnL⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
    Subgroup.orderOf_dvd_natCard _ hcen
  have hord2 : orderOf (⟨n, hnL⟩ : ↥L) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one
    (Subtype.ext (by simpa using hk))
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥L)) (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ).symm
  have h1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

end OneBlock

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_gnC_one {M H L T : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hT2 : IsPGroup 2 T) (hTH : T ≤ H) (hTM : T ≤ M) (hQT : pCoreOf 2 M ≤ T)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)))
    (hmove₁ : ¬ L.subgroupOf (trX M L L T) ≤ gnC (T.subgroupOf (trX M L L T))) :
    ¬ 3 ∣ Nat.card (gnC (T.subgroupOf (trX M L L T))) := by
  intro hdvd
  have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L ∨ barM M L' = barM M L := fun L' hL' => Or.inl (hk1 L' hL')
  have hN := normalizes_trJ h₁ h₁ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hXM : trX M L L T ≤ M := trX_le h₁.le h₁.le hTM
  set X₀ := trX M L L T with hX₀
  set J := trJ M L L with hJ
  set C := gnC (T.subgroupOf X₀) with hC
  have hker : (pCoreOf 2 M).subgroupOf X₀ ≤ C :=
    pCoreOf_subgroupOf_le_gnC hXM le_trX_right hQT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨c, hcC⟩, hc3⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hc3' : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one (⟨c, hcC⟩ : ↥C)
    rw [hc3] at this
    simpa using congrArg Subtype.val this
  have hcJ : ((c : ↥X₀) : G) ∈ J := mem_trJ_of_pow_three hT2 hN c.2 (by
    simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
  set Cg : Subgroup G := C.map X₀.subtype with hCg
  set N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M (Cg ⊓ J) with hNdef
  have hJM : J ≤ M := sup_le (sup_le h₁.le h₁.le) (pCoreOf_le 2 M)
  have hJX : J ≤ X₀ := le_trX_left
  have hbJ : barM M J = barM M L := by
    rw [hJ, trJ, barM_sup_eq (sup_le h₁.le h₁.le) (pCoreOf_le 2 M), barM_sup_eq h₁.le h₁.le,
      barM_pCoreOf_eq_bot, sup_bot_eq, sup_idem]
  have hNle : N ≤ barM M L := hbJ ▸ barM_mono inf_le_right
  have hNn : ∀ x ∈ barM M L, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    rw [← hbJ] at hx
    obtain ⟨m, hmJ, rfl⟩ := mem_barM_iff'.mp hx
    obtain ⟨mc, ⟨hmcC, hmcJ⟩, rfl⟩ := mem_barM_iff'.mp hn
    refine mem_barM_iff'.mpr ⟨m * mc * m⁻¹, ⟨?_, ?_⟩, by simp⟩
    · obtain ⟨cc, hcc, hccv⟩ := hmcC
      have hccv' : ((cc : ↥X₀) : G) = (mc : G) := hccv
      let mX : ↥X₀ := ⟨m, hJX hmJ⟩
      refine ⟨mX * cc * mX⁻¹, (inferInstance : C.Normal).conj_mem cc hcc mX, ?_⟩
      show ((mX * cc * mX⁻¹ : ↥X₀) : G) = (m : G) * (mc : G) * (m : G)⁻¹
      simp [mX, hccv']
    · exact J.mul_mem (J.mul_mem hmJ hmcJ) (J.inv_mem hmJ)
  have hnot : ¬ barM M L ≤ N := by
    intro hle
    apply hmove₁
    intro l hl
    have hlM : (l : G) ∈ M := hXM l.2
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
      mem_barM_iff'.mpr ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    obtain ⟨y, ⟨hyC, hyJ⟩, hy⟩ := mem_barM_iff'.mp (hle hmem)
    obtain ⟨cc, hcc, hccv⟩ := hyC
    have hccv' : ((cc : ↥X₀) : G) = (y : G) := hccv
    have hq : (y : ↥M)⁻¹ * ⟨l, hlM⟩ ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]
      exact hy
    have hz : (y : G)⁻¹ * (l : G) ∈ pCoreOf 2 M := by
      have h2 : (y : G)⁻¹ * (l : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype :=
        ⟨(y : ↥M)⁻¹ * ⟨l, hlM⟩, hq, rfl⟩
      assumption
    have hz' : cc⁻¹ * l ∈ (pCoreOf 2 M).subgroupOf X₀ := by
      rw [Subgroup.mem_subgroupOf]
      show ((cc : ↥X₀) : G)⁻¹ * (l : G) ∈ pCoreOf 2 M
      rw [hccv']
      exact hz
    have := C.mul_mem hcc (hker hz')
    simpa using this
  have hcN : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(c : G), hXM c.2⟩ ∈ N :=
    mem_barM_iff'.mpr ⟨⟨(c : G), hXM c.2⟩, ⟨⟨c, hcC, rfl⟩, hcJ⟩, rfl⟩
  have h1 := eq_one_of_three_pow_of_normal_one h₁.component hZ₁ hNle hNn hnot hcN ⟨1, by
      rw [pow_one, ← map_pow]
      have : ((⟨(c : G), hXM c.2⟩ : ↥M)) ^ 3 = 1 :=
        Subtype.ext (by simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
      rw [this, map_one]⟩
  have hcQ : (c : G) ∈ pCoreOf 2 M := (mk_eq_one_iff_coe_mem_pCoreOf ⟨(c : G), hXM c.2⟩).mp h1
  obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 M ⟨(c : G), hcQ⟩
  have ha' : (c : G) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hd1 : orderOf (c : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : ↥X₀ => (y : G)) hc3')
  have hd2 : orderOf (c : G) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)) hd1 hd2
  have hc1 : (c : G) = 1 := orderOf_eq_one_iff.mp this
  have hc1' : c = 1 := Subtype.ext hc1
  have hC1 : (⟨c, hcC⟩ : ↥C) = 1 := Subtype.ext hc1'
  rw [hC1, orderOf_one] at hc3
  exact absurd hc3 (by norm_num)

theorem isSylowTwoOf_trX_one {M S L T : Subgroup G} (h₁ : IsWeakSBlock M S L)
    (hT2 : IsPGroup 2 T)
    (hN : ∀ t ∈ T, ∀ j ∈ trJ M L L, t * j * t⁻¹ ∈ trJ M L L)
    (hQT : pCoreOf 2 M ≤ T) (hP₁ : IsSylowTwoOf (barM M (T ⊓ L)) (barM M L)) :
    IsSylowTwoOf T (trX M L L T) := by
  refine ⟨le_trX_right, hT2, ?_⟩
  have hle : T ≤ Subgroup.normalizer (trJ M L L : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hN t ht j hj, fun hj => ?_⟩
    have := hN t⁻¹ (T.inv_mem ht) _ hj
    simpa [mul_assoc] using this
  have hJM : trJ M L L ≤ M := sup_le (sup_le h₁.le h₁.le) (pCoreOf_le 2 M)
  set U₀ : Subgroup G := (T ⊓ L) ⊔ pCoreOf 2 M with hU₀
  have hU₀J : U₀ ≤ trJ M L L :=
    sup_le (inf_le_right.trans le_trJ_left) pCoreOf_le_trJ
  have hU₀T : U₀ ≤ T := sup_le inf_le_left hQT
  have hbU : barM M U₀ = barM M (T ⊓ L) := by
    rw [hU₀, barM_sup_eq (inf_le_right.trans h₁.le) (pCoreOf_le 2 M), barM_pCoreOf_eq_bot,
      sup_bot_eq]
  have hbJ : barM M (trJ M L L) = barM M L := by
    rw [trJ, barM_sup_eq (sup_le h₁.le h₁.le) (pCoreOf_le 2 M), barM_sup_eq h₁.le h₁.le,
      barM_pCoreOf_eq_bot, sup_bot_eq, sup_idem]
  have h1 : U₀.relIndex (trJ M L L) = (barM M (T ⊓ L)).relIndex (barM M L) := by
    rw [← hbU, ← hbJ, relIndex_barM_eq hU₀J hJM le_sup_right]
  have h4 : (trJ M L L ⊓ T).relIndex (trJ M L L) ∣ U₀.relIndex (trJ M L L) :=
    Subgroup.relIndex_dvd_of_le_left _ (le_inf hU₀J hU₀T)
  show ¬ 2 ∣ T.relIndex (trX M L L T)
  rw [trX, relIndex_sup_eq hle]
  intro hd
  exact hP₁.2.2 (hd.trans (h4.trans (dvd_of_eq h1)))

theorem false_of_le_gnC_one {X₀ T L : Subgroup G} (hTX : T ≤ X₀) (hT2 : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) (hD : GNBound (T.subgroupOf X₀)) (hLX : L ≤ X₀)
    (hp : ⁅L, L⁆ = L) (h3 : 3 ∣ Nat.card L) (hr : 2 ≤ Open.pRank 3 L)
    (hle : L.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) : False := by
  have hTh2 : IsPGroup 2 ↥(T.subgroupOf X₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hTh0 : T.subgroupOf X₀ ≠ ⊥ := by
    intro h
    apply hT0
    have := Subgroup.map_subgroupOf_eq_of_le hTX
    rw [h, Subgroup.map_bot] at this
    exact this.symm
  set Z : Subgroup ↥X₀ := Quasithin.omegaOneCenterOf (T.subgroupOf X₀) with hZ
  have hZb : Z ≠ ⊥ := QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hTh2 hTh0
  have hZT : Z ≤ T.subgroupOf X₀ := QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hZc : (Z.subgroupOf (T.subgroupOf X₀)).Characteristic :=
    QuasithinUnique.Setup.characteristic_omegaOneCenterOf _
  obtain ⟨hrk, hpf⟩ := hD Z hZb hZT hZc
  have hnorm : ∀ l ∈ gnC (T.subgroupOf X₀), l ∈ Subgroup.normalizer (Z : Set ↥X₀) := by
    intro l hl
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ gnV (T.subgroupOf X₀) := Subgroup.subset_normalClosure hz
    exact Subgroup.mem_centralizer_iff.mp hl z hzV
  have hsup : L.subgroupOf X₀ ≤ Subgroup.normalizer (Z : Set ↥X₀) := fun l hl => hnorm l (hle hl)
  have hrk2 : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Z : Set ↥X₀)) := by
    have h5 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hsup
    have h6 : Open.pRank 3 (L.subgroupOf X₀) = Open.pRank 3 L := by
      rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three X₀.subtype
        X₀.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hLX]
    omega
  have h3' : 3 ∣ Nat.card (L.subgroupOf X₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv]
    exact h3
  exact hpf hrk2 _ hsup (perfect_subgroupOf hLX hp) h3'

omit [Finite G] in
theorem IsOneImageList.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsOneImageList Y) : IsOneImageList Y' := by
  obtain ⟨d, hd, hf⟩ := h
  exact ⟨d, hd, hf.elim fun f => ⟨e.symm.trans f⟩⟩

omit [Finite G] in
theorem IsClassicalOverTwo.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsClassicalOverTwo Y) : IsClassicalOverTwo Y' := by
  obtain ⟨d, hd, hq, hf⟩ := h
  exact ⟨d, hd, hq, hf.elim fun f => ⟨e.symm.trans f⟩⟩

@[expose] def SmallRankAtlas : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨ IsUThreeThree X) →
      Open.pRank 3 (⊤ : Subgroup X) ≤ 2

theorem isClassicalOverTwo_of_nineThreeTwo (hLF : LargeFieldParabolic) (hSA : SmallRankAtlas)
    {M S L : Subgroup G} (hw : IsWeakSBlock M S L) (h2 : NineThreeTwo M S L)
    (hSyl : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) (hsolv : BlockPLThreeSolv M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hr : 3 ≤ Open.pRank 3 L) :
    IsClassicalOverTwo (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  have hrq := pRank_top_quot_center_eq hw.le hZ
  rcases h2.1 with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · have hlt := lieField_lt_four_of_nineThreeTwo hLF hw h2 hSyl hsolv d hd e
    exact ⟨d, hd, lieField_eq_two_of_lt_four d hd hlt, ⟨e⟩⟩
  · exfalso
    have h1 := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrq
    have h3 := pRank_three_alternating_le (N := n)
    omega
  · exfalso
    have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
    have h1 := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrq
    have h3 := hSA (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (by
      rcases hd with hd | hd
      · exact Or.inl ⟨d, hd, ⟨e⟩⟩
      · exact Or.inr ⟨d, hd, ⟨e⟩⟩)
    omega


theorem pairOneImageLieTR_of_cited (hD2 : D1NoXBlock)
    (hLF : LargeFieldParabolic) (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne)
    (hK : KFactStrongThreeSolv) (hSA : SmallRankAtlas) : PairOneImageLieTR := by
  intro G _ _ P M A H R hctx hev L hL hk1 h2 hr hZ
  have hpr := hctx.pair
  have hLF' := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF'
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L :=
    d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair hctx.strong
      hctx.perf L hL
  have hSylneg := (hpr.nineThree_not_one h85 hX hL).2 h2
  have hclass := isClassicalOverTwo_of_nineThreeTwo hLF hSA hL h2 hSylneg hsolv hZ hr
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  obtain ⟨T, hT2, hQT, hNT, hT⟩ := hctx.exists_twoGroup_of_evenIndex hev
  have hNH := hpr.normalizer_twoCore_H
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hT0 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hpr.maxTwoLocal_M.1
    exact eq_bot_iff.mpr (hQT.trans h.le)
  have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L ∨ barM M L' = barM M L := fun L' hL' => Or.inl (hk1 L' hL')
  have hN := normalizes_trJ hL hL hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hSylT := isSylowTwoOf_trX_one hL hT2 hN hQT
    (isSylowTwoOf_barM_inf_of_parabolic hL hT hNH h2)
  have hXM : trX M L L T ≤ M := trX_le hL.le hL.le hTM
  have hTX : T ≤ trX M L L T := le_trX_right
  have hLX : L ≤ trX M L L T := le_trJ_left.trans le_trX_left
  have hD := gnBound_of_pair hctx hK hT2 hTX hXM hNT
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨E0, hE0L, -, hE0c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
    have h1 : 3 ∣ Nat.card E0 := by
      rw [hE0c]
      exact dvd_pow_self 3 (by omega)
    exact h1.trans (Subgroup.card_dvd_of_le hE0L)
  have hmove : ¬ L.subgroupOf (trX M L L T) ≤ gnC (T.subgroupOf (trX M L L T)) := fun hle =>
    false_of_le_gnC_one hTX hT2 hT0 hD hLX hL.perfect h3L (by omega) hle
  have hGNS := gnSetting_trX hX hpr.maxTwoLocal_M hpr.isKGroup.1 hpr.charTwo.1 hL hL hT2 hN hTM
    hSylT
  have hC := not_three_dvd_gnC_one hL hk1 hT2 hTH hTM hQT hZ' hmove
  have hcomp := blockStar_isComponent hXM hTX hQT hL hLX hmove
  obtain ⟨-, -, ⟨e⟩, hf⟩ := blockStar_facts hXM hTX hQT hL hLX hmove
  obtain ⟨-, hrk⟩ := hf hZ'
  have hr' : Open.pRank 3 (barM M L) = Open.pRank 3 L :=
    pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le
  have key := isOneImageList_of_gn hGN hCov hGNS hC hD hcomp
    (IsClassicalOverTwo.of_mulEquiv e hclass) (by omega)
    (blockStar_sylow hXM hTX hL hLX hT2 hSylT)
  exact IsOneImageList.of_mulEquiv e.symm key

end CFSG.AGLEmbeddingD2.McLaughlin
