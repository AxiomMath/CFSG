module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInner
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Walter.Cited.CentralSplit
import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedA7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint
open scoped commutatorElement

section Constructors

variable {G : Type} [Group G] {M S L : Subgroup G} {z : G}

theorem listed_of_bender (h : fusionIsBenderGroup ↥L) : IsListedComponent M S L z := Or.inl h

theorem listed_of_rank_two (h : IsRankTwoCharTwoType L) : IsListedComponent M S L z :=
  Or.inr (Or.inl h)

theorem listed_of_alt_seven
    (h : (Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ IsThreeFoldCoverAlt L 7) ∧
      IsPartitionStabilizerImage L (L ⊓ M)) : IsListedComponent M S L z :=
  Or.inr (Or.inr (Or.inl h))

theorem listed_of_centralizer
    (h : (StatedClassicalModel ↥L .PSL 3 3 1 ∨
        Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
      ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G)) :
    IsListedComponent M S L z :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem listed_of_psl_two
    (h : (∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∧
      L ⊓ M = S ⊓ L) : IsListedComponent M S L z :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem listed_of_mathieu
    (h : (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
        IsAltOverElemAbelian (L ⊓ M) 4 6) ∨
      (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) ∧
        IsAltOverElemAbelian (L ⊓ M) 4 7)) : IsListedComponent M S L z :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem listed_of_l42
    (h : StatedClassicalModel ↥L .PSL 4 2 1 ∧ (∃ s ∈ S, InducesOuter s L) ∧
      ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G)) :
    IsListedComponent M S L z :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end Constructors

section Small

theorem fusionIsBenderGroup_of_psl_two_five {X : Type} [Group X]
    (hX : StatedClassicalModel X .PSL 2 5 1) : fusionIsBenderGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by rw [hK]; norm_num))
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨e4⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  exact Or.inl ⟨2, le_rfl, ⟨(e'.trans e5).trans e4⟩⟩

theorem statedClassicalModel_psl_three_two_of_psl_two_seven {X : Type} [Group X]
    (hX : StatedClassicalModel X .PSL 2 7 1) : StatedClassicalModel X .PSL 3 2 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hX

variable {G : Type} [Group G]

noncomputable def mulEquivQuotientCenter {L : Subgroup G} (h : Subgroup.center ↥L = ⊥) :
    ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

noncomputable def mulEquivQuotientPCore {L : Subgroup G} (h : CFSG.pCore 2 ↥L = ⊥) :
    ↥L ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

theorem pCore_two_le_center {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hs : IsSimpleGroup (K ⧸ Subgroup.center K)) : CFSG.pCore 2 K ≤ Subgroup.center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hmap : ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · intro n hn
    have h1 : QuotientGroup.mk' (Subgroup.center K) n ∈
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).1 h1
  · exfalso
    have h2 : IsPGroup 2 ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))) :=
      (CFSG.pCore_isPGroup (p := 2) (G := K)).map _
    rw [h] at h2
    have h3 : IsPGroup 2 (K ⧸ Subgroup.center K) := h2.of_equiv Subgroup.topEquiv
    have h4 : Group.IsNilpotent (K ⧸ Subgroup.center K) := h3.isNilpotent
    have := hs.toNontrivial
    exact Group.IsPerfect.not_isNilpotent (K ⧸ Subgroup.center K) h4

theorem openQuasisimple {K : Type*} [Group K] (h : CFSG.IsQuasisimple K) :
    CFSG.Open.IsQuasisimple K := ⟨h.1.commutator_eq_top, h.2.1⟩

theorem three_le_of_isFermatOrMersennePrime {p : ℕ} (hp : Ch1.IsFermatOrMersennePrime p) :
    3 ≤ p := by
  obtain ⟨hpp, hp'⟩ := hp
  have h2 := hpp.two_le
  by_contra hlt
  have hp2 : p = 2 := by omega
  rcases hp' with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have h1 : 1 < 2 ^ 2 ^ k := Nat.one_lt_two_pow (by positivity)
    omega
  · have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

end Small

structure Ctx {G : Type} [Group G] (M S L : Subgroup G) (z : G) : Prop where
  quasi : CFSG.IsQuasisimple ↥L
  isP : IsPGroup 2 S
  le_M : S ≤ M
  z_central : z ∈ Subgroup.centralizer (S : Set G)
  z_sq : z ^ 2 = 1
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ M
  comm : ⁅L, Subgroup.zpowers z⁆ = L
  not_le : ¬ L ≤ M
  sylow_L : IsSylowTwoOf (S ⊓ L) L
  dich : ∀ K : Subgroup G, S ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ M ∨ HasChi0Block K
  normal : IsNormalListedType L → S ≤ Subgroup.normalizer (L : Set G) ∧ CharTwo (L ⊓ M)
  m22_center : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M22) →
    Subgroup.center ↥L = ⊥

section Cases

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G} {z : G}

omit [Finite G] in
theorem isNormalListedType_of_isParabolicPairType {R : Subgroup G}
    (h : IsParabolicPairType L R) : IsNormalListedType L := by
  rcases h with h | h | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem false_of_parabolicPairs (hpairs : L239ParabolicPairs) (c : Ctx M S L z)
    (htype : IsParabolicPairType L S) : False := by
  obtain ⟨hSN, -⟩ := c.normal (isNormalListedType_of_isParabolicPairType htype)
  obtain ⟨K₁, K₂, -, -, -, -, hjoin, hN₁, hN₂, hc₁, hc₂, hb₁, hb₂⟩ :=
    hpairs G L S c.quasi htype c.isP hSN c.sylow_L
  have h1 : K₁ ≤ M := (c.dich K₁ hN₁ hc₁).resolve_right hb₁
  have h2 : K₂ ≤ M := (c.dich K₂ hN₂ hc₂).resolve_right hb₂
  exact c.not_le (by rw [← hjoin]; exact sup_le h1 h2)

omit [Finite G] in
theorem inf_eq_of_parabolic {K : Subgroup G} (c : Ctx M S L z) (hKL : K ≤ L)
    (hKN : S ≤ Subgroup.normalizer (K : Set G)) (hKc : CharTwo K) (hKb : ¬ HasChi0Block K)
    (hmax : ∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L) : L ⊓ M = K := by
  have hKM : K ≤ M := (c.dich K hKN hKc).resolve_right hKb
  rcases hmax (L ⊓ M) (le_inf hKL hKM) inf_le_left with h | h
  · exact h
  · exact absurd (inf_eq_left.mp h) c.not_le

theorem listed_of_caseA (hpairs : L239ParabolicPairs) (hl42 : L239L42Overgroups)
    (c : Ctx M S L z) (hA : Lemma115CaseA L z) : IsListedComponent M S L z := by
  obtain ⟨-, hlie, zL, hzL, hact⟩ := hA
  have hp : IsProjectionOn z zL L := ⟨hzL, hact⟩
  rcases hlie with ((⟨f, h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8⟩ | htits) | ⟨n, hn, hmodel⟩) |
      hA6 | hU33
  · exact listed_of_bender (K1.fusionIsBenderGroup_of_stated_psl_two h1.1 h1.2)
  · exact listed_of_rank_two (Or.inl ⟨f, h2.1, h2.2⟩)
  · exact listed_of_bender (K1.fusionIsBenderGroup_of_stated_psu_three h3.1 h3.2)
  · exact listed_of_rank_two (Or.inr (Or.inl ⟨f, h4.1, h4.2⟩))
  · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inl ⟨f, Or.inl h5⟩))).elim
  · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inl ⟨f, Or.inr (Or.inl h6)⟩))).elim
  · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inl ⟨f, Or.inr (Or.inr h7)⟩))).elim
  · exact listed_of_bender (K1.fusionIsBenderGroup_of_suzukiModel h8.2.2)
  · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inr (Or.inl htits)))).elim
  · rcases hn with rfl | rfl
    · by_cases hout : ∃ s ∈ S, InducesOuter s L
      · have hnorm : IsNormalListedType L :=
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel))))
        exact listed_of_l42 ⟨hmodel, hout, zL, hp,
          inf_eq_centralizer_of_l42 hl42 hmodel c.isP (c.normal hnorm).1 c.sylow_L hout c.le_M
            c.z_central hp c.comm c.not_le c.cz_le⟩
      · exact (false_of_parabolicPairs hpairs c (Or.inr (Or.inr (Or.inr ⟨hmodel, hout⟩)))).elim
    · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inr (Or.inr (Or.inl hmodel))))).elim
  · exact listed_of_rank_two (Or.inr (Or.inr (Or.inl hA6)))
  · exact (false_of_parabolicPairs hpairs c (Or.inl (Or.inr (Or.inr (Or.inr hU33))))).elim

theorem listed_of_caseB (hpairs : L239ParabolicPairs) (c : Ctx M S L z)
    (hB : Lemma115CaseB L z) : IsListedComponent M S L z := by
  obtain ⟨-, -, hmodel, -⟩ := hB
  rcases hmodel with h | h
  · exact listed_of_rank_two (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact (false_of_parabolicPairs hpairs c (Or.inr (Or.inl h))).elim

omit [Finite G] in
theorem listed_of_caseC (c : Ctx M S L z) (hC : Lemma115CaseC L z) :
    IsListedComponent M S L z := by
  obtain ⟨φ, _, hZ, -, -⟩ := hC
  rcases hZ with h | h
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    exact listed_of_rank_two (Or.inr (Or.inr (Or.inl ⟨(mulEquivQuotientCenter hbot).trans φ⟩)))
  · exact listed_of_rank_two
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨openQuasisimple c.quasi, h, ⟨φ⟩⟩))))

omit [Finite G] in
theorem listed_of_caseD (ha7 : L239A7Overgroups) (c : Ctx M S L z) (hD : Lemma115CaseD L z) :
    IsListedComponent M S L z := by
  obtain ⟨φ, σ, hZ, hσ, hact⟩ := hD
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rcases hZ with h | h <;> rw [h] <;> decide
  have hn : IsNormalListedType L :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ⟩)))))
  obtain ⟨-, hchar⟩ := c.normal hn
  refine listed_of_alt_seven ⟨?_, isPartitionStabilizerImage_of_a7 ha7 c.quasi φ σ hodd hσ hact
    c.z_sq c.not_le c.cz_le hchar⟩
  rcases hZ with h | h
  · exact Or.inl ⟨(mulEquivQuotientCenter (Subgroup.eq_bot_of_card_eq _ h)).trans φ⟩
  · exact Or.inr ⟨openQuasisimple c.quasi, h, ⟨φ⟩⟩

theorem listed_of_caseE
    (hl33 : L239L33Overgroups) (hl2p : L239Sylow2PSL2) (c : Ctx M S L z)
    (hE : Lemma115CaseE L z) : IsListedComponent M S L z := by
  obtain ⟨hmodel | ⟨p, hp, hpL⟩, zL, hzL, hact⟩ := hE
  · have hn : IsNormalListedType L :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmodel)))))
    obtain ⟨-, hchar⟩ := c.normal hn
    exact listed_of_centralizer ⟨Or.inl hmodel, zL, ⟨hzL, hact⟩,
      inf_eq_centralizer_of_l33 hl33 c.quasi hmodel ⟨hzL, hact⟩ c.z_sq c.comm c.not_le c.cz_le
        hchar⟩
  · by_cases hp7 : 7 < p
    · exact listed_of_psl_two ⟨⟨p, hp, hpL⟩,
        inf_eq_sylow_of_psl2 hl2p hp hp7 hpL c.sylow_L c.le_M c.not_le⟩
    · have hp7' : p ≤ 7 := not_lt.mp hp7
      have hp3 : 3 ≤ p := three_le_of_isFermatOrMersennePrime hp
      have hpp : p.Prime := hp.1
      interval_cases p
      · obtain ⟨-, -, -, -, h3⟩ := hpL.1
        exact absurd (by norm_num) h3
      · exact absurd hpp (by norm_num)
      · exact listed_of_bender (fusionIsBenderGroup_of_psl_two_five hpL)
      · exact absurd hpp (by norm_num)
      · exact listed_of_rank_two
          (Or.inl ⟨1, le_rfl, statedClassicalModel_psl_three_two_of_psl_two_seven hpL⟩)

theorem listed_of_caseF (hpairs : L239ParabolicPairs) (hm11 : L239M11Overgroups)
    (hm22 : L239M22Parabolic) (hm23 : L239M23Parabolic) (hcov : L239Covers) (c : Ctx M S L z)
    (hF : Lemma115CaseF L z) : IsListedComponent M S L z := by
  obtain ⟨⟨s, hs, ⟨e⟩⟩, l, hl, hact, -, -⟩ := hF
  have hproj : IsProjectionOn z l L := ⟨hl, hact⟩
  have hperf : Group.IsPerfect ↥L := c.quasi.1
  have hpc : Subgroup.center ↥L = ⊥ → CFSG.pCore 2 ↥L = ⊥ := fun hZ =>
    le_bot_iff.mp ((pCore_two_le_center c.quasi.2.1).trans hZ.le)
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  ·
    subst hs
    have hZ := hcov G L c.quasi (Or.inl ⟨e⟩)
    have hmodel : Nonempty (↥L ≃* NativeSporadic.Carrier .M11) :=
      ⟨(mulEquivQuotientPCore (hpc hZ)).trans e⟩
    exact listed_of_centralizer ⟨Or.inr hmodel, l, hproj,
      inf_eq_centralizer_of_m11 hm11 hmodel hZ hproj c.z_sq c.comm c.not_le c.cz_le⟩
  · exact (false_of_parabolicPairs hpairs c
      (Or.inr (Or.inr (Or.inl ⟨s, by simp [IsBadSporadicName, hs], ⟨e⟩⟩)))).elim
  ·
    subst hs
    have hZ := c.m22_center ⟨e⟩
    have hmodel : Nonempty (↥L ≃* NativeSporadic.Carrier .M22) :=
      ⟨(mulEquivQuotientPCore (hpc hZ)).trans e⟩
    have hn : IsNormalListedType L := Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨e⟩))))
    obtain ⟨hSN, -⟩ := c.normal hn
    obtain ⟨K, hKL, hKN, hKc, hKb, hKalt, hmax⟩ := hm22 G L S hmodel c.isP hSN c.sylow_L
    refine listed_of_mathieu (Or.inl ⟨hmodel, ?_⟩)
    rw [inf_eq_of_parabolic c hKL hKN hKc hKb hmax]
    exact hKalt
  ·
    subst hs
    have hZ := hcov G L c.quasi (Or.inr ⟨e⟩)
    have hmodel : Nonempty (↥L ≃* NativeSporadic.Carrier .M23) :=
      ⟨(mulEquivQuotientPCore (hpc hZ)).trans e⟩
    have hn : IsNormalListedType L := Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨e⟩))))
    obtain ⟨hSN, -⟩ := c.normal hn
    obtain ⟨K, hKL, hKN, hKc, hKb, hKalt, hmax⟩ := hm23 G L S hmodel c.isP hSN c.sylow_L
    refine listed_of_mathieu (Or.inr ⟨hmodel, ?_⟩)
    rw [inf_eq_of_parabolic c hKL hKN hKc hKb hmax]
    exact hKalt
  all_goals
    exact (false_of_parabolicPairs hpairs c
      (Or.inr (Or.inr (Or.inl ⟨s, by simp [IsBadSporadicName, hs], ⟨e⟩⟩)))).elim

end Cases

end CFSG.QuasithinUnique.Vol2Native.L239

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.Quasithin

theorem lemma2_3_9_7_listed_component
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hl42 : L239.L239L42Overgroups)
    (ha7 : L239.L239A7Overgroups) (hl33 : L239.L239L33Overgroups)
    (hm11 : L239.L239M11Overgroups) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) (hl2p : L239.L239Sylow2PSL2) (hcov : L239.L239Covers)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} (h : UniqueSetting G T M)
    {H S T' : Subgroup G} {z : G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hT' : IsSylowTwoOf T' M) (hST' : S ≤ T') (hz : z ∈ T' ⊓ Subgroup.centralizer (T' : Set G))
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) {L : Subgroup G} (hL : IsComponentIn L H)
    (h22 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
      Subgroup.center ↥L = ⊥) :
    IsListedComponent M S L z := by
  have hSH : IsSylowTwoOf S H := hH.isSylowTwoOf_of_inf h hS
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  have hzS : z ∈ S ⊓ Subgroup.centralizer (S : Set G) := hcentre hz
  have hyp := hH.lemma115Hyp h hS hzS hz1 hz2 ⟨T', hT', hz⟩
  obtain ⟨-, hcomm, hLM, -⟩ := hyp.component_action hL
  have hq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hctx : L239.Ctx M S L z :=
    { quasi := hq
      isP := hS.isPGroup
      le_M := hS.le.trans inf_le_right
      z_central := hzS.2
      z_sq := hz2
      cz_le := hyp.centralizer_z_le
      comm := hcomm
      not_le := hLM
      sylow_L := RankOneRecog.isSylowTwoOf_inf_of_subnormal hSH hL.1 hL.2.2
      dich := fun K hSK hK => L239.charTwo_le_or_hasChi0Block h238 h hH hS hSK hK
      m22_center := h22
      normal := fun htype => by
        have hn : (L.subgroupOf H).Normal := by
          rcases _root_.CFSG.QuasithinUnique.Vol2Native.lemma_1_2_1_three h.qtke.1 h37 h38 hH.isGamma.1
            (_root_.CFSG.QuasithinUnique.Vol2Native.mem_cComp_of_isComponentIn hL)
            with hn | ⟨-, hA⟩
          · exact hn
          · exact absurd hA (hnot G L hq htype)
        have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).mp hn
        refine ⟨hSH.le.trans hHL, ?_⟩
        refine CharTwo.of_normal (hH.charTwo_inf h hS) (inf_le_inf_right M hL.1) ?_
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right M hL.1)]
        intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hHL hx.1, Subgroup.le_normalizer hx.2⟩ }
  rcases hlist G h.simple h.nonabelian h.qtke H S M z hyp L hL with hA | hB | hC | hD | hE | hF
  · exact L239.listed_of_caseA hpairs hl42 hctx hA
  · exact L239.listed_of_caseB hpairs hctx hB
  · exact L239.listed_of_caseC hctx hC
  · exact L239.listed_of_caseD ha7 hctx hD
  · exact L239.listed_of_caseE hl33 hl2p hctx hE
  · exact L239.listed_of_caseF hpairs hm11 hm22 hm23 hcov hctx hF

end CFSG.QuasithinUnique.Vol2Native
