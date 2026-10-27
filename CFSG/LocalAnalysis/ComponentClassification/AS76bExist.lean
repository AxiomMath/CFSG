module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoGeneral
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups

theorem isSolvable_outer_of_fusionIsBenderGroup {X : Type} [Group X] (h : fusionIsBenderGroup X) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv _ e
  · have hc : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
      rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, Nat.mul_comm]
    let eC : CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) (GaloisField 2 (2 * f)) (2 ^ f)) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
      MulEquiv.refl _
    have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f :=
      ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible f hf, GaloisField 2 (2 * f),
        inferInstance, inferInstance, hc,
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm).trans eC⟩⟩
    exact
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_rank_one_classical_model_schreier
        hmodel).2
  · have hmodel : CFSG.Blueprint.SuzukiModel X 2 (2 * a + 1) :=
      ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
        GaloisField.card 2 (2 * a + 1) (by omega),
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative a).symm).trans
          (MulEquiv.subgroupCongr
            (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1)))).symm⟩⟩
    exact (CFSG.LocalAnalysis.ComponentInitial.Suzuki_model_Schreier X 2 (2 * a + 1) hmodel).2

theorem isSolvable_normalizer_sylow_two {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) :
    Group.IsSolvable ↥(normalizer ((S : Subgroup X) : Set X)) := by
  set N := normalizer ((S : Subgroup X) : Set X) with hN
  have hSN : (S : Subgroup X) ≤ N := le_normalizer
  have hTn : ((S : Subgroup X).subgroupOf N).Normal := normal_in_normalizer
  have hS : Group.IsSolvable ↥(S : Subgroup X) := by
    have := S.isPGroup'.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥((S : Subgroup X).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hSN).toMonoidHom)
      (subgroupOfEquivOfLe hSN).injective
  have hodd : Odd (Nat.card (↥N ⧸ (S : Subgroup X).subgroupOf N)) := by
    change Odd ((S : Subgroup X).relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => S.not_dvd_index ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (relIndex_dvd_index_of_le hSN)
  have hQ : Group.IsSolvable (↥N ⧸ (S : Subgroup X).subgroupOf N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup X).subgroupOf N).subtype
    (QuotientGroup.mk' ((S : Subgroup X).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem bender_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (h : fusionIsBenderGroup X)
    (e : X ≃* Y) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem exists_fusionBenderBorel {X : Type} [Group X] [Finite X] (h : fusionIsBenderGroup X) :
    ∃ q k : ℕ, fusionBenderBorel X q k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
      f hf).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
      a ha).map_mulEquiv e.symm⟩

theorem isSolvable_centralizer_of_fusionBenderBorel {X : Type} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) {R : Subgroup X} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Group.IsSolvable (centralizer (R : Set X)) := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hdvd : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rcases n with _ | n
    · exact absurd ((card_eq_one).mp (by simpa using hn)) hR1
    · rw [hn]
      exact dvd_pow_self 2 n.succ_ne_zero
  obtain ⟨⟨r, hrR⟩, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hdvd
  have hr' : orderOf r = 2 := by rwa [Subgroup.orderOf_mk] at hr
  have hse := (hB Q).1
  have hle : centralizer (R : Set X) ≤ normalizer ((Q : Subgroup X) : Set X) := by
    intro x hx
    by_contra hxN
    have hodd := hse.2.2 x hxN
    have hrM : r ∈ normalizer ((Q : Subgroup X) : Set X) := le_normalizer (hRQ hrR)
    have hxr : x * r = r * x := (mem_centralizer_iff.mp hx r hrR).symm
    have hrM' : r ∈ (normalizer ((Q : Subgroup X) : Set X)).map (MulAut.conj x⁻¹).toMonoidHom := by
      refine ⟨r, hrM, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, ← hxr, ← mul_assoc, inv_mul_cancel, one_mul]
    have hzle : zpowers r ≤ normalizer ((Q : Subgroup X) : Set X) ⊓
        (normalizer ((Q : Subgroup X) : Set X)).map (MulAut.conj x⁻¹).toMonoidHom :=
      (zpowers_le).mpr ⟨hrM, hrM'⟩
    have h2 : 2 ∣ Nat.card (normalizer ((Q : Subgroup X) : Set X) ⊓
        (normalizer ((Q : Subgroup X) : Set X)).map (MulAut.conj x⁻¹).toMonoidHom :
          Subgroup X) := by
      have h3 := card_dvd_of_le hzle
      rwa [Nat.card_zpowers, hr'] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have := isSolvable_normalizer_sylow_two Q
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

variable {G : Type} [Group G] [Finite G]

theorem false_of_bender_normal {A N E : Subgroup G} [hN : N.Normal]
    (hq : Open.IsQuasisimple A)
    (htight : TightlyEmbedded (centralizer (A : Set G)))
    (hNK : normalizer (centralizer (A : Set G) : Set G) ≠ ⊤) (hB : fusionIsBenderGroup N)
    (hEK : E ≤ centralizer (A : Set G)) (hEN : E ≤ N) (hE4 : Nat.card E = 4) : False := by
  set K := centralizer (A : Set G) with hK
  have : Group.IsPerfect A := ⟨hq.1⟩
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer N) :=
    isSolvable_outer_of_fusionIsBenderGroup hB
  let θ : A →* MulAut N := (MulAut.conjNormal (H := N)).comp A.subtype
  have hinner := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner θ
  set E' : Subgroup N := E.subgroupOf N with hE'
  have hE'p : IsPGroup 2 E' := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hE', Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv, hE4]
    norm_num
  have hE'1 : E' ≠ ⊥ := by
    intro h
    have : Nat.card E' = 1 := by rw [h, card_bot]
    rw [hE', Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv, hE4] at this
    norm_num at this
  obtain ⟨q, k, hBorel⟩ := exists_fusionBenderBorel hB
  have hsolv := isSolvable_centralizer_of_fusionBenderBorel hBorel hE'p hE'1
  have hcent : ∀ (a : A) (n : N), θ a = MulAut.conj n → n ∈ centralizer (E' : Set N) := by
    intro a n han
    rw [mem_centralizer_iff]
    intro e he
    have h1 := congrArg (fun φ : MulAut N => ((φ e : N) : G)) han
    simp only [θ, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, MulAut.conjNormal_apply,
      MulAut.conj_apply, coe_mul, coe_inv] at h1
    have hae : (a : G) * e = e * a := (mem_centralizer_iff.mp (hEK (mem_subgroupOf.mp he)) a a.2)
    have h2 : (n : G) * e * (n : G)⁻¹ = e := by
      rw [← h1, hae, mul_inv_cancel_right]
    apply Subtype.ext
    simp only [coe_mul]
    calc (e : G) * n = (n : G) * e * (n : G)⁻¹ * n := by rw [h2]
      _ = n * e := by group
  let Ψ : Subgroup (MulAut N) := (centralizer (E' : Set N)).map (MulAut.conj : N →* MulAut N)
  have hΨ : Group.IsSolvable Ψ := by
    have := hsolv
    exact Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective (MulAut.conj : N →* MulAut N) (centralizer (E' : Set N)))
  have hθΨ : ∀ a : A, θ a ∈ Ψ := fun a => by
    obtain ⟨n, hn⟩ := hinner a
    exact ⟨n, hcent a n hn, hn.symm⟩
  have hθ1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (θ.codRestrict Ψ hθΨ)
  have hAN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ = x := by
    intro a ha x hx
    have h1 := congrArg (fun φ : A →* Ψ => (((φ ⟨a, ha⟩ : Ψ) : MulAut N) ⟨x, hx⟩ : N)) hθ1
    simp only [MonoidHom.codRestrict_apply, MonoidHom.one_apply, OneMemClass.coe_one,
      MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val h1
    simpa [θ, MulAut.conjNormal_apply] using h2
  have hNK' : N ≤ K := by
    intro x hx
    rw [hK, mem_centralizer_iff]
    intro a ha
    have := hAN a ha x hx
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  apply hNK
  rw [eq_top_iff]
  intro x _
  by_contra hx
  have hodd := htight.2 x hx
  have hle : N ≤ K ⊓ rightConjugate K x := by
    intro n hn
    refine ⟨hNK' hn, (mem_rightConjugate_iff _ _ _).mpr (hNK' (hN.conj_mem n hn x))⟩
  have h4 : 4 ∣ Nat.card N := by
    rw [← hE4]
    exact card_dvd_of_le hEN
  have h2 : 2 ∣ Nat.card (K ⊓ rightConjugate K x : Subgroup G) :=
    (dvd_trans (by norm_num : 2 ∣ 4) h4).trans (card_dvd_of_le hle)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem exists_bender_normal {K E : Subgroup G} (hO : standardComponentOddCore G = ⊥)
    (hEK : E ≤ K) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hse : fusionStronglyEmbedded
      ((normalizer (K : Set G)).subgroupOf (normalClosure (K : Set G)))) :
    ∃ N : Subgroup G, N.Normal ∧ fusionIsBenderGroup N ∧ E ≤ N := by
  set L := normalClosure (K : Set G) with hL
  have hKL : K ≤ L := le_normalClosure
  have hEL : E ≤ L := hEK.trans hKL
  have hE'p : IsPGroup 2 (E.subgroupOf L) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv, hE4]
    norm_num
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3
      L _ hse with hcq | ⟨M₀, N₀, hM₀, hN₀, hMN, hle, hodd, hidx, hbender⟩
  ·
    exfalso
    obtain ⟨S, hS⟩ := hE'p.exists_le_sylow
    refine false_of_le_cyclic_or_quaternion hS ?_ ?_ (hcq S)
    · refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · have := hE.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩
        simpa using congrArg Subtype.val this
      · simpa using hE.2 _ hx
    · rw [Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv, hE4]
  ·
    have hM₀bot : M₀ = ⊥ := eq_bot_of_odd_normal hO hM₀ hodd
    subst hM₀bot
    have hB₀ : fusionIsBenderGroup N₀ :=
      bender_of_mulEquiv hbender ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf N₀)).trans
        QuotientGroup.quotientBot)
    set N := N₀.map L.subtype with hNdef
    have hB : fusionIsBenderGroup N :=
      bender_of_mulEquiv hB₀ (N₀.equivMapOfInjective L.subtype L.subtype_injective)
    have : IsSimpleGroup N :=
      CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
    set T := closure {x | x ∈ L ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} with hT
    have hTn : T.Normal := closure_twoElements_normal
    have hTN : T ≤ N := by
      rw [hT, closure_le]
      rintro x ⟨hxL, k, hk⟩
      refine ⟨⟨x, hxL⟩, mem_of_two_element_of_odd_index hidx (k := k) ?_, rfl⟩
      exact Subtype.ext (by simpa using hk)
    have hET : E ≤ T := fun x hx => subset_closure ⟨hEL hx, 1, by simpa using hE.2 x hx⟩
    have hTbot : T ≠ ⊥ := by
      intro h
      have : Nat.card E = 1 := by
        rw [card_eq_one, eq_bot_iff]
        exact h ▸ hET
      rw [hE4] at this
      norm_num at this
    have hTeq : T = N := by
      have hnorm : (T.subgroupOf N).Normal := hTn.subgroupOf N
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf N) with h | h
      · exfalso
        apply hTbot
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hTN hx⟩ : N) ∈ T.subgroupOf N := hx
        rw [h, mem_bot] at this
        simpa using congrArg Subtype.val this
      · refine le_antisymm hTN fun x hx => ?_
        have : (⟨x, hx⟩ : N) ∈ T.subgroupOf N := h ▸ mem_top _
        exact this
    exact ⟨N, hTeq ▸ hTn, hB, hTeq ▸ hET⟩

theorem exists_even_overlap {A : Subgroup G} (hA : standardComponentIsStandard A)
    (hO : standardComponentOddCore G = ⊥) (hrank : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnn : ¬ A.Normal) :
    ∃ g : G, g ∉ normalizer (A : Set G) ∧
      Even (Nat.card (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G) :
        Subgroup G)) := by
  set K := centralizer (A : Set G) with hK
  have htight := tightlyEmbedded_centralizer hA
  have hNK := normalizer_centralizer_eq hA
  have hNtop : normalizer (K : Set G) ≠ ⊤ := by
    rw [hNK]
    exact fun h => hnn (normalizer_eq_top_iff.mp h)
  by_contra hcon
  push Not at hcon
  have hodd : CFSG.ComponentClassification.AschbacherTightEmbedding.OddNormalizerOverlaps K := by
    intro g hg
    rw [hNK] at hg ⊢
    exact Nat.not_even_iff_odd.mp (hcon g hg)
  obtain ⟨E, hEK, hE, hE4⟩ := exists_elemAbelian_four hrank
  rcases CFSG.ComponentClassification.AschbacherStrongEmbedding.theorem_2_part_two
      CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      CFSG.ComponentClassification.AschbacherStrongEmbedding.benderDoubleCoverRigidity
      K htight hodd with hKn | hse
  · exact hNtop (normalizer_eq_top_iff.mpr hKn)
  · obtain ⟨N, hNn, hB, hEN⟩ := exists_bender_normal hO hEK hE hE4 hse
    exact false_of_bender_normal hA.1 htight hNtop hB hEK hEN hE4

theorem lemma32_of_asc76Theorem2 (hT2 : Asc76Theorem2) : Lemma32 := by
  intro G _ _ A hA R hR
  obtain ⟨g, hg, heven⟩ := exists_even_overlap hA.standard hA.oddCore hA.rank hA.not_normal
  obtain ⟨T, hT⟩ := exists_isSylowOf 2
    (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G))
  have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hT heven
  rcases hT2 G A hA.oddCore hA.standard (asc76HypII_of_hypII hA.standard.1 hA.hypII) hA.rank R
      hR g hg T hT hT1 with ⟨-, hel, -⟩ | ⟨hel, -⟩
  · exact hel
  · exact hel

theorem lemma33Three_of_asc76Theorem2 (hT2 : Asc76Theorem2) : Lemma33Three := by
  intro G _ _ A hA
  obtain ⟨g, hg, heven⟩ := exists_even_overlap hA.standard hA.oddCore hA.rank hA.not_normal
  obtain ⟨T, hT⟩ := exists_isSylowOf 2
    (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G))
  have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hT heven
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  rcases hT2 G A hA.oddCore hA.standard (asc76HypII_of_hypII hA.standard.1 hA.hypII) hA.rank R
      hR g hg T hT hT1 with ⟨-, -, g', hg', T', hT'1, hT'2⟩ | ⟨-, hTs, -⟩
  · exact ⟨g', hg', T', hT'1, hT'2⟩
  · exact ⟨g, hg, T, hT, hTs⟩

end CFSG.ComponentClassification.AS76b
