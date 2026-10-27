module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalSuz
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMain
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.ComponentClassification.LocalBNormalGeneration

public section

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian standardComponentIsStandard standardComponentOddCore ordA)
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.RankTwoExceptional

section Orders

theorem three_dvd_card_of_psl_two {Q : Type} [Group Q] {n : ℕ} (hn : 1 ≤ n)
    (h : StatedClassicalModel Q .PSL 2 2 n) : 3 ∣ Nat.card Q := by
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  simp only [EvenSmallLie.CatalogOrders.lieOrd, ordA]
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : Odd (2 ^ n - 1) := by
    have h2 : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  have hgcd : Nat.gcd (1 + 1) (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hgcd, Nat.div_one, show (1 + 1 : ℕ) = 2 from rfl, Finset.Icc_self, Finset.prod_singleton]
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 n
    rw [one_pow, ← pow_mul, mul_comm, pow_mul] at h
    exact h
  exact Dvd.dvd.mul_left h3 _

theorem two_pow_seven_dvd_of_classical {Q : Type} [Group Q] {t : StatedLieTag} {n m : ℕ}
    (hm : 1 ≤ m) (hn : EvenSmallLie.CatalogOrders.lieMin t ≤ n)
    (he : 7 ≤ EvenSmallLie.CatalogOrders.lieExp t n) (h : StatedClassicalModel Q t n 2 m) :
    2 ^ 7 ∣ Nat.card Q := by
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  refine dvd_trans ?_ (EvenSmallLie.CatalogOrders.pow_lieExp_dvd hn (2 ^ m))
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 (by nlinarith)

theorem not_alternating_of_two_pow_seven_dvd {Q : Type} [Group Q] (h : 2 ^ 7 ∣ Nat.card Q) :
    ¬ Nonempty (Q ≃* alternatingGroup (Fin 8)) ∧ ¬ Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  have h8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · rw [Nat.card_congr e.toEquiv, h8] at h
    norm_num at h
  · rw [Nat.card_congr e.toEquiv, h6] at h
    norm_num at h

theorem false_of_g2Four_of_e7
    {B : Type} [Group B] [Finite B] {m : ℕ} (hm : 1 ≤ m)
    (hB : ChevalleyExceptionalModel B .G2 2 2)
    (hE : ChevalleyExceptionalModel (B ⧸ center B) .E7 2 m) : False := by
  have hcB := EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hB
  have hcE := EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hE
  simp only [EvenSmallLie.CatalogOrders.lieOrd] at hcB hcE
  have hdvd : (2 ^ m) ^ 63 ∣ Nat.card (B ⧸ center B) := by
    rw [hcE]
    exact EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .E7) (n := 0) (le_refl _) (2 ^ m)
  have hpos : 0 < Nat.card (B ⧸ center B) := Nat.card_pos
  have hle1 : 2 ^ 63 ≤ Nat.card (B ⧸ center B) := by
    refine le_trans ?_ (Nat.le_of_dvd hpos hdvd)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle2 : Nat.card (B ⧸ center B) ≤ Nat.card B :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  rw [hcB] at hle2
  simp only [CFSG.Open.ordG2] at hle2
  norm_num at hle2
  omega

end Orders

section Group

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_rankTwoHyp {A : Subgroup G} (hH : RankTwoHyp G A)
    (hO : standardComponentOddCore G = ⊥) : center G = ⊥ := by
  by_cases hodd : Odd (Nat.card (center G))
  · have h : center G ≤ standardComponentOddCore G := le_sSup ⟨inferInstance, hodd⟩
    rw [hO] at h
    exact le_bot_iff.mp h
  · exfalso
    apply hH.not_normal
    have htight := AS76b.tightlyEmbedded_centralizer hH.standard
    rw [← normalizer_eq_top_iff, ← AS76b.normalizer_centralizer_eq hH.standard, eq_top_iff]
    intro g _
    by_contra hg
    have h := htight.2 g hg
    have hZK : center G ≤ centralizer (A : Set G) := fun z hz =>
      mem_centralizer_iff.mpr fun a _ => (mem_center_iff.mp hz a)
    have hle : center G ≤ centralizer (A : Set G) ⊓
        rightConjugate (centralizer (A : Set G)) g := by
      refine le_inf hZK fun z hz => (mem_rightConjugate_iff _ _ _).mpr ?_
      rw [mem_center_iff.mp hz g, mul_inv_cancel_right]
      exact hZK hz
    exact hodd (h.of_dvd_nat (Subgroup.card_dvd_of_le hle))

theorem card_centralizer_lt {A : Subgroup G} (hH : RankTwoHyp G A)
    (hO : standardComponentOddCore G = ⊥) {Q : Subgroup G} (hQ : Q ≠ ⊥) :
    Nat.card (centralizer (Q : Set G)) < Nat.card G := by
  have hZ := center_eq_bot_of_rankTwoHyp hH hO
  have hne : centralizer (Q : Set G) ≠ ⊤ := by
    intro htop
    apply hQ
    rw [eq_bot_iff, ← hZ]
    intro q hq
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer (Q : Set G) := htop ▸ mem_top g
    exact (mem_centralizer_iff.mp hg q hq).symm
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)

theorem four_le_card_of_isSylowOf {R K : Subgroup G} (hR : IsSylowOf 2 R K)
    (hK : 2 ≤ CFSG.Open.pRank 2 K) : 4 ≤ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hK
  obtain ⟨Q, rfl⟩ := hR
  have hUp : IsPGroup 2 (U.subgroupOf K) := by
    intro x
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hU.2 _ (mem_subgroupOf.mp x.2)))⟩
  obtain ⟨P, hP⟩ := hUp.exists_le_sylow
  have h1 : Nat.card (U.subgroupOf K) = 4 := by
    rw [← hU4]
    exact Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv
  have h2 : Nat.card (U.subgroupOf K) ≤ Nat.card P := Subgroup.card_le_of_le hP
  have h3 : Nat.card P = Nat.card Q := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h4 : Nat.card ((Q : Subgroup K).map K.subtype) = Nat.card Q :=
    Nat.card_congr ((Q : Subgroup K).equivMapOfInjective _ K.subtype_injective).toEquiv.symm
  omega

omit [Finite G] in
theorem commutator_rankTwoX {L : Subgroup G} (hL : commutator ↥L = ⊤) :
    commutator ↥(rankTwoX L) = ⊤ := by
  have : Group.IsPerfect ↥L := (Group.isPerfect_def).2 hL
  exact (Group.isPerfect_def).1 (LocalBNormalGeneration.perfect_normalClosure L)

omit [Finite G] in
theorem odd_card_centralizer_rankTwoX {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hnn : ¬ L.Normal) : Odd (Nat.card (centralizer (rankTwoX L : Set G))) := by
  by_contra hev
  apply hnn
  have htight := AS76b.tightlyEmbedded_centralizer hL
  rw [← normalizer_eq_top_iff, ← AS76b.normalizer_centralizer_eq hL, eq_top_iff]
  intro g _
  by_contra hg
  have h := htight.2 g hg
  have hCX : centralizer (rankTwoX L : Set G) ≤ centralizer (L : Set G) :=
    centralizer_le Subgroup.subset_normalClosure
  have hCXn : (centralizer (rankTwoX L : Set G)).Normal := inferInstance
  have hle : centralizer (rankTwoX L : Set G) ≤ centralizer (L : Set G) ⊓
      rightConjugate (centralizer (L : Set G)) g :=
    le_inf hCX fun x hx => (mem_rightConjugate_iff _ _ _).mpr (hCX (hCXn.conj_mem x hx g))
  exact hev (h.of_dvd_nat (Subgroup.card_dvd_of_le hle))

end Group

section Lemma815

variable {G : Type} [Group G] [Finite G]

theorem standard_of_config
    (h75 : AS76b.Asc75Theorem4) (h32 : AS76b.Lemma32) {A : Subgroup G} (hA : AS76b.Hyp31 A)
    {D : ExcModel A} {g : G} {R T Q : Subgroup G} (hc : Config814 D g R T Q) :
    standardComponentIsStandard
        ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))) ∧
      ¬ ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTR : Nat.card T = Nat.card R := by
    rw [hc.sylowT.card_eq, hc.sylowR.card_eq, rightConjugate_card]
  exact AS76b.lemma38 h75 h32 AS76b.asc08Lemma34 hA hc.sylowR hc.le hc.quasisimple
    hc.sylow_inf hc.le_sup hc.inf_eq_bot hTR hc.not_le hc.noConj

theorem false_of_bender (h2 : RankTwoBenderStandard)
    {H : Type} [Group H] [Finite H] {B : Subgroup H} (hB : RankTwoHyp H B)
    (hO : standardComponentOddCore H = ⊥) {n : ℕ} (hn : 3 ≤ n)
    (hT : StatedClassicalModel (rankTwoQuot B) .PSL 2 2 n) : False := by
  obtain ⟨hSz, -⟩ := h2 H B hB hO (Or.inl ⟨n, hn, hT⟩)
  exact RankTwoL3Even.not_three_dvd_card_of_suzukiModel_three hSz
    (three_dvd_card_of_psl_two (by omega) hT)

theorem false_of_triality_four (hSuz : SuzL34DiagInput) (h32 : AS76b.Lemma32)
    {A : Subgroup G} (hA : AS76b.Hyp31 A) (hH : RankTwoHyp G A) {R Q : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hQA : Q ≤ A)
    (hstd : standardComponentIsStandard
      ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))))
    (hnn : ¬ ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))).Normal)
    (hZ : Odd (Nat.card (center ↥(AS76b.layerCentralizer A Q))))
    (hT : StatedClassicalModel (rankTwoQuot (AS76b.layerCentralizer A Q)) .PSL 3 2 2)
    (h4 : L3EvenAt ↥(centralizer (Q : Set G))
      ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))))
    (hy : ∃ y ∈ A ⊓ centralizer (Q : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
      ¬ InducesInner y (AS76b.layerCentralizer A Q)) : False := by
  set W := centralizer (Q : Set G) with hW
  set L := AS76b.layerCentralizer A Q with hLdef
  have hLAW : L ≤ A ⊓ W := AS76b.layerCentralizer_le A Q
  have hLW : L ≤ W := hLAW.trans inf_le_right
  have hLA : L ≤ A := hLAW.trans inf_le_left
  have hH' : RankTwoHyp ↥W (L.subgroupOf W) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
        (fun e h => SectionRank.catalog_of_mulEquiv e h) hH.kProper W, hstd, hnn,
      RankTwoL3Even.two_le_pRank_centralizer_subgroupOf hQA hLA hH.rank⟩
  let eLL : ↥(L.subgroupOf W) ≃* ↥L := subgroupOfEquivOfLe hLW
  have hTL' : StatedClassicalModel (rankTwoQuot (L.subgroupOf W)) .PSL 3 2 2 :=
    SectionRank.statedClassicalModel_of_mulEquiv (quotCenterCongr eLL) hT
  obtain ⟨-, hii, -⟩ := h4 hH' 2 le_rfl hTL'
  rcases hii rfl with ⟨hSz, -⟩ | ⟨⟨eE⟩, -⟩
  swap
  · have hcardE : Nat.card (center ↥(L.subgroupOf W)) = 4 := by
      rw [Nat.card_congr eE.toEquiv, Nat.card_prod]
      simp
    have hcardZ : Nat.card (center ↥(L.subgroupOf W)) = Nat.card (center ↥L) :=
      Nat.card_congr ((MulEquiv.subgroupMap eLL (center _)).toEquiv.trans
        (MulEquiv.subgroupCongr (Subgroup.map_center_eq eLL)).toEquiv)
    rw [hcardZ] at hcardE
    rw [hcardE] at hZ
    exact absurd hZ (by decide)
  obtain ⟨e⟩ := hSz
  obtain ⟨y, ⟨hyA, hyQ⟩, ⟨k, hk⟩, hyn⟩ := hy
  apply hyn
  have hyW : y ∈ W := hyQ
  have hRW : R ≤ W := hR.le.trans (centralizer_le hQA)
  have hRL : R ≤ centralizer (L : Set G) := hR.le.trans (centralizer_le hLA)
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  have hyL : y ∈ normalizer (L : Set G) :=
    AS76b.normalizer_inf_le_normalizer_layerCentralizer A Q ⟨le_normalizer hyA, hyQ⟩
  refine inducesInner_subgroupOf hLW (y := ⟨y, hyW⟩) ?_
  refine inducesInner_of_l34DiagFact (X₀ := NativeSporadic.Carrier .Suz) hSuz
    (X := rankTwoX (L.subgroupOf W)) (R := R.subgroupOf W)
    (commutator_rankTwoX hstd.1.1) e Subgroup.le_normalClosure hstd.1 hTL' ?_ ?_ ?_ ?_ ?_ ?_
    ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro r hr
    rw [mem_centralizer_iff]
    intro l hl
    exact Subtype.ext (mem_centralizer_iff.mp (hRL (mem_subgroupOf.mp hr)) l
      (mem_subgroupOf.mp hl))
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun r hr => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, mem_subgroupOf.mp a.2⟩
        ⟨b, mem_subgroupOf.mp b.2⟩)
      simpa using this
    · simpa using hRe.2 _ (mem_subgroupOf.mp hr)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hRW).toEquiv]
    exact four_le_card_of_isSylowOf hR hH.rank
  · refine AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ _ ?_
      (odd_card_centralizer_rankTwoX hstd hnn) inf_le_right
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hRe.2 _ (mem_subgroupOf.mp (mem_inf.mp x.2).1)
  · rw [mem_normalizer_iff]
    intro l
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hyL l
  · rw [mem_centralizer_iff]
    intro r hr
    exact Subtype.ext (mem_centralizer_iff.mp (hR.le (mem_subgroupOf.mp hr)) y hyA).symm

end Lemma815

end CFSG.ComponentClassification.RankTwoExceptional
