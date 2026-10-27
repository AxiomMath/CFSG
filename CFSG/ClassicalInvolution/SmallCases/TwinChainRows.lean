module

public import CFSG.ClassicalInvolution.SmallCases.TwinChainX
public import CFSG.ClassicalInvolution.RouteD.ExoticD4TwinModel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternNodes
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpBasic
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinMain
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthGenRows
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_mem_of_nonA1_comp (hMFZ : Gaps.FundNoncentral p) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {z : G} (D : LieSystemData p f (locQuot Ω z) (locFamily Ω z))
    {i : Fin D.card} (hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) {M : Subgroup G}
    (hM : M ∈ compMembers Ω z D i) (hz2 : orderOf z = 2) : z ∉ M := by
  intro hzM
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hM
  obtain ⟨k, hkR, hk⟩ := exists_model_elt hR hzM
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer hM.1 hzM
  have hcentral : ∀ a : locQuot Ω z,
      locMk Ω z ⟨z, hzY⟩ * a = a * locMk Ω z ⟨z, hzY⟩ := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    show locMk Ω z ⟨z, hzY⟩ * locMk Ω z y = locMk Ω z y * locMk Ω z ⟨z, hzY⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show z * (y : G) = (y : G) * z
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} y.2)).symm
  have h1 : k = 1 := by
    refine hMFZ (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i) (D.admissible i) hne R hR.2.1 k
      hkR fun y => ?_
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hk]
    rw [hcentral (D.hom i y)]
    group
  exact ne_one_of_hom_eq_locMk hzY hz2 hk h1

theorem exists_chain_of_layer (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hcen : Subgroup.center G = ⊥)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hIH : LocalLieSystems p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (D : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) (i₁ : Fin D.card) (hcard : D.card = 3)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2)
    (hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2))
    (hKj : ∃ j, j ≠ i₁ ∧ locImg Ω z K ≤ (D.hom j).range)
    (hP1x : ∀ M ∈ Ω, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
      LocalOddCentral Ω {z * w})
    (hlink : ∀ K₂ ∈ centralizingMembers Ω {z}, locImg Ω z K₂ ≤ (D.hom i₁).range →
      ∀ w : G, IsClassicalMember p f K₂ w → LinkedAtProduct Ω K z w)
    (hTwin : TwinPartnerFactTwin p f .POmegaPlus 4 f) :
    ∃ (K₁ K₂ : Subgroup G) (z₁ : G), K₁ ∈ Ω ∧ K₂ ∈ Ω ∧ IsClassicalMember p f K₁ z₁ ∧
      Commutes K K₂ ∧ (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K K₁) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) ∧
      locImg Ω z K₂ ≤ (D.hom i₁).range := by
  classical
  have hMFZ := Gaps.fundNoncentral p
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨j₀, hj₀, hKj₀⟩ := hKj
  obtain ⟨a₀, a₂, h0, h2, h02, hall⟩ := exists_three_indices hcard i₁
  obtain ⟨j', hj'₁, hj'₀⟩ : ∃ j', j' ≠ i₁ ∧ j' ≠ j₀ := by
    rcases hall j₀ with h | h | h
    · exact ⟨a₂, h2, fun e => h02 (h.symm.trans e.symm)⟩
    · exact absurd h hj₀
    · exact ⟨a₀, h0, fun e => h02 (e.trans h)⟩
  obtain ⟨hj'tag, hj'rank⟩ := hrest j' hj'₁
  obtain ⟨T₁, hT₁, hT₁img⟩ := mem_locFamily_iff.mp (range_mem_of_A1 D j' hj'tag hj'rank)
  have hT₁j' : locImg Ω z T₁ ≤ (D.hom j').range := hT₁img.le
  have hT₁K : T₁ ≠ K := by
    rintro rfl
    exact hj'₀ (eq_of_locImg_le_range hΩ hex D hT₁ hT₁j' hKj₀)
  have hT₁comm : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T₁ → Commutes T₁ N := by
    intro N hN hNT
    obtain ⟨m, hm⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    by_cases hmj : m = j'
    · subst hmj
      exfalso
      apply hNT
      have e1 : locImg Ω z N = (D.hom m).range :=
        Subgroup.eq_of_le_of_card_ge hm (by
          rw [card_locImg hΩ hex hN]
          exact card_range_le_of_psl_two D m hj'tag hj'rank)
      exact locImg_injOn hΩ hP1 hN hT₁ (e1.trans hT₁img.symm)
    · exact commutes_of_ne_comp hΩ hP1 D (Ne.symm hmj) ⟨hT₁, hT₁j'⟩ ⟨hN, hm⟩
  obtain ⟨R₁, -, hmem⟩ := D.meets i₁
  obtain ⟨K₂, hK₂, hK₂img⟩ := mem_locFamily_iff.mp hmem
  have hK₂i : locImg Ω z K₂ ≤ (D.hom i₁).range := by
    rw [hK₂img]
    exact Subgroup.map_le_range _ _
  have hK₂K : K₂ ≠ K := by
    rintro rfl
    exact hj₀ (eq_of_locImg_le_range hΩ hex D hK₂ hKj₀ hK₂i)
  have hK₂T : K₂ ≠ T₁ := by
    rintro rfl
    exact hj'₁ (eq_of_locImg_le_range hΩ hex D hK₂ hT₁j' hK₂i)
  obtain ⟨w, hw⟩ := hΩ.classical K₂ hK₂.1
  have hzw : z ≠ w := fun h =>
    not_mem_of_nonA1_comp hMFZ hΩ hex D hbig ⟨hK₂, hK₂i⟩ hz.orderOf_eq_two
      (by rw [h]; exact hw.mem)
  have hKK₂ : Commutes K K₂ :=
    (commutes_or_eq_of_involution hMFZ hΩ hex hP1 D hKz hK₂ hz).resolve_right hK₂K
  obtain ⟨N, hN, pKN, pNK₂⟩ := exists_chain_of_twin_product hp2 hq hcen hΩ hex hIH hK hsingle hz
    hP1 hT₁ hT₁K hT₁comm hK₂ hK₂K hK₂T hw hzw (hP1x K₂ hK₂.1 w hw hKK₂ hzw)
    (hlink K₂ hK₂ hK₂i w hw) hTwin
  obtain ⟨z₁, hz₁⟩ := hΩ.classical N hN.1
  exact ⟨N, K₂, z₁, hN.1, hK₂.1, hz₁, hKK₂, pKN, pNK₂, hK₂i⟩

theorem commutes_ne_of_big_comp (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (D : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {i₁ j₀ : Fin D.card} (hj₀ : j₀ ≠ i₁)
    (hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2)) (hK : K ∈ Ω)
    (hKj₀ : locImg Ω z K ≤ (D.hom j₀).range) {K₂ : Subgroup G}
    (hK₂ : K₂ ∈ centralizingMembers Ω {z}) (hK₂i : locImg Ω z K₂ ≤ (D.hom i₁).range)
    {w : G} (hw : IsClassicalMember p f K₂ w) :
    K₂ ≠ K ∧ Commutes K K₂ ∧ z ≠ w := by
  have hMFZ := Gaps.fundNoncentral p
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hK₂K : K₂ ≠ K := by
    rintro rfl
    exact hj₀ (eq_of_locImg_le_range hΩ hex D hK₂ hKj₀ hK₂i)
  exact ⟨hK₂K,
    (commutes_or_eq_of_involution hMFZ hΩ hex hP1 D hKz hK₂ hz).resolve_right hK₂K,
    fun h => not_mem_of_nonA1_comp hMFZ hΩ hex D hbig ⟨hK₂, hK₂i⟩ hz.orderOf_eq_two
      (by rw [h]; exact hw.mem)⟩

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem twinSp2Chain_of_inputs (hP1 : ProductOfTwoP1 p f) (hlink : TwinSp2Linked p f)
    (hTwin : NonClassical.TwinPartnerFactTwin p f .POmegaPlus 4 f) : TwinSp2Chain p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨Λ⟩ := hshape.nonempty_spLayer
  obtain ⟨j₀, hj₀, hKj₀⟩ := SpLayer.exists_other_of_self S.five (mem_conjClass_self K) S.cls Λ
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, hK₂i⟩ :=
    exists_chain_of_layer S.odd S.five (center_eq_bot hnab) S.inClass S.exact S.ih
      (mem_conjClass_self K) (single_class K) S.cls S.p1 Λ.D Λ.i₁
      (by have := Λ.card_eq; omega) Λ.rest
      (by
        rintro ⟨h, -⟩
        rw [Λ.tag_eq] at h
        exact absurd h (by decide))
      ⟨j₀, hj₀, hKj₀⟩ (fun M hM w hw hc hzw => hP1 G hnab K z S M hM w hw hc hzw)
      (fun K₂ hK₂ hi w hw => hlink G hnab K z S hshape Λ K₂ hK₂ hi w hw) hTwin
  exact ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩

theorem twinSU4ChainData_of_inputs (hP1 : ProductOfTwoP1 p f) (hlink : TwinSU4Linked p f)
    (hTwin : NonClassical.TwinPartnerFactTwin p f .POmegaPlus 4 f) : TwinSU4ChainData p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨Λ⟩ := hshape.nonempty_suLayer
  obtain ⟨j₀, hj₀, hKj₀⟩ := Λ.exists_other_of_self S.odd S.five (mem_conjClass_self K) S.cls
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, hK₂i⟩ :=
    exists_chain_of_layer S.odd S.five (center_eq_bot hnab) S.inClass S.exact S.ih
      (mem_conjClass_self K) (single_class K) S.cls S.p1 Λ.D Λ.i₁
      (by have := Λ.card_eq; omega) Λ.rest
      (by
        rintro ⟨h, -⟩
        rw [Λ.tag_eq] at h
        exact absurd h (by decide))
      ⟨j₀, hj₀, hKj₀⟩ (fun M hM w hw hc hzw => hP1 G hnab K z S M hM w hw hc hzw)
      (fun K₂ hK₂ hi w hw => hlink G hnab K z S hshape Λ K₂ hK₂ hi w hw) hTwin
  exact ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩

@[expose] def LinkedAtTwinProduct (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LinkedAtProduct (conjClass K) K z w

theorem twinSp2Linked_of_linkedAtTwinProduct (h : LinkedAtTwinProduct p f) :
    TwinSp2Linked p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂i w hw
  obtain ⟨j₀, hj₀, hKj₀⟩ := SpLayer.exists_other_of_self S.five (mem_conjClass_self K) S.cls Λ
  obtain ⟨-, hc, hzw⟩ := commutes_ne_of_big_comp S.inClass S.exact S.cls S.p1 Λ.D hj₀
    (by
      rintro ⟨h', -⟩
      rw [Λ.tag_eq] at h'
      exact absurd h' (by decide))
    (mem_conjClass_self K) hKj₀ hK₂ hK₂i hw
  exact h G hnab K z S K₂ hK₂.1 w hw hc hzw

theorem twinSU4Linked_of_linkedAtTwinProduct (h : LinkedAtTwinProduct p f) :
    TwinSU4Linked p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂i w hw
  obtain ⟨j₀, hj₀, hKj₀⟩ := Λ.exists_other_of_self S.odd S.five (mem_conjClass_self K) S.cls
  obtain ⟨-, hc, hzw⟩ := commutes_ne_of_big_comp S.inClass S.exact S.cls S.p1 Λ.D hj₀
    (by
      rintro ⟨h', -⟩
      rw [Λ.tag_eq] at h'
      exact absurd h' (by decide))
    (mem_conjClass_self K) hKj₀ hK₂ hK₂i hw
  exact h G hnab K z S K₂ hK₂.1 w hw hc hzw

theorem pieceTwinSp2_of_inputs (hP1 : ProductOfTwoP1 p f) (hlink : TwinSp2Linked p f)
    (hTwin : NonClassical.TwinPartnerFactTwin p f .POmegaPlus 4 f) : PieceTwinSp2 p f :=
  pieceTwinSp2_of_chain (twinSp2Chain_of_inputs hP1 hlink hTwin)

theorem pieceTwinSU4_of_inputs (hb : SU4SpinMinus p f (minusCoeffs_irr p f))
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) (hP1 : ProductOfTwoP1 p f)
    (hlink : TwinSU4Linked p f) (hTwin : NonClassical.TwinPartnerFactTwin p f .POmegaPlus 4 f)
    (hpat : SU4PatternStmt p f) : PieceTwinSU4 p f :=
  pieceTwinSU4_of_chain hb hg6
    (twinSU4Chain_of_chainData (twinSU4ChainData_of_inputs hP1 hlink hTwin) hpat)

theorem twinSp2Chain_of_p1_linked (hP1 : ProductOfTwoP1 p f) (hlink : TwinSp2Linked p f) :
    TwinSp2Chain p f := by
  intro G _ _ _ hnab K z S hshape
  exact twinSp2Chain_of_inputs hP1 hlink
    (NonClassical.twinPartnerFactTwin_pOmegaPlus_four S.odd S.five) G hnab K z S hshape

theorem twinSU4ChainData_of_p1_linked (hP1 : ProductOfTwoP1 p f) (hlink : TwinSU4Linked p f) :
    TwinSU4ChainData p f := by
  intro G _ _ _ hnab K z S hshape
  exact twinSU4ChainData_of_inputs hP1 hlink
    (NonClassical.twinPartnerFactTwin_pOmegaPlus_four S.odd S.five) G hnab K z S hshape

end CFSG.ClassicalInvolution.Generic.CoreAssembly
