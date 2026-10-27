module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd15Comp
public import CFSG.Quasithin.EmptyFaithful.SBd14Glue

public section

namespace CFSG.Quasithin.SBd15

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Frontier15338_F4 : Prop where

  h11 : StageLemma14111

  h113 : StageLemma14113

  h25 : Stage15325_F4

  h34 : Input15334

  h36 : Input15336One

  h37 : Input15337

  hA37 : A37ForSQTK

  hA38 : A38ForSQTK

  hA39 : A39ForSQTK

  kR : RankOneFamilies153

  kR2 : RankTwoFamilies153

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_restHyp_F4 (F : Frontier15338_F4) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (c37 : Concl15337 T V₁ Yp L)
    (hNL : I ≤ Subgroup.normalizer (L : Set G)) (hr2 : 2 ≤ CFSG.Open.pRank 3 L) (hY : ¬ Yp ≤ L) :
    SBd14.RestHyp T Mc M V₁ V₂ Yp I L t ∨ SBd14.RestHyp T Mc M V₂ V₁ Yp I L t := by
  have hLI := c.c33.mem
  rcases c37 with h1 | ⟨hL0, hlist, -⟩ | ⟨hL0, hlist, hYL, hy⟩
  · exact absurd (h1.trans (S153I.conjClosure_le_of_normal (le_of_mem_cComp hLI)
      (le_sup_right.trans c.inH.1.1)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLI)).mpr hNL))) hY
  · exfalso
    have h := F.kR ↥L (S153I.isPGroup_two_center_of_center_eq c.c33.center_eq) hlist
    rw [pRank_top_subtype] at h
    omega
  · obtain ⟨hn2, hYY, ⟨hB, hBM, hQV⟩, hcase⟩ :=
      SBd9.prefix38_of_psl F.h113 F.hA37 F.hA38 c hL0 hlist hYL
    rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨c, hL0, hn2, hYL, hy, hY, hNL, hYY, hB, hBM, hQV, h1, h2, h3, h4⟩
    · have hS := SBd9.sgp153_swap c.hyp.hyp c.hyp.decomp
      have c' := SBd9.ctxComp2_swap c hYY
      have hL0' : L = conjClosure L (Sgp153 T V₂) := by rw [hS]; exact hL0
      rw [← hS] at hB hBM hQV
      exact Or.inr ⟨c', hL0', hn2, hYL, hy, hY, hNL, hYY, hB, hBM, hQV, h1, h2, h3, h4⟩

theorem exists_next_F4 (F : Frontier15338_F4) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (r : SBd14.RestHyp T Mc M V₁ V₂ Yp I L t) :
    ∃ W₁ W₂ L₁ : Subgroup G,
      SBd14.RestHyp T Mc M W₁ W₂ Yp (Subgroup.normalizer (V₁ : Set G)) L₁ t := by
  classical
  have hV : V₁ = centerOf L := r.V₁_eq_center F.h113
  have c : CtxComp2 T Mc M V₁ V₂ Yp I L t := r.ctx
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  set S := Sgp153 T V₁ with hSdef
  set I₁ : Subgroup G := Subgroup.normalizer (V₁ : Set G) with hI₁
  have hII₁ : I ≤ I₁ := SBd14.le_normalizer_of_eq_center r.hNL hV
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hLI₁ : L ≤ I₁ := hLI.trans hII₁

  have hpC : pCoreOf 2 I₁ ≠ ⊥ := by
    have hV₁2 : IsPGroup 2 ↥V₁ := IsPGroup.of_card (n := 2) (by rw [hh.decomp.card₁]; norm_num)
    have hle : V₁ ≤ pCoreOf 2 I₁ :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV₁2
    intro hb
    rw [hb, le_bot_iff] at hle
    have := hh.decomp.card₁
    rw [hle, Subgroup.card_bot] at this
    omega
  have hH : IsHPlus Yp S M I₁ :=
    ⟨⟨c.inH.1.1.trans hII₁, hpC⟩, fun hle => c.inH.2 (hII₁.trans hle)⟩
  have hF₁ : Facts153 T M V₁ Yp I₁ := S153D.facts153_of_stages F.h11 F.h113 hh hH
  have hS₁ : IsSylowTwoOf S I₁ := hF₁.sylow
  have hnc : ¬ CharTwo I₁ := F.h25 G T Mc M V₁ V₂ Yp t hh I₁ hH
  have c0 : CtxComp T Mc M V₁ V₂ Yp I₁ t :=
    ctxComp_of_inputs (S153D.input15311Eight_of_stages F.h113) F.h11 F.h113 hh hH hnc

  have hLloc : quasithinIsLocal S L :=
    isLocal_of_mem_cComp_of_sylow c.facts.sylow c.inH.1.2 c.c33.mem
  have hB : L ∈ lFamily S := mem_lFamily_of_isLocal hLloc
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := r.S_le_L
  have hqk := hq.qtke
  obtain ⟨L₁, hL₁, hLL₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists hqk hq.simple hq.nonabelian
    F.hA37 F.hA39 hpC hS₁ hLI₁ hB
  have hnorm : (L₁.subgroupOf I₁).Normal := CFSG.Quasithin.lemma_1_2_4_normal hqk hq.simple
    hq.nonabelian F.hA37 F.hA38 hpC hS₁ hB hLL₁ hL₁ hSL
  have hL₁I₁ : L₁ ≤ I₁ := le_of_mem_cComp hL₁
  have hNL₁ : I₁ ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁I₁).mp hnorm

  have hcomp : IsComponentIn L₁ I₁ := by
    by_contra hnc'
    have hCT : CharTwo L₁ := S153H.charTwo_of_mem_cComp_not_isComponentIn c0.oddCore hL₁ hnc'
    have hN : Yp ⊔ S ≤ Subgroup.normalizer (L₁ : Set G) := c0.inH.1.1.trans hNL₁
    have hle : L₁ ≤ M ⊓ I₁ := le_M_of_charTwo_F4 F.h113 F.h25 c0 hL₁I₁ hN hCT
    exact c.c33.not_le (hLL₁.trans (hle.trans inf_le_left))
  have c33₁ : Concl15333 T M V₁ Yp I₁ L₁ := concl15333_of_isComponentIn_F4 F.h11 F.h113 F.h25 c0 hcomp
  have c₁ : CtxComp2 T Mc M V₁ V₂ Yp I₁ L₁ t :=
    { c0 with
      rank := c.rank
      facts11 := S153D.facts15311_of_stages F.h11 F.h113 hh c.rank hH
      s3s3 := F.h36 G T Mc M V₁ V₂ Yp t hh c.rank I₁ hH
      c33 := c33₁
      c34 := F.h34 G T Mc M V₁ V₂ Yp I₁ L₁ t c0 c33₁ }
  have c37₁ : Concl15337 T V₁ Yp L₁ := F.h37 G T Mc M V₁ V₂ Yp I₁ L₁ t c₁

  have hr2L : 2 ≤ CFSG.Open.pRank 3 L := by
    have h := F.kR2 ↥L (S153I.isPGroup_two_center_of_center_eq c.c33.center_eq) (Or.inr r.hn2)
    rwa [pRank_top_subtype] at h
  have hr2L₁ : 2 ≤ CFSG.Open.pRank 3 L₁ :=
    hr2L.trans (CFSG.SectionRank.pRank_mono (by norm_num) hLL₁)

  have hY₁ : ¬ Yp ≤ L₁ := by
    intro hYL₁
    have hcent : L₁ ≤ Subgroup.centralizer (V₁ : Set G) :=
      le_centralizer_of_isPerfect_of_card_le_four hh.decomp.card₁.le hL₁I₁
        (perfect_of_mem_cComp hL₁)
    obtain ⟨t', ht'T, -, -, hc2, -⟩ := SBd14.exists_swap hh.hyp hh.decomp
    obtain ⟨y₂, hy₂, y₁, hy₁, -, ⟨v₁, hv₁, hne'⟩⟩ := r.exists_pair hc2
    exact hne' ((Subgroup.mem_centralizer_iff.mp (hcent (hYL₁ (r.D_le_Yp ht'T hy₁))) v₁ hv₁).symm)
  rcases exists_restHyp_F4 F c₁ c37₁ hNL₁ hr2L₁ hY₁ with r₁ | r₁
  · exact ⟨V₁, V₂, L₁, r₁⟩
  · exact ⟨V₂, V₁, L₁, r₁⟩

end CFSG.Quasithin.SBd15
