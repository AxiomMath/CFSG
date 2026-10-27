module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Six
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PJ
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Lift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Setting
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.RankThree.PartOne.S12.Sec13Zero

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

theorem small1522_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : Small1522 S') : Small1522 S := by
  rcases h with (⟨h1, d, q, hq, hd, hf⟩ | ⟨h1, d, Q, hQ, hQe, hd, hf⟩) | hf | hf |
    ⟨Q, hQ, hc, d, hd, hf⟩ | ⟨d, hd, hf⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl (Or.inl ⟨h1, d, q, hq, hd, ⟨e.trans f⟩⟩)
  · obtain ⟨f⟩ := hf
    exact Or.inl (Or.inr ⟨h1, d, Q, hQ, hQe, hd, ⟨e.trans f⟩⟩)
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Q, hQ, hc, d, hd, ⟨e.trans f⟩⟩)))
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, hd, ⟨e.trans f⟩⟩)))

variable {X : Type} [Group X] [Finite X]

theorem small1522_map_toStar_of_small1522_subgroupOf {T L M : Subgroup X} (hTM : T ≤ M)
    (hLM : L ≤ M) (hLn : L.Normal) (hq : CFSG.Open.IsQuasisimple ↥(L.map (toStar T)))
    (h : Small1522 ↥((L.subgroupOf M).map (toStar (T.subgroupOf M)))) :
    Small1522 ↥(L.map (toStar T)) := by
  have hZ := inf_comap_centralizer_le_centralizer_uCore hTM hLM (small1522_simple_center h).2
  obtain ⟨e⟩ := nonempty_mulEquiv_map_toStar_subgroupOf hTM hLM
    (inf_centralizer_uCore_le_gnC_of_le hLn hLM hq hZ)
  exact small1522_of_mulEquiv e h

theorem gnA_le_map_normalizer_two_of_le_gnImg_sup {T T₁ T₂ L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    (hcomp : GNYComponent T T₁ T₂ Ls) (hlift : LiftOf T L Ls) (hLn : L.Normal)
    (hg₁ : GNGood (T.subgroupOf (L ⊔ T)) (T₁.subgroupOf (L ⊔ T)) (T₂.subgroupOf (L ⊔ T)))
    (h : (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T))) ≤
      gnImg (T.subgroupOf (L ⊔ T))
        (Subgroup.normalizer ((T₂.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)))) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  obtain ⟨hC2, rfl⟩ := hlift
  have hgn₁ := gnSetting_sup_of_normal hX hLn
  have hLM : L ≤ L ⊔ T := le_sup_left
  haveI := hLn
  have hLn₁ : (L.subgroupOf (L ⊔ T)).Normal := Subgroup.normal_subgroupOf
  have hsl₁ := gnA_le_map_normalizer_two_of_sup_eq_top hgn₁ hg₁
    ⟨isC2_subgroupOf_of_normal hLn hLM hC2, rfl⟩ hLn₁ (sup_subgroupOf_sup_eq_top L T)
  have hq := hcomp.1.2.2
  have hT₂M : T₂ ≤ L ⊔ T := hg.pair.le₂.trans le_sup_right
  refine le_trans (inf_le_right : gnA T T₂ (L.map (toStar T)) ≤ L.map (toStar T))
    (CFSG.RankThree.PartOne.le_of_isPerfect_of_forall_mul_central ⟨hq.1⟩ fun y hy => ?_)
  obtain ⟨l, hl, rfl⟩ := hy
  have hm : toStar (T.subgroupOf (L ⊔ T)) ⟨l, hLM hl⟩ ∈
      (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
  obtain ⟨n, hnNL, hn⟩ := hsl₁ (Subgroup.mem_inf.mpr ⟨h hm, hm⟩)
  obtain ⟨hnN, hnL⟩ := Subgroup.mem_inf.mp hnNL
  have hk : (n : X)⁻¹ * l ∈ L ⊓ Subgroup.centralizer (uCore (L ⊔ T) T : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (Subgroup.mem_subgroupOf.mp hnL)) hl, ?_⟩
    have h1 : n⁻¹ * ⟨l, hLM hl⟩ ∈ gnC (T.subgroupOf (L ⊔ T)) := QuotientGroup.eq.mp hn
    rw [gnC_subgroupOf_eq le_sup_right, Subgroup.mem_subgroupOf] at h1
    exact h1
  rw [← Subgroup.subgroupOf_normalizer_eq hT₂M] at hnN
  have hz := inf_centralizer_uCore_le_comap_centralizer hLn hLM hq hk
  rw [Subgroup.mem_comap, map_mul, map_inv, Subgroup.mem_centralizer_iff] at hz
  exact ⟨toStar T n, Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hnL), Subgroup.mem_map_of_mem _
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hnN, Subgroup.mem_subgroupOf.mp hnL⟩)⟩,
    (toStar T n)⁻¹ * toStar T l, fun x hx => (hz x hx).symm, mul_inv_cancel_left _ _⟩

theorem exists_rank_two_of_bad_of_gnSixAll (hT : LieOddRankTable) (hKSMAlt : KSMAlt)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b) (hSix : GNSixAll)
    {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (hLn : L.Normal) (h20 : CFSG.Open.pRank 3 L < 3)
    (hbad : ¬ Small1522 ↥Ls) :
    ∃ (Ti : Subgroup X) (r : ℕ), (Ti = T₁ ∨ Ti = T₂) ∧ r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set X) ⊓ L) := by
  have hgn₁ := gnSetting_sup_of_normal hl.gn hLn
  have hg₁ := gnGood_sup_of_normal hSix hl.gn hl.good hl.comp hl.lift hLn
  by_cases h3 : (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T))) ≤
      gnImg (T.subgroupOf (L ⊔ T))
        (Subgroup.normalizer ((T₂.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)))
  · exact exists_rank_two_of_bad_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hl hLn h20
      (gnA_le_map_normalizer_two_of_le_gnImg_sup hl.gn hl.good hl.comp hl.lift hLn hg₁ h3) hbad
  have hl₁ := liftCtxGen_subgroupOf hl hLn le_sup_right le_sup_left hgn₁ hg₁ h3
  haveI := hLn
  have hLn₁ : (L.subgroupOf (L ⊔ T)).Normal := Subgroup.normal_subgroupOf
  have h20₁ : CFSG.Open.pRank 3 (L.subgroupOf (L ⊔ T)) < 3 := by
    refine lt_of_le_of_lt ?_ h20
    have h1 := CFSG.SectionRank.pRank_le_map (show 1 < 3 by norm_num) (L ⊔ T).subtype
      (L ⊔ T).subtype_injective (L.subgroupOf (L ⊔ T))
    rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_left] at h1
  have hq : CFSG.Open.IsQuasisimple ↥(L.map (toStar T)) := by
    rw [hl.lift.2]
    exact hl.comp.1.2.2
  have hbad₁ : ¬ Small1522 ↥((L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) := by
    intro hs
    apply hbad
    rw [← hl.lift.2]
    exact small1522_map_toStar_of_small1522_subgroupOf le_sup_right le_sup_left hLn hq hs
  obtain ⟨Ti, r, hTi, hr, hr2, hrk⟩ := exists_rank_two_of_bad_gen hT hKSMAlt hKSMOdd hKSMU4
    hKSML3 k517_4b hl₁ hLn₁ h20₁
    (gnA_le_map_normalizer_two_of_sup_eq_top hgn₁ hg₁ hl₁.lift hLn₁ (sup_subgroupOf_sup_eq_top L T))
    hbad₁
  have hback : ∀ U : Subgroup X, U ≤ T → 2 ≤ CFSG.Open.pRank r
      (Subgroup.normalizer ((U.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)) ⊓
        L.subgroupOf (L ⊔ T)) →
      2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (U : Set X) ⊓ L) := by
    intro U hU hU2
    refine hU2.trans ((CFSG.SectionRank.pRank_le_map hr.one_lt (L ⊔ T).subtype
      (L ⊔ T).subtype_injective _).trans (CFSG.SectionRank.pRank_mono hr.one_lt ?_))
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxL⟩ := Subgroup.mem_inf.mp hx
    rw [← Subgroup.subgroupOf_normalizer_eq (hU.trans le_sup_right)] at hxN
    exact Subgroup.mem_inf.mpr ⟨hxN, Subgroup.mem_subgroupOf.mp hxL⟩
  rcases hTi with rfl | rfl
  · exact ⟨T₁, r, Or.inl rfl, hr, hr2, hback T₁ (hl.good.pair.le_center.trans
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self T)) hrk⟩
  · exact ⟨T₂, r, Or.inr rfl, hr, hr2, hback T₂ hl.good.pair.le₂ hrk⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
