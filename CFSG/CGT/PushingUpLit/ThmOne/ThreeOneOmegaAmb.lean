module

public import CFSG.CGT.PushingUpLit.ThmOne.AmbKSharp

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.SixThree

variable {L : Type} [Group L] [Finite L]

theorem exists_embedding_of_isSylowOf (hA : AschbacherEmbeddingAmbK') (hK : CFSG.IsKGroup L)
    (hchar : IsCharacteristicP 2 L) {Y R : Subgroup L} (hY : InClassX ↥Y)
    (hQY : pCore 2 L ≤ centralizerModCore Y) (hR : IsSylowOf 2 R (centralizerModCore Y))
    (hYR : Y ≤ Subgroup.normalizer (R : Set L))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set L))).IsSubnormal)
    (hns : ¬ Y.IsSubnormal) :
    Subgroup.centralizer (omegaOneCenterIn (pCore 2 L) : Set L) ≤ centralizerModCore Y ∧
      ¬ Y ≤ Subgroup.centralizer (omegaOneCenterIn (pCore 2 L) : Set L) ∧
      ∃ D : Subgroup L, Y ≤ D ∧ D.IsSubnormal ∧
        Subgroup.centralizer (omegaOneCenterIn (pCore 2 L) : Set L) ≤
          Subgroup.normalizer (D : Set L) ∧
        IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (omegaOneCenterIn (pCore 2 L) : Set L)) ∧
        ((InClassX ↥D ∧ ⁅oTwoIn D, D⁆ ≤ omegaOneCenterIn (pCore 2 L) ∧ ArrowNat Y D) ∨
          OmegaFourOutcomeSharp (omegaOneCenterIn (pCore 2 L)) Y D) := by
  have hQ2 : IsPGroup 2 (pCore 2 L) := pCore_isPGroup
  have hchar' : Subgroup.centralizer ((pCore 2 L : Subgroup L) : Set L) ≤ pCore 2 L := hchar
  have hmax : ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N ≤ pCore 2 L := fun N hN hp =>
    le_sSup ⟨hN, hp⟩
  have hVn : (omegaOneCenterIn (pCore 2 L)).Normal := normal_omegaOneCenterIn (pCore 2 L)
  obtain ⟨hQU, -, hUV, hnot⟩ := step_two hY.1 hQ2 hchar' hQY
  have hCC : Subgroup.centralizer (omegaOneCenterIn (pCore 2 L) : Set L) ≤
      centralizerModCore Y :=
    step_three (SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq) hQ2 hchar' hmax
      (fun g hg => (hQY hg).1) (hQU.le.trans hUV)
  refine ⟨hCC, hnot, ?_⟩
  set V := omegaOneCenterIn (pCore 2 L) with hV
  have hCY : Subgroup.centralizer (V : Set L) ≤ Subgroup.normalizer (Y : Set L) :=
    fun g hg => (hCC hg).1
  have hsubC := isSubnormal_normalizer_sup hYR hsub hCY
  have hRC : ¬ R ≤ Subgroup.centralizer (V : Set L) := by
    intro hRC
    have hRC' : IsSylowOf 2 R (Subgroup.centralizer (V : Set L)) := isSylowOf_of_le hR hRC hCC
    have hfr : Subgroup.normalizer (R : Set L) ⊔ Subgroup.centralizer (V : Set L) = ⊤ :=
      eq_top_iff.mpr fun g _ => le_normalizer_sup_of_isSylowOf hRC'
        (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g)
    rw [hfr] at hsubC
    exact hns (isSubnormal_of_subgroupOf_top hsubC)
  have hRRC : IsSylowOf 2 R (R ⊔ Subgroup.centralizer (V : Set L)) :=
    isSylowOf_of_le hR le_sup_left (sup_le hR.1 hCC)
  have hN : Subgroup.normalizer ((R ⊔ Subgroup.centralizer (V : Set L) : Subgroup L) : Set L) =
      Subgroup.normalizer (R : Set L) ⊔ Subgroup.centralizer (V : Set L) := by
    refine le_antisymm (fun g hg => ?_) (sup_le ?_ ?_)
    · exact sup_le le_sup_left (sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)
        (le_normalizer_sup_of_isSylowOf hRRC hg)
    · refine le_trans (le_inf le_rfl ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
      rw [Subgroup.normalizer_eq_top (Subgroup.centralizer (V : Set L))]
      exact le_top
    · exact le_sup_right.trans Subgroup.le_normalizer
  have hYN : Y ≤ Subgroup.normalizer
      ((R ⊔ Subgroup.centralizer (V : Set L) : Subgroup L) : Set L) := by
    rw [hN]
    exact hYR.trans le_sup_left
  have hsub' : (Y.subgroupOf (Subgroup.normalizer
      ((R ⊔ Subgroup.centralizer (V : Set L) : Subgroup L) : Set L))).IsSubnormal := by
    rw [hN]
    exact hsubC
  exact hA L hK hchar Y V hY hVn (isElementaryAbelian_omegaOneCenterIn _) hnot
    ⟨R, hR.2.1, hRC, hYN, hsub'⟩

theorem exists_embedding_of_isSylowOf_inf {G : Type} [Group G] [Finite G]
    (hA : AschbacherEmbeddingAmbK') {H Y R : Subgroup G} (hK : CFSG.IsKGroup ↥H)
    (hchar : IsCharacteristicP 2 ↥H) (hY : InClassX ↥Y) (hYH : Y ≤ H)
    (hQY : oTwoIn H ≤ centralizerModCore Y) (hR : IsSylowOf 2 R (centralizerModCore Y ⊓ H))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set G) ⊓ H)).IsSubnormal)
    (hns : ¬ (Y.subgroupOf H).IsSubnormal) :
    Subgroup.centralizer (omegaOneCenterIn (pCore 2 ↥H) : Set ↥H) ≤
        centralizerModCore (Y.subgroupOf H) ∧
      ¬ Y.subgroupOf H ≤ Subgroup.centralizer (omegaOneCenterIn (pCore 2 ↥H) : Set ↥H) ∧
      ∃ D : Subgroup ↥H, Y.subgroupOf H ≤ D ∧ D.IsSubnormal ∧
        Subgroup.centralizer (omegaOneCenterIn (pCore 2 ↥H) : Set ↥H) ≤
          Subgroup.normalizer (D : Set ↥H) ∧
        IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (omegaOneCenterIn (pCore 2 ↥H) : Set ↥H)) ∧
        ((InClassX ↥D ∧ ⁅oTwoIn D, D⁆ ≤ omegaOneCenterIn (pCore 2 ↥H) ∧
            ArrowNat (Y.subgroupOf H) D) ∨
          OmegaFourOutcomeSharp (omegaOneCenterIn (pCore 2 ↥H)) (Y.subgroupOf H) D) := by
  have hRH : R ≤ H := hR.1.trans inf_le_right
  have hQY' : pCore 2 ↥H ≤ centralizerModCore (Y.subgroupOf H) := by
    rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
      map_centralizerModCore_subgroupOf hYH, ← oTwoIn_eq_map]
    exact le_inf hQY (oTwoIn_le H)
  obtain ⟨hYR', hsub'⟩ := (EightOneRel.sylowClause_subgroupOf_iff hYH hRH).mpr ⟨hYR, hsub⟩
  exact exists_embedding_of_isSylowOf hA hK hchar ((inClassX_subgroupOf_iff hYH).mpr hY) hQY'
    ((EightOneRel.isSylowOf_subgroupOf_iff hYH hRH).mpr hR) hYR' hsub' hns

end CFSG.CGT.PushingUpLit.ThmOne
