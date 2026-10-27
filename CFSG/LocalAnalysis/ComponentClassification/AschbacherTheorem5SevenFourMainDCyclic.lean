module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainInner

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace FieldHyps

variable {t g : G}

theorem false_of_cyclic_four (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) (i : Fin 2) {R : Subgroup G}
    (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.centralizer ({t} : Set G)))
    (hRc : IsCyclic R) (hR4 : Nat.card R = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set ι := quotientEmbedding D
  have hι := quotientEmbedding_injective D
  set t' : H := ⟨t, hF.mem⟩
  have ht' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact hF.two
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hRH : R ≤ H := hR.le.trans (inf_le_left.trans hAH)
  have hX : (Abar i).map ι = bar D A := map_quotientEmbedding D (Abar i)
  have hsemi : aschbacherThm5IsSemisimple ((Abar i).map ι) :=
    isSemisimple_map_of_injective ι hι (Abar i) (hC.hyp.hsemisimple i)
  have htN : toBar D t' ∈
      Subgroup.normalizer (((Abar i).map ι : Subgroup (Bar D)) : Set (Bar D)) := by
    rw [hX]
    have htA : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hF.norm i))
    exact bar_le_normalizer htA hAH (toBar_mem_bar D (Subgroup.mem_zpowers t))
  have ht2 : toBar D t' ^ 2 = 1 := by
    rw [← map_pow]
    have : t' ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hF.two]; exact pow_orderOf_eq_one t)
    rw [this, map_one]
  have hCbar : Subgroup.centralizer ({toBar D t'} : Set (Bar D)) =
      bar D (Subgroup.centralizer ({t} : Set G)) := by
    rw [centralizer_toBar_eq t' ht', bar]
    congr 1
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  have hXC : (Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D)) =
      bar D (A ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [hX, hCbar, inf_comm (bar D A), inf_comm A,
      bar_inf_of_core_le (core_le_preimage D (Abar i))]
  have hRbar : IsSylowOf 2 (bar D R)
      ((Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D))) := by
    rw [hXC]
    exact isSylowOf_bar hR (inf_le_left.trans hAH)
  have hP3 : ∃ P : Sylow 2 ↥((Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D))),
      IsCyclic (P : Subgroup ↥((Abar i).map ι ⊓
        Subgroup.centralizer ({toBar D t'} : Set (Bar D)))) ∧ Nat.card P = 4 := by
    obtain ⟨P, hP⟩ := hRbar
    have hcardR : Nat.card (bar D R) = 4 := by
      rw [card_bar_of_isPGroup hR.isPGroup hRH, hR4]
    have hcycR : IsCyclic (bar D R) := by
      have hRs : IsCyclic (R.subgroupOf H) :=
        isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hRH).symm.surjective
      exact isCyclic_of_surjective ((toBar D).subgroupMap (R.subgroupOf H))
        ((toBar D).subgroupMap_surjective _)
    let K := (Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D))
    let e := ((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
    refine ⟨P, ?_, ?_⟩
    · exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    · rw [Nat.card_congr e.toEquiv]
      exact hcardR
  have h37 := AschbacherKnownGroup.lemma_3_7 hin.knownGroups (Bar D) ((Abar i).map ι)
    (toBar D t') hsemi htN ht2 hP3
  have hrank : 2 ≤ CFSG.Open.pRank 2 (Abar i) :=
    (hF.two_le_pRank hin hC i).trans (pRank_preimage_le _)
  have hrankmap := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two ι hι (Abar i)
  omega

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
