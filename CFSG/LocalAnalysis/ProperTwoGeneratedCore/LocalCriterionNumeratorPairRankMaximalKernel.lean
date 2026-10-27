module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.TwoRankLowerBound.Helpers
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} [Group G]

@[expose] def numeratorPairRankPointClass (H : Subgroup G) (z w : G) : Set G :=
  involutionPointClass z ∩ (H : Set G) ∩
    (Subgroup.centralizer ({w} : Set G) : Set G)

theorem numeratorPairRankPointClass_normalized (H : Subgroup G) (z w : G) :
    H ⊓ Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer (numeratorPairRankPointClass H z w) := by
  apply Subgroup.le_set_normalizer_iff.mpr
  intro a ha x hx
  refine ⟨⟨?_, H.mul_mem (H.mul_mem ha.1 hx.1.2) (H.inv_mem ha.1)⟩, ?_⟩
  · simpa only [rightConjugateElem, inv_inv] using
      pointClass_right_conjugate_mem hx.1.1 a⁻¹
  · exact (Subgroup.mem_normalizer_iff.mp
      (commute_normalizes_centralizer a w
        (Subgroup.mem_centralizer_singleton_iff.mp ha.2)) x).mp hx.2

theorem numeratorPairRank_opposite_normalized (I U : Subgroup G) (t : G)
    (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (htI : t ∈ Subgroup.normalizer (I : Set G)) :
    I ≤ Subgroup.normalizer (U.map (MulAut.conj t).toMonoidHom : Set G) := by
  intro a ha
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hta : t⁻¹ * a * t ∈ I := (Subgroup.mem_normalizer_iff''.mp htI a).mp ha
  have hU : U.map (MulAut.conj (t⁻¹ * a * t)).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hIU hta)
  rw [Subgroup.map_map]
  change U.map ((MulAut.conj a).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
    U.map (MulAut.conj t).toMonoidHom
  have hmaps : (MulAut.conj a).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj (t⁻¹ * a * t)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hmaps, ← Subgroup.map_map, hU]

theorem numeratorPairRank_flip_normalizes_pair {Ω : Type v} [MulAction G Ω]
    (alpha beta : Ω) (t : G) (ht : orderOf t = 2) (hflip : t • alpha = beta) :
    t ∈ Subgroup.normalizer
      ((MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta).map
      (MulAut.conj t).toMonoidHom = MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    hflip, involution_flips_pair ht hflip, inf_comm]

variable [Finite G]

theorem original_pair_generated_maximal_point_class_kernel_rank_one
    {Ω : Type v} [MulAction G Ω] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (alpha beta : Ω) (hab : alpha ≠ beta)
    (z : G) (hz : orderOf z = 2)
    (hzfix : z • alpha = alpha)
    (hunique : ∀ omega : Ω, z • omega = omega → omega = alpha)
    (t : G) (htclass : t ∈ involutionPointClass z) (hflip : t • alpha = beta)
    (u : G) (hu : orderOf u = 2)
    (huB : u ∈ MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta)
    (huz : Commute u z) (hut : Commute u t)
    (hgen :
      Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
        (CFSG.oddCore (show Subgroup G from
          MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta)).map
          (MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta).subtype = ⊤)
    (hmax : ∀ w : G,
      w ∈ MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta →
      orderOf w = 2 → Commute w z → Commute w t →
      numeratorPairRankPointClass (MulAction.stabilizer G alpha) z u ⊆
        numeratorPairRankPointClass (MulAction.stabilizer G alpha) z w →
      numeratorPairRankPointClass (MulAction.stabilizer G alpha) z w =
        numeratorPairRankPointClass (MulAction.stabilizer G alpha) z u) :
    twoRank (Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z u : Set G) : Subgroup G) = 1 := by
  let H := MulAction.stabilizer G alpha
  let B := H ⊓ MulAction.stabilizer G beta
  let I := (CFSG.oddCore B).map B.subtype
  let Y := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let C := Y ⊓ Subgroup.centralizer (L : Set G)
  have ht : orderOf t = 2 := order_two_of_mem_pointClass hz htclass
  have hzL : z ∈ L := Subgroup.subset_closure
    ⟨distinguished_mem_pointClass z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq⟩
  have htL : t ∈ L := Subgroup.subset_closure
    ⟨htclass, Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq⟩
  have hLY : L ≤ Y := localInvolutionPointHull_le_centralizer z u
  have huC : u ∈ C := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLY hl)
  have hCB : C ≤ B := by
    intro c hc
    have hcz : Commute c z :=
      (Subgroup.mem_centralizer_iff.mp hc.2 z hzL).symm
    have hct : Commute c t :=
      (Subgroup.mem_centralizer_iff.mp hc.2 t htL).symm
    have hca : c • alpha = alpha := by
      apply hunique
      rw [← mul_smul, ← hcz.eq, mul_smul, hzfix]
    refine ⟨hca, ?_⟩
    change c • beta = beta
    rw [← hflip, ← mul_smul, hct.eq, mul_smul, hca]
  have hYproper : Y ≠ ⊤ := by
    intro htop
    have hucenter : u ∈ Subgroup.center G :=
      Subgroup.centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton u)
    rw [center_eq_bot_of_nonabelian_simple G hnonab] at hucenter
    exact (orderOf_eq_prime_iff.mp hu).2 (Subgroup.mem_bot.mp hucenter)
  have hIodd : Odd (Nat.card I) := by
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card B
  have hIB : I ≤ B := Subgroup.map_subtype_le _
  have htI : t ∈ Subgroup.normalizer (I : Set G) :=
    normalizer_normalizes_oddCore_image B
      (numeratorPairRank_flip_normalizes_pair alpha beta t ht hflip)
  have hnofour : ∀ V : Subgroup C, IsElemAbelian 2 V → Nat.card V ≠ 4 := by
    intro V _hV hVcard
    obtain ⟨v, hvone, hvu⟩ : ∃ v : V, ((v : C) : G) ≠ 1 ∧ ((v : C) : G) ≠ u := by
      by_contra hnone
      push Not at hnone
      have hcases : ∀ v : V, ((v : C) : G) = 1 ∨ ((v : C) : G) = u := by
        intro v
        by_cases hv : ((v : C) : G) = 1
        · exact Or.inl hv
        · exact Or.inr (hnone v hv)
      let f : V → ({(1 : G), u} : Set G) := fun v => ⟨v, hcases v⟩
      have hfinj : Function.Injective f := by
        intro a b heq
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : ({(1 : G), u} : Set G) => (x : G)) heq
      have hcardtwo : Nat.card ({(1 : G), u} : Set G) = 2 := by
        rw [Nat.card_coe_set_eq, Set.ncard_pair (orderOf_eq_prime_iff.mp hu).2.symm]
      have hbound := Nat.card_le_card_of_injective f hfinj
      rw [hcardtwo, hVcard] at hbound
      omega
    let vG : G := ((v : C) : G)
    have hvC : vG ∈ C := (v : C).property
    have hvsq : (v : C) ^ 2 = 1 := _hV.2 (v : C) v.property
    have hv : orderOf vG = 2 := orderOf_eq_prime_iff.mpr
      ⟨by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
          congrArg (fun x : C => (x : G)) hvsq, hvone⟩
    have huv : Commute u vG :=
      (Subgroup.mem_centralizer_singleton_iff.mp hvC.1).symm
    let W := denominatorFourGroup u vG
    obtain ⟨hW, _hWcard, _hWcases⟩ := commuting_distinct_involutions_four_group hu hv huv hvu
    rw [← denominatorFourGroup_eq] at hW
    have hWC : W ≤ C := by
      change denominatorFourGroup u vG ≤ C
      rw [denominatorFourGroup_eq]
      exact sup_le (Subgroup.zpowers_le.mpr huC) (Subgroup.zpowers_le.mpr hvC)
    have hWI : W ≤ Subgroup.normalizer (I : Set G) := by
      intro w hw
      exact normalizer_normalizes_oddCore_image B (B.le_normalizer (hCB (hWC hw)))
    have hCI : ∀ w ∈ W, w ≠ 1 → I ⊓ Subgroup.centralizer ({w} : Set G) ≤
        Subgroup.normalizer (numeratorPairRankPointClass H z u) := by
      intro w hw hwone
      have hwC := hWC hw
      have hwz : Commute w z :=
        (Subgroup.mem_centralizer_iff.mp hwC.2 z hzL).symm
      have hwt : Commute w t :=
        (Subgroup.mem_centralizer_iff.mp hwC.2 t htL).symm
      have hw : orderOf w = 2 := orderOf_eq_prime_iff.mpr ⟨hW.2 w hw, hwone⟩
      have hsubset : numeratorPairRankPointClass H z u ⊆
          numeratorPairRankPointClass H z w := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact Subgroup.mem_centralizer_iff.mp hwC.2 x
          (Subgroup.subset_closure ⟨hx.1.1, hx.2⟩)
      have hdelta := hmax w (hCB hwC) hw hwz hwt hsubset
      have hN : I ⊓ Subgroup.centralizer ({w} : Set G) ≤
          Subgroup.normalizer (numeratorPairRankPointClass H z w) :=
        (inf_le_inf (hIB.trans inf_le_left) le_rfl).trans
          (numeratorPairRankPointClass_normalized H z w)
      rwa [hdelta] at hN
    have huW : u ∈ W := Subgroup.subset_closure (Set.mem_insert u {vG})
    have hvW : vG ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem u (Set.mem_singleton vG))
    have huvone : u * vG ≠ 1 := by
      intro heq
      exact hvu (by
        have heq' := mul_eq_one_iff_eq_inv.mp heq
        rw [inv_eq_self_of_orderOf_eq_two hv] at heq'
        exact heq'.symm)
    have hIN : I ≤ Subgroup.normalizer (numeratorPairRankPointClass H z u) := by
      rw [four_group_odd_centralizer_generation I u vG hu hv huv hvu.symm hIodd hWI]
      exact sup_le (sup_le (hCI u huW (orderOf_eq_prime_iff.mp hu).2)
        (hCI vG hvW hvone)) (hCI (u * vG) (W.mul_mem huW hvW) huvone)
    let U := Subgroup.closure (numeratorPairRankPointClass H z u)
    let Ut := U.map (MulAut.conj t).toMonoidHom
    let P := U ⊔ Ut
    have hIU : I ≤ Subgroup.normalizer (U : Set G) :=
      hIN.trans (Subgroup.normalizer_le_normalizer_closure _)
    have hIUt : I ≤ Subgroup.normalizer (Ut : Set G) :=
      numeratorPairRank_opposite_normalized I U t hIU htI
    have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
      (le_inf hIU hIUt).trans (Subgroup.inf_normalizer_le_normalizer_sup U Ut)
    have hUL : U ≤ L := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      exact Subgroup.subset_closure ⟨hx.1.1, hx.2⟩
    have hUtL : Ut ≤ L := by
      rintro x ⟨a, ha, rfl⟩
      exact L.mul_mem (L.mul_mem htL (hUL ha)) (L.inv_mem htL)
    have hPL : P ≤ L := sup_le hUL hUtL
    have hzU : z ∈ U := Subgroup.subset_closure
      ⟨⟨distinguished_mem_pointClass z, hzfix⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq⟩
    have hzP : z ∈ P := (show U ≤ P from le_sup_left) hzU
    have htUt : Ut.map (MulAut.conj t).toMonoidHom = U := by
      rw [Subgroup.map_map]
      have htwice : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          MonoidHom.id G := by
        ext x
        change t * (t * x * t⁻¹) * t⁻¹ = x
        calc
          _ = (t * t) * x * (t * t)⁻¹ := by group
          _ = x := by
            rw [show t * t = 1 from (by simpa only [pow_two] using
              (orderOf_eq_prime_iff.mp ht).1), inv_one, one_mul, mul_one]
      rw [htwice, Subgroup.map_id]
    have htP : t ∈ Subgroup.normalizer (P : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      change (U ⊔ Ut).map (MulAut.conj t).toMonoidHom = U ⊔ Ut
      rw [Subgroup.map_sup, htUt]
      exact sup_comm Ut U
    have hGnormal : (⊤ : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := by
      rw [← hgen]
      exact sup_le (sup_le (Subgroup.zpowers_le.mpr (P.le_normalizer hzP))
        (Subgroup.zpowers_le.mpr htP)) hIP
    let : P.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hGnormal)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hPbot | hPtop
    · rw [hPbot] at hzP
      have hzOne : z = 1 := Subgroup.mem_bot.mp hzP
      exact hab (hunique beta (by rw [hzOne, one_smul])).symm
    · exact hYproper (top_le_iff.mp (hPtop ▸ hPL.trans hLY))
  have hupper := twoRank_le_one_of_no_four_group hnofour
  let uBC : ↥(B ⊓ C : Subgroup G) := ⟨u, huB, huC⟩
  have huorder : orderOf uBC = 2 := (Subgroup.orderOf_coe uBC).symm.trans hu
  have hlower := le_twoRank_of_elementary ↥(B ⊓ C : Subgroup G) (Subgroup.zpowers uBC)
    (involution_zpowers_elementary uBC huorder) 1
    (by simpa only [pow_one] using (Nat.card_zpowers uBC).trans huorder)
  have hBC : B ⊓ C = C := inf_eq_right.mpr hCB
  rw [hBC] at hlower
  exact Nat.le_antisymm hupper hlower

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
