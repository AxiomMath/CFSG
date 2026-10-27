module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.SignalizerFunctor.Helpers
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem normalizer_normalizes_oddCore_image (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (((oddCore D).map D.subtype : Subgroup G) : Set G) := by
  intro s hs
  let phi : MulAut D := D.normalizerMonoidHom ⟨s, hs⟩
  have hhom : (MulAut.conj s).toMonoidHom.comp D.subtype =
      D.subtype.comp phi.toMonoidHom := by
    ext d
    rfl
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change ((oddCore D).map D.subtype).map (MulAut.conj s).toMonoidHom = _
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map]
  have hphi : (oddCore D).map phi.toMonoidHom = oddCore D :=
    CFSG.ComponentClassification.OddCore.char_invariant phi
  rw [hphi]

theorem commute_normalizes_centralizer (s t : G) (hst : Commute s t) :
    s ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  have hN : Subgroup.normalizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer ({t} : Set G))).mp inferInstance
  apply hN
  rw [Subgroup.normalizer_singleton]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hst.eq

theorem denominatorFourGroup_eq (u t : G) :
    denominatorFourGroup u t = Subgroup.zpowers u ⊔ Subgroup.zpowers t := by
  apply le_antisymm
  · change Subgroup.closure ({u, t} : Set G) ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers t
    apply (Subgroup.closure_le _).mpr
    intro s hs
    rcases Set.mem_insert_iff.mp hs with hs | hs
    · rw [hs]
      exact (show Subgroup.zpowers u ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers t from le_sup_left) (Subgroup.mem_zpowers u)
    · have heq : s = t := hs
      subst s
      exact (show Subgroup.zpowers t ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers t from le_sup_right) (Subgroup.mem_zpowers t)
  · apply sup_le
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

variable [Finite G]

theorem four_group_odd_centralizer_generation (J : Subgroup G) (u t : G)
    (hu : orderOf u = 2) (ht : orderOf t = 2) (hut : Commute u t) (hne : u ≠ t)
    (hodd : Odd (Nat.card J))
    (hJN : denominatorFourGroup u t ≤ Subgroup.normalizer (J : Set G)) :
    J = (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({u * t} : Set G)) := by
  let A := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  obtain ⟨hA, hcard, hcases⟩ := commuting_distinct_involutions_four_group
    hu ht hut (Ne.symm hne)
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := by
    rwa [denominatorFourGroup_eq] at hJN
  apply le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  conv_lhs => rw [← elementary_abelian_centralizer_generation 2 1 Nat.prime_two A J hA
    (by simpa using hcard.ge) hAN (Nat.coprime_two_left.mpr hodd)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hUcard : Nat.card U = 2 := by simpa using hU.2
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by simp only [hUcard, dvd_refl])
  have hsG : orderOf (s : G) = 2 := (Subgroup.orderOf_coe s).trans hs
  have hsne : (s : G) ≠ 1 := by intro heq; simp [heq] at hsG
  have hCs : Subgroup.centralizer (U : Set G) ≤
      Subgroup.centralizer ({(s : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.property)
  have hinf : J ⊓ Subgroup.centralizer (U : Set G) ≤
      J ⊓ Subgroup.centralizer ({(s : G)} : Set G) := inf_le_inf_left J hCs
  rcases hcases s (hU.1 s.property) with hone | hu' | ht' | hv'
  · exact False.elim (hsne hone)
  · intro j hj
    have hj' := hinf hj
    rw [hu'] at hj'
    apply (show J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      J ⊓ Subgroup.centralizer ({u * t} : Set G) from le_sup_left)
    exact (show J ⊓ Subgroup.centralizer ({u} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) from le_sup_left) hj'
  · intro j hj
    have hj' := hinf hj
    rw [ht'] at hj'
    apply (show J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      J ⊓ Subgroup.centralizer ({u * t} : Set G) from le_sup_left)
    exact (show J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) from le_sup_right) hj'
  · intro j hj
    have hj' := hinf hj
    rw [hv'] at hj'
    exact (show J ⊓ Subgroup.centralizer ({u * t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({u * t} : Set G)) from le_sup_right) hj'

theorem pair_hull_nontrivial_of_three_point_generation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H a t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (huz : Commute u z) (hunoncentral : u ∉ Subgroup.center G)
    (hthree : ThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      (oddCore (show Subgroup G from
        rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype = ⊤)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L) :
    L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) ≠ ⊥ := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let J := (oddCore D).map D.subtype
  let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
  let A := J ⊓ Subgroup.centralizer ({t} : Set G)
  have ht : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order htclass
  obtain ⟨hne, _, _, _, _⟩ := commuting_pair_product_geometry H a b hab u t hu ht hut huD hflip
  have hJD : J ≤ D := Subgroup.map_subtype_le _
  have hJodd : Odd (Nat.card J) := by
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card D
  have huJ := normalizer_normalizes_oddCore_image D (D.le_normalizer huD)
  have htJ := normalizer_normalizes_oddCore_image D (right_pair_flip_normalizes H t ht a b hflip)
  have huA : u ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huJ, commute_normalizes_centralizer u t hut⟩
  have hAN : A ≤ D := inf_le_left.trans hJD
  have hunique := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨gamma, hgamma, hgammaUnique⟩ := hunique t htclass
  have hga : gamma ≠ a := by
    intro heq
    rw [heq, hflip] at hgamma
    exact hab hgamma.symm
  have hgb : gamma ≠ b := by
    intro heq
    rw [heq, right_involution_flip_reverse H t ht a b hflip] at hgamma
    exact hab hgamma
  have hgamA : gamma ∈ pointFixedSet H A := by
    intro c hc
    have hct := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hconj : rightConjugateElem t c = t := by
      simp only [rightConjugateElem, mul_assoc]
      rw [← hct, inv_mul_cancel_left]
    have hf := point_right_fixed_conjugate hgamma c
    rw [hconj] at hf
    exact hgammaUnique _ hf
  have hAthree : 3 ≤ Nat.card (pointFixedSet H A) :=
    right_fixed_triple_card H A a b gamma hab hga hgb
      ((mem_pointFixedSet_iff H A a).mpr (hAN.trans inf_le_left))
      ((mem_pointFixedSet_iff H A b).mpr (hAN.trans inf_le_right)) hgamA
  have hAu : A ≤ Subgroup.centralizer ({u} : Set G) := hthree A hAN hAthree u hu huA
  intro hbot
  have hEcentral : E ≤ Subgroup.centralizer ({t} : Set G) := by
    obtain ⟨_, _, horbit⟩ := pair_hull_orbit_premises H a b t (u * t) ht hflip L hLC hLnormal htL
    intro e he
    have heq : rightConjugateElem t e * t = 1 := Subgroup.mem_bot.mp (hbot ▸ horbit e he)
    have hright : rightConjugateElem t e = t := by
      have heqt := mul_eq_one_iff_eq_inv.mp heq
      rwa [inv_eq_self_of_orderOf_eq_two ht] at heqt
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e⁻¹ * t * e = t at hright
    have he' := congrArg (fun s : G => e * s) hright
    simpa only [mul_assoc, mul_inv_cancel_left] using he'.symm
  have hJu : J ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := inf_le_right
  have hJt : J ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := hAu
  have hJv : J ⊓ Subgroup.centralizer ({u * t} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro j hj
    exact hAu ⟨hj.1, hEcentral ⟨hJD hj.1, hj.2⟩⟩
  have hVJ : denominatorFourGroup u t ≤ Subgroup.normalizer (J : Set G) := by
    rw [denominatorFourGroup_eq]
    exact sup_le (Subgroup.zpowers_le.mpr huJ) (Subgroup.zpowers_le.mpr htJ)
  have hJcentral : J ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [four_group_odd_centralizer_generation J u t hu ht hut hne hJodd hVJ]
    exact sup_le (sup_le hJu hJt) hJv
  have hGcentral : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← hgen]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq))) hJcentral
  apply hunoncentral
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hGcentral (Subgroup.mem_top g))

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
