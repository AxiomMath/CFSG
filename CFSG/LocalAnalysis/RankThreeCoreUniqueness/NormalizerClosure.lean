module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem gamma_rank_normalizer_le_overgroup
    (threshold prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (overgroup : Subgroup G) (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma threshold prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hinclusion : primeGroup ≤ overgroup) (hrank : threshold ≤ pRank prime primeGroup) :
    Subgroup.normalizer (primeGroup : Set G) ≤ overgroup := by
  obtain ⟨conjugator, hconjugated⟩ := pGroup_conjugate_into_sylow_within_overgroup prime hprime
    sylowGroup overgroup hsylow primeGroup hpGroup hinclusion
  let automorphism := MulAut.conj (conjugator : G)
  let conjugateGroup := primeGroup.map automorphism.toMonoidHom
  have hconjugateRank : threshold ≤ pRank prime conjugateGroup := by
    rw [pRank_map_automorphism prime hprime.one_lt]
    exact hrank
  have hnormalizer : Subgroup.normalizer (conjugateGroup : Set G) ≤ overgroup :=
    (gamma_normalizer_le threshold prime (sylowGroup : Subgroup G) conjugateGroup hconjugated
      hconjugateRank).trans hcore
  intro normalizingElement hnormalizing
  have himage : automorphism normalizingElement ∈ overgroup := by
    apply hnormalizer
    rw [← Subgroup.map_equiv_normalizer_eq primeGroup automorphism]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hnormalizing
  have hproduct := overgroup.mul_mem
    (overgroup.mul_mem (overgroup.inv_mem conjugator.property) himage) conjugator.property
  simpa [automorphism, MulAut.conj_apply, mul_assoc] using hproduct

theorem pGroup_le_of_rank_intersection_of_normalizer_closure
    (threshold prime : ℕ) (hprime : prime.Prime) (overgroup : Subgroup G)
    (hclosure : ∀ primeGroup : Subgroup G, IsPGroup prime primeGroup → primeGroup ≤ overgroup →
      threshold ≤ pRank prime primeGroup → Subgroup.normalizer (primeGroup : Set G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hrank : threshold ≤ pRank prime (primeGroup ⊓ overgroup)) : primeGroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent primeGroup := hpGroup.isNilpotent
  have hnormalizer := hclosure (primeGroup ⊓ overgroup) hpGroup.to_inf_left inf_le_right hrank
  have hself : Subgroup.normalizer ((primeGroup ⊓ overgroup).subgroupOf primeGroup : Set primeGroup) =
      (primeGroup ⊓ overgroup).subgroupOf primeGroup := by
    apply le_antisymm
    · rw [← Subgroup.subgroupOf_normalizer_eq (show primeGroup ⊓ overgroup ≤ primeGroup from inf_le_left)]
      intro element hnormalizing
      exact ⟨element.property, hnormalizer hnormalizing⟩
    · exact Subgroup.le_normalizer
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := primeGroup))) _ hself
  exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

theorem gamma_pGroup_le_of_large_intersection
    (threshold prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (overgroup : Subgroup G) (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma threshold prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hrank : threshold ≤ pRank prime (primeGroup ⊓ overgroup)) : primeGroup ≤ overgroup := by
  exact pGroup_le_of_rank_intersection_of_normalizer_closure threshold prime hprime overgroup
    (gamma_rank_normalizer_le_overgroup threshold prime hprime sylowGroup overgroup hsylow hcore)
    primeGroup hpGroup hrank

theorem aschCore_two_pGroup_le_of_rank_three_intersection
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (overgroup : Subgroup G) (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hrank : 3 ≤ pRank prime (primeGroup ⊓ overgroup)) : primeGroup ≤ overgroup := by
  exact pGroup_le_of_rank_intersection_of_normalizer_closure 3 prime hprime overgroup
    (aschCore_two_rank_three_normalizer_le_overgroup prime hprime sylowGroup overgroup hsylow hcore)
    primeGroup hpGroup hrank

theorem normalizer_closure_transporter_mem
    (threshold prime : ℕ) (hprime : prime.Prime) (overgroup : Subgroup G)
    (hclosure : ∀ primeGroup : Subgroup G, IsPGroup prime primeGroup → primeGroup ≤ overgroup →
      threshold ≤ pRank prime primeGroup → Subgroup.normalizer (primeGroup : Set G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hinclusion : primeGroup ≤ overgroup) (hrank : threshold ≤ pRank prime primeGroup)
    (transporter : G)
    (htransported : primeGroup.map (MulAut.conj transporter).toMonoidHom ≤ overgroup) :
    transporter ∈ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨sourceSylow, hsylowGroup⟩ := hpGroup.exists_le_sylow
  have hsource : (sourceSylow : Subgroup G) ≤ overgroup := by
    apply pGroup_le_of_rank_intersection_of_normalizer_closure threshold prime hprime overgroup
      hclosure (sourceSylow : Subgroup G) sourceSylow.isPGroup'
    exact hrank.trans (pRank_mono prime hprime.one_lt (le_inf hsylowGroup hinclusion))
  have htarget : ((transporter • sourceSylow : Sylow prime G) : Subgroup G) ≤ overgroup := by
    apply pGroup_le_of_rank_intersection_of_normalizer_closure threshold prime hprime overgroup
      hclosure _ (transporter • sourceSylow).isPGroup'
    have himageSylow : primeGroup.map (MulAut.conj transporter).toMonoidHom ≤
        ((transporter • sourceSylow : Sylow prime G) : Subgroup G) := by
      rw [sylow_conjugate_eq_map]
      exact Subgroup.map_mono hsylowGroup
    have himageRank : threshold ≤ pRank prime
        (primeGroup.map (MulAut.conj transporter).toMonoidHom) := by
      rwa [pRank_map_automorphism prime hprime.one_lt]
    exact himageRank.trans (pRank_mono prime hprime.one_lt (le_inf himageSylow htransported))
  obtain ⟨adjustment, hadjustment⟩ := MulAction.IsPretransitive.exists_smul_eq (M := overgroup)
    ((transporter • sourceSylow).subtype htarget) (sourceSylow.subtype hsource)
  rw [Sylow.smul_subtype htarget adjustment] at hadjustment
  have hnormalized : (adjustment : G) • (transporter • sourceSylow) = sourceSylow := by
    simpa only [Subgroup.smul_def] using Sylow.subtype_injective hadjustment
  have hnormalizer : Subgroup.normalizer (sourceSylow : Set G) ≤ overgroup :=
    hclosure _ sourceSylow.isPGroup' hsource
      (hrank.trans (pRank_mono prime hprime.one_lt hsylowGroup))
  have hproduct : (adjustment : G) * transporter ∈ overgroup := by
    apply hnormalizer
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rwa [mul_smul]
  simpa only [inv_mul_cancel_left] using
    overgroup.mul_mem (overgroup.inv_mem adjustment.property) hproduct

theorem normalizer_closure_conjugate_intersection_rank_lt
    (threshold prime : ℕ) (hprime : prime.Prime) (hthreshold : 0 < threshold)
    (overgroup : Subgroup G)
    (hclosure : ∀ primeGroup : Subgroup G, IsPGroup prime primeGroup → primeGroup ≤ overgroup →
      threshold ≤ pRank prime primeGroup → Subgroup.normalizer (primeGroup : Set G) ≤ overgroup)
    (conjugator : G) (houtside : conjugator ∉ overgroup) :
    pRank prime (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) < threshold := by
  by_contra hlarge
  have hrank : threshold ≤ pRank prime
      (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) := by omega
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime
    (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) (by omega)
  have helementaryRank : threshold ≤ pRank prime elementary := by
    apply hrank.trans
    unfold pRank
    exact le_csSup (pRank_set_bddAbove prime hprime.one_lt elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩
  have hinverseTransported : elementary.map (MulAut.conj conjugator⁻¹).toMonoidHom ≤ overgroup := by
    rintro element ⟨source, hsource, rfl⟩
    have hinverse := Subgroup.mem_map_equiv.mp (hinclusion hsource).2
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.conj_symm_apply]
      using hinverse
  have hinverseMember := normalizer_closure_transporter_mem threshold prime hprime overgroup hclosure
    elementary (elementary_isPGroup prime elementary helementary) (hinclusion.trans inf_le_left)
    helementaryRank conjugator⁻¹ hinverseTransported
  exact houtside (overgroup.inv_mem_iff.mp hinverseMember)

theorem gamma_conjugate_intersection_rank_lt
    (threshold prime : ℕ) (hprime : prime.Prime) (hthreshold : 0 < threshold)
    (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma threshold prime (sylowGroup : Subgroup G) ≤ overgroup)
    (conjugator : G) (houtside : conjugator ∉ overgroup) :
    pRank prime (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) < threshold := by
  exact normalizer_closure_conjugate_intersection_rank_lt threshold prime hprime hthreshold overgroup
    (gamma_rank_normalizer_le_overgroup threshold prime hprime sylowGroup overgroup hsylow hcore)
    conjugator houtside

theorem aschCore_two_conjugate_intersection_rank_lt_three
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (conjugator : G) (houtside : conjugator ∉ overgroup) :
    pRank prime (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) < 3 := by
  exact normalizer_closure_conjugate_intersection_rank_lt 3 prime hprime (by omega) overgroup
    (aschCore_two_rank_three_normalizer_le_overgroup prime hprime sylowGroup overgroup hsylow hcore)
    conjugator houtside

theorem selected_coreLocal_has_rank_three_normalizer_closure
    (hrank : evenRank G = 3) (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G) :
    ∃ maximalLocal : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧ pRank prime maximalLocal = 3 ∧
      Subgroup.normalizer (maximalLocal : Set G) = maximalLocal ∧
      (∀ primeGroup : Subgroup G, IsPGroup prime primeGroup → primeGroup ≤ maximalLocal →
        3 ≤ pRank prime primeGroup → Subgroup.normalizer (primeGroup : Set G) ≤ maximalLocal) ∧
      (∀ primeGroup : Subgroup G, IsPGroup prime primeGroup →
        3 ≤ pRank prime (primeGroup ⊓ maximalLocal) → primeGroup ≤ maximalLocal) ∧
      (∀ conjugator : G, conjugator ∉ maximalLocal →
        pRank prime (maximalLocal ⊓
          maximalLocal.map (MulAut.conj conjugator).toMonoidHom) < 3) := by
  obtain ⟨maximalLocal, hmaximal, hcore, _, hinclusion, _, hlocalRank⟩ :=
    selected_coreLocal_all_sylows_have_maximal_overgroup hrank hcoreLocal prime hselected sylowGroup
  have hprime := sigmaA_prime prime hselected
  refine ⟨maximalLocal, hmaximal, hcore, hinclusion, hlocalRank,
    maxTwoLocal_self_normalizing maximalLocal hmaximal, ?_, ?_, ?_⟩
  · exact aschCore_two_rank_three_normalizer_le_overgroup prime hprime sylowGroup maximalLocal
      hinclusion hcore
  · exact aschCore_two_pGroup_le_of_rank_three_intersection prime hprime sylowGroup maximalLocal
      hinclusion hcore
  · exact aschCore_two_conjugate_intersection_rank_lt_three prime hprime sylowGroup maximalLocal
      hinclusion hcore

end CFSG.RankThreeCoreUniqueness.Helpers
