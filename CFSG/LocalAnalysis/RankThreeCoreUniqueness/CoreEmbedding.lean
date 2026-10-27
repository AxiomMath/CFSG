module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem aschProduct_eq_of_abelian (ambient generator : Subgroup G)
    (hcommutative : IsMulCommutative ambient) (hinclusion : generator ≤ ambient) :
    generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G)) = ambient := by
  have hcentralizer : ambient ≤ Subgroup.centralizer (generator : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommutative).trans
      (Subgroup.centralizer_le hinclusion)
  rw [inf_eq_left.mpr hcentralizer, sup_eq_right.mpr hinclusion]

theorem sylow_conjugate_eq_map (prime : ℕ) (sylowGroup : Sylow prime G) (conjugator : G) :
    ((conjugator • sylowGroup : Sylow prime G) : Subgroup G) =
      (sylowGroup : Subgroup G).map (MulAut.conj conjugator).toMonoidHom := by
  apply SetLike.coe_injective
  change ((conjugator • sylowGroup : Sylow prime G) : Set G) = _
  rw [Sylow.coe_smul, Subgroup.coe_map]
  rfl

theorem conjugate_map_mul (subgroup : Subgroup G) (outer inner : G) :
    (subgroup.map (MulAut.conj inner).toMonoidHom).map (MulAut.conj outer).toMonoidHom =
      subgroup.map (MulAut.conj (outer * inner)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext element
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

variable [Finite G]

theorem aschCore_eq_gamma_of_abelian (threshold prime : ℕ) (ambient : Subgroup G)
    (hcommutative : IsMulCommutative ambient) (hrank : 3 ≤ pRank prime ambient) :
    rankThreeAschCore threshold prime ambient = rankThreeGamma threshold prime ambient := by
  apply le_antisymm (aschCore_le_gamma threshold prime ambient)
  apply (gamma_le_iff threshold prime ambient _).mpr
  intro generator hinclusion hgeneratorRank
  apply aschCore_normalizer_le threshold prime ambient generator hinclusion hgeneratorRank
  rw [aschProduct_eq_of_abelian ambient generator hcommutative hinclusion]
  exact hrank

theorem selected_abelian_coreLocal_all_sylows_have_full_core_overgroup
    (hrank : evenRank G = 3) (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G)
    (hcommutative : IsMulCommutative (sylowGroup : Subgroup G)) :
    ∃ maximalLocal : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      Subgroup.normalizer (sylowGroup : Set G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      pRank prime (sylowGroup : Subgroup G) = 3 ∧ pRank prime maximalLocal = 3 := by
  obtain ⟨maximalLocal, hmaximal, hcore, hnormalizer, hinclusion, hsylowRank, hlocalRank⟩ :=
    selected_coreLocal_all_sylows_have_maximal_overgroup hrank hcoreLocal prime hselected sylowGroup
  rw [aschCore_eq_gamma_of_abelian 2 prime (sylowGroup : Subgroup G) hcommutative
    (by omega)] at hcore
  exact ⟨maximalLocal, hmaximal, hcore, hnormalizer, hinclusion, hsylowRank, hlocalRank⟩

theorem abelian_sylow_transporter_mem_of_gamma_two_le (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (hcommutative : IsMulCommutative (sylowGroup : Subgroup G))
    (overgroup : Subgroup G) (hcore : rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (generator : Subgroup G) (hinclusion : generator ≤ (sylowGroup : Subgroup G))
    (hrank : 2 ≤ pRank prime generator) (transporter : G)
    (htransported : generator.map (MulAut.conj transporter).toMonoidHom ≤
      (sylowGroup : Subgroup G)) : transporter ∈ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let conjugation := (MulAut.conj transporter).toMonoidHom
  let conjugateGenerator := generator.map conjugation
  let centralizingGroup := Subgroup.centralizer (conjugateGenerator : Set G)
  have hconjugateRank : 2 ≤ pRank prime conjugateGenerator := by
    rw [← pRank_eq_of_subgroup_equiv prime hprime.one_lt generator conjugateGenerator
      (generator.equivMapOfInjective conjugation (MulAut.conj transporter).injective)]
    exact hrank
  have hcentralizerOvergroup : centralizingGroup ≤ overgroup :=
    (Subgroup.centralizer_le_normalizer _).trans
      ((gamma_normalizer_le 2 prime (sylowGroup : Subgroup G) conjugateGenerator
        htransported hconjugateRank).trans hcore)
  have hsylowCentralizer : (sylowGroup : Subgroup G) ≤ centralizingGroup :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommutative).trans
      (Subgroup.centralizer_le htransported)
  have hconjugateSylowCentralizer : ((transporter • sylowGroup : Sylow prime G) : Subgroup G) ≤
      centralizingGroup := by
    rw [sylow_conjugate_eq_map]
    have hcentralizing : (sylowGroup : Subgroup G) ≤ Subgroup.centralizer (generator : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommutative).trans
        (Subgroup.centralizer_le hinclusion)
    exact (Subgroup.map_mono hcentralizing).trans
      (Subgroup.map_centralizer_le_centralizer_image (generator : Set G) conjugation)
  obtain ⟨adjustment, hadjustment⟩ := MulAction.IsPretransitive.exists_smul_eq (M := centralizingGroup)
    ((transporter • sylowGroup).subtype hconjugateSylowCentralizer)
    (sylowGroup.subtype hsylowCentralizer)
  have hnormalized : (adjustment : G) • (transporter • sylowGroup) = sylowGroup := by
    rw [Sylow.smul_subtype hconjugateSylowCentralizer adjustment] at hadjustment
    simpa only [Subgroup.smul_def] using Sylow.subtype_injective hadjustment
  have hnormalizer : Subgroup.normalizer (sylowGroup : Set G) ≤ overgroup :=
    (gamma_normalizer_le 2 prime (sylowGroup : Subgroup G) (sylowGroup : Subgroup G) le_rfl
      (hrank.trans (pRank_mono prime hprime.one_lt hinclusion))).trans hcore
  have hproduct : (adjustment : G) * transporter ∈ overgroup := by
    apply hnormalizer
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rwa [mul_smul]
  have hadjustmentOvergroup : (adjustment : G) ∈ overgroup :=
    hcentralizerOvergroup adjustment.property
  simpa [← mul_assoc] using overgroup.mul_mem (overgroup.inv_mem hadjustmentOvergroup) hproduct

theorem pGroup_conjugate_into_sylow_within_overgroup (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup) (primeGroup : Subgroup G)
    (hpGroup : IsPGroup prime primeGroup) (hinclusion : primeGroup ≤ overgroup) :
    ∃ conjugator : overgroup,
      primeGroup.map (MulAut.conj (conjugator : G)).toMonoidHom ≤ (sylowGroup : Subgroup G) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hinternal : IsPGroup prime (primeGroup.subgroupOf overgroup) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  obtain ⟨internalSylow, hcontained⟩ := hinternal.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.IsPretransitive.exists_smul_eq (M := overgroup)
    internalSylow (sylowGroup.subtype hsylow)
  refine ⟨conjugator, ?_⟩
  rintro element ⟨source, hsource, rfl⟩
  let internalSource : overgroup := ⟨source, hinclusion hsource⟩
  have hinternalSource : internalSource ∈ internalSylow := hcontained hsource
  have hconjugateSource : (MulAut.conj conjugator) internalSource ∈
      ((conjugator • internalSylow : Sylow prime overgroup) : Subgroup overgroup) := by
    rw [sylow_conjugate_eq_map]
    exact Subgroup.mem_map_of_mem _ hinternalSource
  rw [hconjugator, Sylow.coe_subtype] at hconjugateSource
  exact hconjugateSource

theorem aschCore_two_rank_three_normalizer_le_overgroup
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hinclusion : primeGroup ≤ overgroup) (hrank : 3 ≤ pRank prime primeGroup) :
    Subgroup.normalizer (primeGroup : Set G) ≤ overgroup := by
  obtain ⟨conjugator, hconjugated⟩ := pGroup_conjugate_into_sylow_within_overgroup prime hprime
    sylowGroup overgroup hsylow primeGroup hpGroup hinclusion
  let conjugation := (MulAut.conj (conjugator : G)).toMonoidHom
  let conjugateGroup := primeGroup.map conjugation
  have hconjugateRank : 3 ≤ pRank prime conjugateGroup := by
    rw [← pRank_eq_of_subgroup_equiv prime hprime.one_lt primeGroup conjugateGroup
      (primeGroup.equivMapOfInjective conjugation (MulAut.conj (conjugator : G)).injective)]
    exact hrank
  have hnormalizer : Subgroup.normalizer (conjugateGroup : Set G) ≤ overgroup :=
    ((gamma_normalizer_le 3 prime (sylowGroup : Subgroup G) conjugateGroup hconjugated
      hconjugateRank).trans
      (gamma_three_le_aschCore_two prime hprime.one_lt (sylowGroup : Subgroup G))).trans hcore
  intro normalizingElement hnormalizing
  have hconjugateNormalizer : (MulAut.conj (conjugator : G)) normalizingElement ∈ overgroup := by
    apply hnormalizer
    rw [← Subgroup.map_equiv_normalizer_eq primeGroup (MulAut.conj (conjugator : G))]
    exact Subgroup.mem_map_of_mem conjugation hnormalizing
  have hproduct := overgroup.mul_mem
    (overgroup.mul_mem (overgroup.inv_mem conjugator.property) hconjugateNormalizer) conjugator.property
  simpa [MulAut.conj_apply, mul_assoc] using hproduct

theorem gamma_of_abelian_rank_three_le_aschCore (threshold prime : ℕ) (hprime : 1 < prime)
    (ambient abelianGroup : Subgroup G) (hinclusion : abelianGroup ≤ ambient)
    (hcommutative : IsMulCommutative abelianGroup) (hrank : 3 ≤ pRank prime abelianGroup) :
    rankThreeGamma threshold prime abelianGroup ≤ rankThreeAschCore threshold prime ambient := by
  rw [← aschCore_eq_gamma_of_abelian threshold prime abelianGroup hcommutative hrank]
  exact aschCore_mono_group prime hprime threshold hinclusion

theorem aschCore_two_abelian_rank_three_subcore_le_overgroup
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (abelianGroup : Subgroup G) (hpGroup : IsPGroup prime abelianGroup)
    (hinclusion : abelianGroup ≤ overgroup) (hcommutative : IsMulCommutative abelianGroup)
    (hrank : 3 ≤ pRank prime abelianGroup) : rankThreeGamma 2 prime abelianGroup ≤ overgroup := by
  obtain ⟨conjugator, hconjugated⟩ := pGroup_conjugate_into_sylow_within_overgroup prime hprime
    sylowGroup overgroup hsylow abelianGroup hpGroup hinclusion
  let automorphism := MulAut.conj (conjugator : G)
  let conjugateGroup := abelianGroup.map automorphism.toMonoidHom
  have hconjugateRank : 3 ≤ pRank prime conjugateGroup := by
    rw [← pRank_eq_of_subgroup_equiv prime hprime.one_lt abelianGroup conjugateGroup
      (abelianGroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective)]
    exact hrank
  have hconjugateCommutative : IsMulCommutative conjugateGroup := by
    apply (isMulCommutative_iff).mpr
    intro first second
    obtain ⟨sourceFirst, hsourceFirst⟩ :=
      (abelianGroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective).surjective first
    obtain ⟨sourceSecond, hsourceSecond⟩ :=
      (abelianGroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective).surjective second
    rw [← hsourceFirst, ← hsourceSecond, ← map_mul, ← map_mul]
    exact congrArg _ (isMulCommutative_iff.mp hcommutative sourceFirst sourceSecond)
  have hconjugateCore : rankThreeGamma 2 prime conjugateGroup ≤ overgroup :=
    (gamma_of_abelian_rank_three_le_aschCore 2 prime hprime.one_lt (sylowGroup : Subgroup G)
      conjugateGroup hconjugated hconjugateCommutative hconjugateRank).trans hcore
  apply (gamma_le_iff 2 prime abelianGroup overgroup).mpr
  intro generator hgenerator hgeneratorRank
  have hconjugateGeneratorRank : 2 ≤ pRank prime (generator.map automorphism.toMonoidHom) := by
    rw [← pRank_eq_of_subgroup_equiv prime hprime.one_lt generator _
      (generator.equivMapOfInjective automorphism.toMonoidHom automorphism.injective)]
    exact hgeneratorRank
  have hconjugateNormalizer : Subgroup.normalizer (generator.map automorphism.toMonoidHom : Set G) ≤
      overgroup :=
    (gamma_normalizer_le 2 prime conjugateGroup (generator.map automorphism.toMonoidHom)
      (Subgroup.map_mono hgenerator) hconjugateGeneratorRank).trans hconjugateCore
  intro normalizingElement hnormalizing
  have himage : automorphism normalizingElement ∈ overgroup := by
    apply hconjugateNormalizer
    rw [← Subgroup.map_equiv_normalizer_eq generator automorphism]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hnormalizing
  have hproduct := overgroup.mul_mem
    (overgroup.mul_mem (overgroup.inv_mem conjugator.property) himage) conjugator.property
  simpa [automorphism, MulAut.conj_apply, mul_assoc] using hproduct

theorem full_core_escape_has_exact_rank_two_obstruction
    (prime : ℕ) (hprime : 1 < prime) (ambient overgroup : Subgroup G)
    (hcore : rankThreeAschCore 2 prime ambient ≤ overgroup)
    (hescape : ¬ rankThreeGamma 2 prime ambient ≤ overgroup) :
    ∃ generator : Subgroup G, generator ≤ ambient ∧ pRank prime generator = 2 ∧
      pRank prime (generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G))) = 2 ∧
      pRank prime (ambient ⊓ Subgroup.centralizer (generator : Set G)) ≤ 2 ∧
      ¬ Subgroup.normalizer (generator : Set G) ≤ overgroup := by
  classical
  have hnormalizers := (gamma_le_iff 2 prime ambient overgroup).not.mp hescape
  push Not at hnormalizers
  obtain ⟨generator, hinclusion, hrank, hnormalizer⟩ := hnormalizers
  have hproductRank :
      pRank prime (generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G))) < 3 := by
    by_contra hlarge
    exact hnormalizer ((aschCore_normalizer_le 2 prime ambient generator hinclusion hrank
      (by omega)).trans hcore)
  have hgeneratorRank := pRank_mono prime hprime
    (le_sup_left : generator ≤ generator ⊔
      (ambient ⊓ Subgroup.centralizer (generator : Set G)))
  have hcentralizerRank := pRank_mono prime hprime
    (le_sup_right : ambient ⊓ Subgroup.centralizer (generator : Set G) ≤ generator ⊔
      (ambient ⊓ Subgroup.centralizer (generator : Set G)))
  exact ⟨generator, hinclusion, by omega, by omega, by omega, hnormalizer⟩

theorem escaping_normalizer_has_no_rank_three_abelian_extension
    (prime : ℕ) (hprime : 1 < prime) (ambient overgroup generator : Subgroup G)
    (hcore : rankThreeAschCore 2 prime ambient ≤ overgroup)
    (hrank : 2 ≤ pRank prime generator)
    (hescape : ¬ Subgroup.normalizer (generator : Set G) ≤ overgroup)
    (abelianGroup : Subgroup G) (hinclusion : abelianGroup ≤ ambient)
    (hcommutative : IsMulCommutative abelianGroup) (habRank : 3 ≤ pRank prime abelianGroup) :
    ¬ generator ≤ abelianGroup := by
  intro hextension
  exact hescape ((gamma_normalizer_le 2 prime abelianGroup generator hextension hrank).trans
    ((gamma_of_abelian_rank_three_le_aschCore 2 prime hprime ambient abelianGroup hinclusion
      hcommutative habRank).trans hcore))

theorem full_core_le_iff_exact_rank_two_normalizers_le
    (prime : ℕ) (hprime : 1 < prime) (ambient overgroup : Subgroup G)
    (hcore : rankThreeAschCore 2 prime ambient ≤ overgroup) :
    rankThreeGamma 2 prime ambient ≤ overgroup ↔
      ∀ generator : Subgroup G, generator ≤ ambient → pRank prime generator = 2 →
        pRank prime (generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G))) = 2 →
        Subgroup.normalizer (generator : Set G) ≤ overgroup := by
  constructor
  · intro hfull generator hinclusion hrank _
    exact (gamma_normalizer_le 2 prime ambient generator hinclusion (by omega)).trans hfull
  · intro hnormalizers
    by_contra hescape
    obtain ⟨generator, hinclusion, hrank, hproductRank, _, hnormalizer⟩ :=
      full_core_escape_has_exact_rank_two_obstruction prime hprime ambient overgroup hcore hescape
    exact hnormalizer (hnormalizers generator hinclusion hrank hproductRank)

theorem selected_full_core_escape_has_rank_two_obstruction
    (hrank : evenRank G = 3) (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G)
    (hfullNonlocal : ∀ localGroup : Subgroup G, IsTwoLocal localGroup →
      ¬ rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ localGroup) :
    ∃ maximalLocal generator : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧ pRank prime maximalLocal = 3 ∧
      generator ≤ (sylowGroup : Subgroup G) ∧ IsPGroup prime generator ∧
      pRank prime generator = 2 ∧
      pRank prime (generator ⊔ ((sylowGroup : Subgroup G) ⊓
        Subgroup.centralizer (generator : Set G))) = 2 ∧
      pRank prime ((sylowGroup : Subgroup G) ⊓ Subgroup.centralizer (generator : Set G)) ≤ 2 ∧
      ¬ Subgroup.normalizer (generator : Set G) ≤ maximalLocal := by
  obtain ⟨maximalLocal, hmaximal, hcore, _, hinclusion, _, hlocalRank⟩ :=
    selected_coreLocal_all_sylows_have_maximal_overgroup hrank hcoreLocal prime hselected sylowGroup
  obtain ⟨generator, hgenerator, hgeneratorRank, hproductRank, hcentralizerRank, hnormalizer⟩ :=
    full_core_escape_has_exact_rank_two_obstruction prime (sigmaA_prime prime hselected).one_lt
      (sylowGroup : Subgroup G) maximalLocal hcore (hfullNonlocal maximalLocal hmaximal.1)
  exact ⟨maximalLocal, generator, hmaximal, hcore, hinclusion, hlocalRank, hgenerator,
    sylowGroup.isPGroup'.to_le hgenerator, hgeneratorRank, hproductRank, hcentralizerRank,
    hnormalizer⟩

theorem abelian_sylow_transporter_mem_of_gamma_two_le_overgroup
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (hcommutative : IsMulCommutative (sylowGroup : Subgroup G)) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hinclusion : primeGroup ≤ overgroup) (hrank : 2 ≤ pRank prime primeGroup)
    (transporter : G)
    (htransported : primeGroup.map (MulAut.conj transporter).toMonoidHom ≤ overgroup) :
    transporter ∈ overgroup := by
  obtain ⟨sourceAdjustment, hsource⟩ := pGroup_conjugate_into_sylow_within_overgroup
    prime hprime sylowGroup overgroup hsylow primeGroup hpGroup hinclusion
  have himagePGroup := hpGroup.map (MulAut.conj transporter).toMonoidHom
  obtain ⟨targetAdjustment, htarget⟩ := pGroup_conjugate_into_sylow_within_overgroup
    prime hprime sylowGroup overgroup hsylow _ himagePGroup htransported
  let generator := primeGroup.map (MulAut.conj (sourceAdjustment : G)).toMonoidHom
  have hgeneratorRank : 2 ≤ pRank prime generator := by
    rw [← pRank_eq_of_subgroup_equiv prime hprime.one_lt primeGroup generator
      (primeGroup.equivMapOfInjective _ (MulAut.conj (sourceAdjustment : G)).injective)]
    exact hrank
  let adjustedTransporter := (targetAdjustment : G) * transporter * (sourceAdjustment : G)⁻¹
  have hadjusted : generator.map (MulAut.conj adjustedTransporter).toMonoidHom ≤
      (sylowGroup : Subgroup G) := by
    dsimp only [generator]
    rw [conjugate_map_mul]
    have hcancel : adjustedTransporter * (sourceAdjustment : G) =
        (targetAdjustment : G) * transporter := by
      dsimp only [adjustedTransporter]
      group
    rw [hcancel, ← conjugate_map_mul]
    exact htarget
  have hmember := abelian_sylow_transporter_mem_of_gamma_two_le prime hprime sylowGroup
    hcommutative overgroup hcore generator hsource hgeneratorRank adjustedTransporter hadjusted
  have hproduct := overgroup.mul_mem
    (overgroup.mul_mem (overgroup.inv_mem targetAdjustment.property) hmember) sourceAdjustment.property
  have hcancel : (targetAdjustment : G)⁻¹ * adjustedTransporter * (sourceAdjustment : G) =
      transporter := by
    dsimp only [adjustedTransporter]
    group
  rwa [hcancel] at hproduct

theorem abelian_sylow_gamma_two_conjugate_intersection_rank_lt_two
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (hcommutative : IsMulCommutative (sylowGroup : Subgroup G)) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (conjugator : G) (houtside : conjugator ∉ overgroup) :
    pRank prime (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) < 2 := by
  by_contra hlarge
  have hrank : 2 ≤ pRank prime
      (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) := by omega
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime
    (overgroup ⊓ overgroup.map (MulAut.conj conjugator).toMonoidHom) (by omega)
  have helementaryRank : 2 ≤ pRank prime elementary := by
    apply hrank.trans
    unfold pRank
    exact le_csSup (pRank_set_bddAbove prime hprime.one_lt elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩
  have hinverseTransported : elementary.map (MulAut.conj conjugator⁻¹).toMonoidHom ≤ overgroup := by
    rintro element ⟨source, hsource, rfl⟩
    have hsourceImage := (hinclusion hsource).2
    have hinverse := Subgroup.mem_map_equiv.mp hsourceImage
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.conj_symm_apply]
      using hinverse
  have hinverseMember := abelian_sylow_transporter_mem_of_gamma_two_le_overgroup prime hprime
    sylowGroup hcommutative overgroup hsylow hcore elementary (elementary_isPGroup prime elementary
      helementary) (hinclusion.trans inf_le_left) helementaryRank conjugator⁻¹ hinverseTransported
  exact houtside (overgroup.inv_mem_iff.mp hinverseMember)

theorem abelian_sylow_gamma_two_rank_two_normalizer_le
    (prime : ℕ) (hprime : prime.Prime) (sylowGroup : Sylow prime G)
    (hcommutative : IsMulCommutative (sylowGroup : Subgroup G)) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (primeGroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hinclusion : primeGroup ≤ overgroup) (hrank : 2 ≤ pRank prime primeGroup) :
    Subgroup.normalizer (primeGroup : Set G) ≤ overgroup := by
  intro normalizingElement hnormalizing
  apply abelian_sylow_transporter_mem_of_gamma_two_le_overgroup prime hprime sylowGroup
    hcommutative overgroup hsylow hcore primeGroup hpGroup hinclusion hrank normalizingElement
  change primeGroup.map (↑(MulAut.conj normalizingElement) : G →* G) ≤ overgroup
  rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalizing]
  exact hinclusion

theorem selected_abelian_coreLocal_has_rank_two_intersection_confinement
    (hrank : evenRank G = 3) (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G)
    (hcommutative : IsMulCommutative (sylowGroup : Subgroup G)) :
    ∃ maximalLocal : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeGamma 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      pRank prime maximalLocal = 3 ∧
      (∀ conjugator : G, conjugator ∉ maximalLocal →
        pRank prime (maximalLocal ⊓
          maximalLocal.map (MulAut.conj conjugator).toMonoidHom) < 2) ∧
      (∀ primeGroup : Subgroup G, IsPGroup prime primeGroup → primeGroup ≤ maximalLocal →
        2 ≤ pRank prime primeGroup → Subgroup.normalizer (primeGroup : Set G) ≤ maximalLocal) := by
  obtain ⟨maximalLocal, hmaximal, hcore, _, hinclusion, _, hlocalRank⟩ :=
    selected_abelian_coreLocal_all_sylows_have_full_core_overgroup hrank hcoreLocal prime hselected
      sylowGroup hcommutative
  refine ⟨maximalLocal, hmaximal, hcore, hinclusion, hlocalRank, ?_, ?_⟩
  · exact abelian_sylow_gamma_two_conjugate_intersection_rank_lt_two prime
      (sigmaA_prime prime hselected) sylowGroup hcommutative maximalLocal hinclusion hcore
  · intro primeGroup hpGroup hprimeGroup hgroupRank
    exact abelian_sylow_gamma_two_rank_two_normalizer_le prime (sigmaA_prime prime hselected)
      sylowGroup hcommutative maximalLocal hinclusion hcore primeGroup hpGroup hprimeGroup hgroupRank

end CFSG.RankThreeCoreUniqueness.Helpers
