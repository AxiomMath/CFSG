module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

@[expose] def rankTwoSignalizerJoin (prime : ℕ) (actingGroup : Subgroup G) : Subgroup G :=
  sSup {signalGroup : Subgroup G | Nat.Coprime prime (Nat.card signalGroup) ∧
    actingGroup ≤ Subgroup.normalizer (signalGroup : Set G)}

omit [Finite G] in
theorem rankTwoSignalizerJoin_le_iff
    (prime : ℕ) (actingGroup overgroup : Subgroup G) :
    rankTwoSignalizerJoin prime actingGroup ≤ overgroup ↔
      ∀ signalGroup : Subgroup G, Nat.Coprime prime (Nat.card signalGroup) →
        actingGroup ≤ Subgroup.normalizer (signalGroup : Set G) → signalGroup ≤ overgroup := by
  constructor
  · intro hjoin signalGroup hcoprime hinvariant
    exact (show signalGroup ≤ rankTwoSignalizerJoin prime actingGroup from
      le_sSup ⟨hcoprime, hinvariant⟩).trans hjoin
  · intro hsignals
    apply sSup_le
    rintro signalGroup ⟨hcoprime, hinvariant⟩
    exact hsignals signalGroup hcoprime hinvariant

omit [Finite G] in
theorem rankTwoSignalizerJoin_map_le
    (prime : ℕ) (actingGroup : Subgroup G) (automorphism : MulAut G) :
    (rankTwoSignalizerJoin prime actingGroup).map automorphism.toMonoidHom ≤
      rankTwoSignalizerJoin prime (actingGroup.map automorphism.toMonoidHom) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (rankTwoSignalizerJoin_le_iff prime actingGroup _).mpr
  intro signalGroup hcoprime hinvariant
  apply Subgroup.map_le_iff_le_comap.mp
  apply le_sSup
  constructor
  · have hcard := Nat.card_congr
      (signalGroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective).toEquiv
    rwa [← hcard]
  · have himage := Subgroup.map_mono (f := automorphism.toMonoidHom) hinvariant
    rwa [Subgroup.map_equiv_normalizer_eq] at himage

omit [Finite G] in
theorem normalizer_le_normalizer_rankTwoSignalizerJoin
    (prime : ℕ) (actingGroup : Subgroup G) :
    Subgroup.normalizer (actingGroup : Set G) ≤
      Subgroup.normalizer (rankTwoSignalizerJoin prime actingGroup : Set G) := by
  intro normalizingElement hnormalizing
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm
  · have himage := rankTwoSignalizerJoin_map_le prime actingGroup (MulAut.conj normalizingElement)
    have hpreserved := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalizing
    change actingGroup.map (MulAut.conj normalizingElement).toMonoidHom = actingGroup at hpreserved
    rw [hpreserved] at himage
    exact himage
  · apply (Subgroup.map_le_map_iff_of_injective
      (f := (MulAut.conj normalizingElement⁻¹).toMonoidHom)
      (MulAut.conj normalizingElement⁻¹).injective).mp
    have hinverse := rankTwoSignalizerJoin_map_le prime actingGroup
      (MulAut.conj normalizingElement⁻¹)
    have hinverseNormalizing := (Subgroup.normalizer (actingGroup : Set G)).inv_mem hnormalizing
    have hpreserved := Subgroup.mem_normalizer_iff_map_conj_eq.mp hinverseNormalizing
    change actingGroup.map (MulAut.conj normalizingElement⁻¹).toMonoidHom = actingGroup at hpreserved
    rw [hpreserved] at hinverse
    change (rankTwoSignalizerJoin prime actingGroup).map
        (MulAut.conj normalizingElement⁻¹).toMonoidHom ≤
      ((rankTwoSignalizerJoin prime actingGroup).map
        (MulAut.conj normalizingElement).toMonoidHom).map
        (MulAut.conj normalizingElement⁻¹).toMonoidHom
    rw [conjugate_map_mul, inv_mul_cancel]
    have hidentity : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext element
      simp
    rwa [hidentity, Subgroup.map_id]

theorem local_twoCore_le_rankTwoSignalizerJoin
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup localGroup : Subgroup G) (hinclusion : actingGroup ≤ localGroup) :
    pCoreOf 2 localGroup ≤ rankTwoSignalizerJoin prime actingGroup := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ :=
    (IsPGroup.iff_card (p := 2) (G := pCoreOf 2 localGroup)).mp
      (pCoreOf_isPGroup 2 localGroup)
  apply le_sSup
  constructor
  · rw [hcard]
    exact (Nat.coprime_primes hprime Nat.prime_two |>.mpr hodd).pow_right exponent
  · exact hinclusion.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)

theorem rankTwoSignalizerJoin_twoCore_ne_bot
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (hinclusion : actingGroup ≤ localGroup)
    (hjoin : rankTwoSignalizerJoin prime actingGroup ≤ localGroup) :
    pCoreOf 2 (rankTwoSignalizerJoin prime actingGroup) ≠ ⊥ := by
  have hcontained := local_twoCore_le_rankTwoSignalizerJoin prime hprime hodd actingGroup
    localGroup hinclusion
  have hnormalizing : rankTwoSignalizerJoin prime actingGroup ≤
      Subgroup.normalizer (pCoreOf 2 localGroup : Set G) :=
    hjoin.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)
  have hnormal := Subgroup.normal_subgroupOf_iff_le_normalizer hcontained |>.mpr hnormalizing
  have hcore := normal_pGroup_le_pCoreOf 2 (pCoreOf 2 localGroup)
    (rankTwoSignalizerJoin prime actingGroup) hcontained hnormal (pCoreOf_isPGroup 2 localGroup)
  intro htrivial
  exact twoLocal_pCoreOf_ne_bot localGroup hlocal
    (le_bot_iff.mp (htrivial ▸ hcore))

theorem rankTwo_full_sylow_normalizer_signalizer_branch
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (maximalLocal actingGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal maximalLocal)
    (hacting : actingGroup ≤ maximalLocal)
    (hsylow : (sylowGroup : Subgroup G) ≤ Subgroup.normalizer (actingGroup : Set G))
    (hsylowLocal : (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hrank : 3 ≤ pRank prime (sylowGroup : Subgroup G))
    (hsignals : ∀ signalGroup : Subgroup G, Nat.Coprime prime (Nat.card signalGroup) →
      actingGroup ≤ Subgroup.normalizer (signalGroup : Set G) → signalGroup ≤ maximalLocal)
    (hlocalConfinement : ∀ localGroup : Subgroup G, IsTwoLocal localGroup →
      3 ≤ pRank prime (localGroup ⊓ maximalLocal) → localGroup ≤ maximalLocal) :
    Subgroup.normalizer (actingGroup : Set G) ≤ maximalLocal := by
  let signalJoin := rankTwoSignalizerJoin prime actingGroup
  have hjoin : signalJoin ≤ maximalLocal :=
    (rankTwoSignalizerJoin_le_iff prime actingGroup maximalLocal).mpr hsignals
  have hcoreNontrivial : pCoreOf 2 signalJoin ≠ ⊥ :=
    rankTwoSignalizerJoin_twoCore_ne_bot prime hprime hodd actingGroup maximalLocal hmaximal.1
      hacting hjoin
  have hnormalizer : Subgroup.normalizer (actingGroup : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 signalJoin : Set G) :=
    (normalizer_le_normalizer_rankTwoSignalizerJoin prime actingGroup).trans
      (normalizer_localGroup_le_normalizer_pCoreOf 2 signalJoin)
  have hlocal : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 signalJoin : Set G)) :=
    ⟨pCoreOf 2 signalJoin, hcoreNontrivial, pCoreOf_isPGroup 2 signalJoin, rfl⟩
  exact hnormalizer.trans (hlocalConfinement _ hlocal
    (hrank.trans (pRank_mono prime hprime.one_lt
      (le_inf (hsylow.trans hnormalizer) hsylowLocal))))

theorem rankTwo_escaping_normalizer_full_sylow_has_escaping_signalizer
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (maximalLocal actingGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal maximalLocal)
    (hacting : actingGroup ≤ maximalLocal)
    (hsylow : (sylowGroup : Subgroup G) ≤ Subgroup.normalizer (actingGroup : Set G))
    (hsylowLocal : (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hrank : 3 ≤ pRank prime (sylowGroup : Subgroup G))
    (hlocalConfinement : ∀ localGroup : Subgroup G, IsTwoLocal localGroup →
      3 ≤ pRank prime (localGroup ⊓ maximalLocal) → localGroup ≤ maximalLocal)
    (hescape : ¬ Subgroup.normalizer (actingGroup : Set G) ≤ maximalLocal) :
    ∃ signalGroup : Subgroup G, Nat.Coprime prime (Nat.card signalGroup) ∧
      actingGroup ≤ Subgroup.normalizer (signalGroup : Set G) ∧ ¬ signalGroup ≤ maximalLocal := by
  classical
  have hsignals : ¬ ∀ signalGroup : Subgroup G, Nat.Coprime prime (Nat.card signalGroup) →
      actingGroup ≤ Subgroup.normalizer (signalGroup : Set G) → signalGroup ≤ maximalLocal := by
    intro hconfined
    exact hescape (rankTwo_full_sylow_normalizer_signalizer_branch prime hprime hodd sylowGroup
      maximalLocal actingGroup hmaximal hacting hsylow hsylowLocal hrank hconfined hlocalConfinement)
  push Not at hsignals
  exact hsignals

@[expose] def rankTwoMaximalInvariantTwoSubgroup (actingGroup twoGroup : Subgroup G) : Prop :=
  IsPGroup 2 twoGroup ∧ actingGroup ≤ Subgroup.normalizer (twoGroup : Set G) ∧
    ∀ larger : Subgroup G, IsPGroup 2 larger →
      actingGroup ≤ Subgroup.normalizer (larger : Set G) → twoGroup ≤ larger → larger = twoGroup

omit [Finite G] in
theorem rankTwoMaximalInvariantTwoSubgroup_map
    (actingGroup twoGroup : Subgroup G) (automorphism : MulAut G)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup) :
    rankTwoMaximalInvariantTwoSubgroup (actingGroup.map automorphism.toMonoidHom)
      (twoGroup.map automorphism.toMonoidHom) := by
  refine ⟨hmaximal.1.map automorphism.toMonoidHom, ?_, ?_⟩
  · have himage := Subgroup.map_mono (f := automorphism.toMonoidHom) hmaximal.2.1
    rwa [Subgroup.map_equiv_normalizer_eq] at himage
  · intro larger hpGroup hinvariant hinclusion
    have hinversePGroup := hpGroup.map automorphism.symm.toMonoidHom
    have hinverseInvariant := Subgroup.map_mono (f := automorphism.symm.toMonoidHom) hinvariant
    rw [map_automorphism_symm_map, Subgroup.map_equiv_normalizer_eq] at hinverseInvariant
    have hinverseInclusion := Subgroup.map_mono (f := automorphism.symm.toMonoidHom) hinclusion
    rw [map_automorphism_symm_map] at hinverseInclusion
    have hequal := hmaximal.2.2 (larger.map automorphism.symm.toMonoidHom) hinversePGroup
      hinverseInvariant hinverseInclusion
    apply (Subgroup.map_injective (f := automorphism.symm.toMonoidHom)
      automorphism.symm.injective)
    rwa [map_automorphism_symm_map]

omit [Finite G] in
theorem rankTwo_normalizer_le_of_signalizer_transitivity
    (actingGroup overgroup twoGroup : Subgroup G)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup)
    (hcentralizer : Subgroup.centralizer (actingGroup : Set G) ≤ overgroup)
    (hnormalizer : Subgroup.normalizer (twoGroup : Set G) ≤ overgroup)
    (htransitivity : ∀ other : Subgroup G, rankTwoMaximalInvariantTwoSubgroup actingGroup other →
      ∃ centralizingElement : G, centralizingElement ∈ Subgroup.centralizer (actingGroup : Set G) ∧
        other.map (MulAut.conj centralizingElement).toMonoidHom = twoGroup) :
    Subgroup.normalizer (actingGroup : Set G) ≤ overgroup := by
  intro normalizingElement hnormalizing
  have hpreserved := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalizing
  change actingGroup.map (MulAut.conj normalizingElement).toMonoidHom = actingGroup at hpreserved
  have hconjugateMaximal := rankTwoMaximalInvariantTwoSubgroup_map actingGroup twoGroup
    (MulAut.conj normalizingElement) hmaximal
  rw [hpreserved] at hconjugateMaximal
  obtain ⟨centralizingElement, hcentralizing, hadjusted⟩ := htransitivity _ hconjugateMaximal
  have hproduct : centralizingElement * normalizingElement ∈ overgroup := by
    apply hnormalizer
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change twoGroup.map (MulAut.conj (centralizingElement * normalizingElement)).toMonoidHom =
      twoGroup
    rw [← conjugate_map_mul]
    exact hadjusted
  simpa only [inv_mul_cancel_left] using
    overgroup.mul_mem (overgroup.inv_mem (hcentralizer hcentralizing)) hproduct

omit [Finite G] in
theorem rankTwo_normalizer_le_of_signalizer_transitivity_and_central_line
    (actingGroup overgroup twoGroup centralLine : Subgroup G)
    (hline : centralLine ≤ actingGroup)
    (hlineNormalizer : Subgroup.normalizer (centralLine : Set G) ≤ overgroup)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup)
    (hnormalizer : Subgroup.normalizer (twoGroup : Set G) ≤ overgroup)
    (htransitivity : ∀ other : Subgroup G, rankTwoMaximalInvariantTwoSubgroup actingGroup other →
      ∃ centralizingElement : G, centralizingElement ∈ Subgroup.centralizer (actingGroup : Set G) ∧
        other.map (MulAut.conj centralizingElement).toMonoidHom = twoGroup) :
    Subgroup.normalizer (actingGroup : Set G) ≤ overgroup := by
  exact rankTwo_normalizer_le_of_signalizer_transitivity actingGroup overgroup twoGroup hmaximal
    ((Subgroup.centralizer_le hline).trans
      ((Subgroup.centralizer_le_normalizer _).trans hlineNormalizer)) hnormalizer htransitivity

end CFSG.RankThreeCoreUniqueness.Helpers
