module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SignalizerCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeNonabelian

public section

open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def tripleCoordinateMap {FieldType : Type*} [CommSemiring FieldType] :
    FieldType × FieldType × FieldType →ₗ[FieldType] (Fin 3 → FieldType) where
  toFun coordinate := ![coordinate.1, coordinate.2.1, coordinate.2.2]
  map_add' := by
    intro first second
    ext index
    fin_cases index <;> rfl
  map_smul' := by
    intro scalar coordinate
    ext index
    fin_cases index <;> rfl

theorem tripleCoordinateMap_injective {FieldType : Type*} [CommSemiring FieldType] :
    Function.Injective (tripleCoordinateMap (FieldType := FieldType)) := by
  intro first second hequal
  exact Prod.ext (congrFun hequal 0)
    (Prod.ext (congrFun hequal 1) (congrFun hequal 2))

theorem vector_space_rank_three_has_coordinate_embedding
    {FieldType Value : Type*} [Field FieldType] [AddCommGroup Value] [Module FieldType Value]
    [Module.Finite FieldType Value] (hrank : 3 ≤ Module.finrank FieldType Value) :
    ∃ embedding : FieldType × FieldType × FieldType →+ Value,
      Function.Injective embedding := by
  classical
  let basis := Module.finBasis FieldType Value
  let selectedVectors : Fin 3 → Value := (fun index => basis index) ∘ Fin.castLEEmb hrank
  have hindependent : LinearIndependent FieldType selectedVectors :=
    basis.linearIndependent.comp _ (Fin.castLEEmb hrank).injective
  let embedding := (Fintype.linearCombination FieldType selectedVectors).comp tripleCoordinateMap
  exact ⟨embedding.toAddMonoidHom,
    hindependent.fintypeLinearCombination_injective.comp tripleCoordinateMap_injective⟩

theorem elementary_rank_three_has_coordinate_embedding
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (elementary : Subgroup G) (helementary : IsElemAbelian prime elementary)
    (exponent : ℕ) (hcard : Nat.card elementary = prime ^ exponent) (hrank : 3 ≤ exponent) :
    ∃ embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G,
      Function.Injective embedding ∧ embedding.range ≤ elementary := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : CommGroup elementary := { (inferInstance : Group elementary) with
    mul_comm := helementary.1.is_comm.comm }
  have hexponent : ∀ element : Additive elementary, prime • element = 0 := by
    intro element
    apply Additive.toMul.injective
    apply Subtype.ext
    exact helementary.2 ((Additive.toMul element : elementary) : G)
      (Additive.toMul element).property
  let moduleStructure : Module (ZMod prime) (Additive elementary) :=
    AddCommGroup.zmodModule hexponent
  let : Module (ZMod prime) (Additive elementary) := moduleStructure
  let : Fintype (Additive elementary) := Fintype.ofFinite _
  let finiteStructure : Module.Finite (ZMod prime) (Additive elementary) := Module.Finite.of_finite
  have hdimension : Module.finrank (ZMod prime) (Additive elementary) = exponent := by
    apply Nat.pow_right_injective hprime.two_le
    have hmoduleCard := Module.card_eq_pow_finrank (K := ZMod prime)
      (V := Additive elementary)
    rw [ZMod.card] at hmoduleCard
    have hcardAdditive := Nat.card_congr (Additive.ofMul : elementary ≃ Additive elementary)
    rw [Nat.card_eq_fintype_card (α := Additive elementary)] at hcardAdditive
    exact hmoduleCard.symm.trans (hcardAdditive.symm.trans hcard)
  obtain ⟨additiveEmbedding, hadditiveInjective⟩ :=
    @vector_space_rank_three_has_coordinate_embedding (ZMod prime) (Additive elementary)
      (inferInstance : Field (ZMod prime)) (inferInstance : AddCommGroup (Additive elementary))
      moduleStructure finiteStructure (hdimension ▸ hrank)
  let internalEmbedding := AddMonoidHom.toMultiplicativeLeft additiveEmbedding
  let embedding := elementary.subtype.comp internalEmbedding
  refine ⟨embedding, ?_, ?_⟩
  · exact Subtype.val_injective.comp (Additive.toMul.injective.comp
      (hadditiveInjective.comp Multiplicative.toAdd.injective))
  · rintro element ⟨coordinate, rfl⟩
    exact (internalEmbedding coordinate).property

theorem rank_three_has_coordinate_embedding
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (actingGroup : Subgroup G) (hrank : 3 ≤ pRank prime actingGroup) :
    ∃ embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G,
      Function.Injective embedding ∧ embedding.range ≤ actingGroup := by
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime actingGroup
    (by omega)
  obtain ⟨embedding, hinjective, hrange⟩ := elementary_rank_three_has_coordinate_embedding
    prime hprime elementary helementary (pRank prime actingGroup) hcard hrank
  exact ⟨embedding, hinjective, hrange.trans hinclusion⟩

theorem rank_three_signalizer_le_aschCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (ambient actingGroup signalizer : Subgroup G) (hinclusion : actingGroup ≤ ambient)
    (hrank : 3 ≤ pRank prime actingGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) :
    signalizer ≤ rankThreeAschCore 2 prime ambient := by
  obtain ⟨embedding, hinjective, hrange⟩ := rank_three_has_coordinate_embedding
    prime hprime actingGroup hrank
  exact embedded_rank_three_signalizer_le_aschCore prime hprime embedding hinjective
    ambient signalizer (hrange.trans hinclusion) (hrange.trans hinvariant) hcoprime

theorem rank_three_signalizer_join_le_aschCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (ambient actingGroup : Subgroup G) (hinclusion : actingGroup ≤ ambient)
    (hrank : 3 ≤ pRank prime actingGroup) :
    rankTwoSignalizerJoin prime actingGroup ≤ rankThreeAschCore 2 prime ambient := by
  apply (rankTwoSignalizerJoin_le_iff prime actingGroup _).mpr
  intro signalizer hcoprime hinvariant
  exact rank_three_signalizer_le_aschCore prime hprime ambient actingGroup signalizer
    hinclusion hrank hinvariant hcoprime

theorem rank_three_signalizer_le_overgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup actingGroup signalizer : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hacting : actingGroup ≤ overgroup) (hpGroup : IsPGroup prime actingGroup)
    (hrank : 3 ≤ pRank prime actingGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) : signalizer ≤ overgroup := by
  obtain ⟨conjugator, hconjugated⟩ := pGroup_conjugate_into_sylow_within_overgroup
    prime hprime sylowGroup overgroup hsylow actingGroup hpGroup hacting
  let automorphism := MulAut.conj (conjugator : G)
  have hconjugateRank : 3 ≤ pRank prime (actingGroup.map automorphism.toMonoidHom) := by
    rwa [pRank_map_automorphism prime hprime.one_lt]
  have hconjugateInvariant : actingGroup.map automorphism.toMonoidHom ≤
      Subgroup.normalizer (signalizer.map automorphism.toMonoidHom : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hinvariant
  have hconjugateCoprime : prime.Coprime (Nat.card (signalizer.map automorphism.toMonoidHom)) := by
    rw [← Nat.card_congr
      (signalizer.equivMapOfInjective automorphism.toMonoidHom automorphism.injective).toEquiv]
    exact hcoprime
  have hconjugateLe := (rank_three_signalizer_le_aschCore prime hprime
    (sylowGroup : Subgroup G) (actingGroup.map automorphism.toMonoidHom)
    (signalizer.map automorphism.toMonoidHom) hconjugated hconjugateRank
    hconjugateInvariant hconjugateCoprime).trans hcore
  intro element helement
  have hconjugateElement := hconjugateLe
    (Subgroup.mem_map_of_mem automorphism.toMonoidHom helement)
  have hproduct := overgroup.mul_mem
    (overgroup.mul_mem (overgroup.inv_mem conjugator.property) hconjugateElement) conjugator.property
  simpa [automorphism, MulAut.conj_apply, mul_assoc] using hproduct

theorem rank_three_signalizer_join_le_overgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup actingGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hacting : actingGroup ≤ overgroup) (hpGroup : IsPGroup prime actingGroup)
    (hrank : 3 ≤ pRank prime actingGroup) : rankTwoSignalizerJoin prime actingGroup ≤ overgroup := by
  apply (rankTwoSignalizerJoin_le_iff prime actingGroup _).mpr
  intro signalizer hcoprime hinvariant
  exact rank_three_signalizer_le_overgroup prime hprime sylowGroup overgroup actingGroup
    signalizer hsylow hcore hacting hpGroup hrank hinvariant hcoprime

theorem two_local_rank_three_intersection_twoCore_le_overgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (overgroup localGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) : pCoreOf 2 localGroup ≤ overgroup := by
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime
    (localGroup ⊓ overgroup) (by omega)
  have hgroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  have helementaryRank : 3 ≤ pRank prime elementary := by
    unfold pRank
    exact hrank.trans (le_csSup (pRank_set_bddAbove prime hprime.one_lt elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩)
  exact (local_twoCore_le_rankTwoSignalizerJoin prime hprime hodd elementary localGroup
    (hinclusion.trans inf_le_left)).trans
    (rank_three_signalizer_join_le_overgroup prime hprime sylowGroup overgroup elementary
      hsylow hcore (hinclusion.trans inf_le_right) hgroup helementaryRank)

theorem escaping_two_local_rank_three_twoCore_not_normal_in_maximal
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (maximalLocal localGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal maximalLocal) (hlocal : IsTwoLocal localGroup)
    (hsylow : (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ maximalLocal))
    (hescape : ¬ localGroup ≤ maximalLocal) :
    pCoreOf 2 localGroup ≤ maximalLocal ∧
      ¬ ((pCoreOf 2 localGroup).subgroupOf maximalLocal).Normal := by
  have hcontained := two_local_rank_three_intersection_twoCore_le_overgroup prime hprime
    hodd sylowGroup maximalLocal localGroup hsylow hcore hrank
  refine ⟨hcontained, ?_⟩
  intro hnormal
  have hmaximalNormalizing :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcontained).mp hnormal
  have hnormalizer := hmaximal.2 _ (normalizer_pCoreOf_isTwoLocal localGroup hlocal)
    hmaximalNormalizing
  exact hescape ((localGroup_le_normalizer_pCoreOf 2 localGroup).trans hnormalizer.le)

end CFSG.RankThreeCoreUniqueness.Helpers
