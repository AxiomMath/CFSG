module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeSylowTransitivity

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

def coordinatePairProjectionHom {FieldType : Type*} [CommSemiring FieldType] :
    Multiplicative (FieldType × FieldType × FieldType) →* Multiplicative (FieldType × FieldType) where
  toFun coordinate := Multiplicative.ofAdd
    ((Multiplicative.toAdd coordinate).1, (Multiplicative.toAdd coordinate).2.1)
  map_one' := rfl
  map_mul' := by
    intro first second
    rfl

@[expose] def coordinatePairLineHom {FieldType : Type*} [CommSemiring FieldType]
    (vector : FieldType × FieldType) : Multiplicative FieldType →* Multiplicative (FieldType × FieldType) where
  toFun coordinate := Multiplicative.ofAdd (Multiplicative.toAdd coordinate • vector)
  map_one' := by
    change (0 : FieldType) • vector = 0
    exact zero_smul _ _
  map_mul' := by
    intro first second
    change (Multiplicative.toAdd first + Multiplicative.toAdd second) • vector =
      Multiplicative.toAdd first • vector + Multiplicative.toAdd second • vector
    exact add_smul _ _ _

theorem independent_plane_projection_not_both_zero
    {FieldType : Type*} [Field FieldType] (first second : FieldType × FieldType × FieldType)
    (hindependent : LinearIndependent FieldType ![first, second]) :
    (first.1, first.2.1) ≠ (0, 0) ∨ (second.1, second.2.1) ≠ (0, 0) := by
  by_contra hnone
  push Not at hnone
  have hfirstZero : first.1 = 0 ∧ first.2.1 = 0 :=
    ⟨congrArg Prod.fst hnone.1, congrArg Prod.snd hnone.1⟩
  have hsecondZero : second.1 = 0 ∧ second.2.1 = 0 :=
    ⟨congrArg Prod.fst hnone.2, congrArg Prod.snd hnone.2⟩
  have hrelation : second.2.2 • first + (-first.2.2) • second = 0 := by
    apply Prod.ext
    · simp [hfirstZero.1, hsecondZero.1]
    · apply Prod.ext
      · simp [hfirstZero.2, hsecondZero.2]
      · change second.2.2 * first.2.2 + (-first.2.2) * second.2.2 = 0
        ring
  have hcoefficients := LinearIndependent.pair_iff.mp hindependent _ _ hrelation
  have hthirdZero : first.2.2 = 0 := neg_eq_zero.mp hcoefficients.2
  apply hindependent.ne_zero 0
  change first = 0
  exact Prod.ext hfirstZero.1 (Prod.ext hfirstZero.2 hthirdZero)

theorem finite_prime_coprime_fixed_lines_generate
    {Value : Type*} [Group Value] [Finite Value]
    (prime : ℕ) (hprime : prime.Prime)
    (action : Multiplicative (ZMod prime × ZMod prime) →* MulAut Value)
    (overgroup : Subgroup Value) (hcoprime : prime.Coprime (Nat.card Value))
    (hlines : ∀ vector : ZMod prime × ZMod prime, vector ≠ 0 → ∀ element : Value,
      (∀ coordinate : ZMod prime,
        action (coordinatePairLineHom vector (Multiplicative.ofAdd coordinate)) element = element) →
      element ∈ overgroup) : overgroup = ⊤ := by
  let : Fact prime.Prime := ⟨hprime⟩
  apply finite_prime_coprime_fixed_planes_generate prime hprime
    (action.comp coordinatePairProjectionHom) overgroup hcoprime
  intro first second hindependent element hfixed
  rcases independent_plane_projection_not_both_zero first second hindependent with hfirst | hsecond
  · apply hlines (first.1, first.2.1) hfirst element
    intro coordinate
    have hknown := hfixed (Multiplicative.ofAdd (coordinate, 0))
    have hequal : coordinatePairProjectionHom
        (coordinatePlaneHom first second (Multiplicative.ofAdd (coordinate, 0))) =
        coordinatePairLineHom (first.1, first.2.1) (Multiplicative.ofAdd coordinate) := by
      change ((coordinate • first + (0 : ZMod prime) • second).1,
        (coordinate • first + (0 : ZMod prime) • second).2.1) =
          coordinate • (first.1, first.2.1)
      simp
    change action (coordinatePairProjectionHom
      (coordinatePlaneHom first second (Multiplicative.ofAdd (coordinate, 0)))) element = element
      at hknown
    rwa [hequal] at hknown
  · apply hlines (second.1, second.2.1) hsecond element
    intro coordinate
    have hknown := hfixed (Multiplicative.ofAdd (0, coordinate))
    have hequal : coordinatePairProjectionHom
        (coordinatePlaneHom first second (Multiplicative.ofAdd (0, coordinate))) =
        coordinatePairLineHom (second.1, second.2.1) (Multiplicative.ofAdd coordinate) := by
      change (((0 : ZMod prime) • first + coordinate • second).1,
        ((0 : ZMod prime) • first + coordinate • second).2.1) =
          coordinate • (second.1, second.2.1)
      simp
    change action (coordinatePairProjectionHom
      (coordinatePlaneHom first second (Multiplicative.ofAdd (0, coordinate)))) element = element
      at hknown
    rwa [hequal] at hknown

open CFSG.Open

theorem embedded_rank_two_signalizer_le_of_line_centralizers
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime) →* G)
    (signalizer overgroup : Subgroup G)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer))
    (hcentralizers : ∀ vector : ZMod prime × ZMod prime, vector ≠ 0 →
      signalizer ⊓ Subgroup.centralizer
        ((embedding.comp (coordinatePairLineHom vector)).range : Set G) ≤ overgroup) :
    signalizer ≤ overgroup := by
  let action := ambientSubgroupActionHom embedding.range signalizer hinvariant
  let embeddingAction := action.comp embedding.rangeRestrict
  have hfull : overgroup.subgroupOf signalizer = ⊤ := by
    apply finite_prime_coprime_fixed_lines_generate prime hprime embeddingAction
      (overgroup.subgroupOf signalizer) hcoprime
    intro vector hvector element hfixed
    apply hcentralizers vector hvector
    refine ⟨element.property, ?_⟩
    change (element : G) ∈ Subgroup.centralizer
      ((embedding.comp (coordinatePairLineHom vector)).range : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro actingElement ⟨coordinate, rfl⟩
    have hambient := congrArg Subtype.val (hfixed (Multiplicative.toAdd coordinate))
    change ↑(ambientSubgroupActionHom embedding.range signalizer hinvariant
      (embedding.rangeRestrict (coordinatePairLineHom vector coordinate)) element) = (element : G)
      at hambient
    rw [ambientSubgroupActionHom_apply_coe] at hambient
    exact mul_inv_eq_iff_eq_mul.mp hambient
  intro element helement
  exact show (⟨element, helement⟩ : signalizer) ∈ overgroup.subgroupOf signalizer from
    hfull ▸ Subgroup.mem_top _

theorem embedded_coordinate_line_rank_at_least_one
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding) (vector : ZMod prime × ZMod prime)
    (hvector : vector ≠ 0) :
    1 ≤ pRank prime (embedding.comp (coordinatePairLineHom vector)).range := by
  let : Fact prime.Prime := ⟨hprime⟩
  let lineEmbedding := embedding.comp (coordinatePairLineHom vector)
  have hlineInjective : Function.Injective lineEmbedding := by
    intro first second hequal
    let : AddCommGroup (ZMod prime) := (ZMod.commRing prime).toAddCommGroup
    have hcoordinates := hinjective hequal
    change Multiplicative.toAdd first • vector = Multiplicative.toAdd second • vector at hcoordinates
    exact Multiplicative.toAdd.injective
      (smul_left_injective (ZMod prime) hvector hcoordinates)
  have helementary : IsElemAbelian prime lineEmbedding.range := by
    constructor
    · infer_instance
    · rintro element ⟨source, rfl⟩
      rw [← map_pow]
      have hexponent : source ^ prime = 1 := by
        change prime • Multiplicative.toAdd source = 0
        simp [nsmul_eq_mul]
      rw [hexponent, map_one]
  have hcard : Nat.card lineEmbedding.range = prime ^ 1 := by
    have hcardRange := Nat.card_range_of_injective hlineInjective
    change Nat.card lineEmbedding.range = _ at hcardRange
    rw [hcardRange]
    change Nat.card (ZMod prime) = prime ^ 1
    simp
  unfold pRank
  exact le_csSup (pRank_set_bddAbove prime hprime.one_lt lineEmbedding.range)
    ⟨lineEmbedding.range, le_rfl, helementary, hcard⟩

theorem embedded_rank_two_signalizer_le_gamma_one
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding) (ambient signalizer : Subgroup G)
    (hinclusion : embedding.range ≤ ambient)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) :
    signalizer ≤ rankThreeGamma 1 prime ambient := by
  apply embedded_rank_two_signalizer_le_of_line_centralizers prime hprime embedding
    signalizer _ hinvariant hcoprime
  intro vector hvector
  have hlineInclusion : (embedding.comp (coordinatePairLineHom vector)).range ≤ ambient := by
    rintro element ⟨coordinate, rfl⟩
    exact hinclusion ⟨coordinatePairLineHom vector coordinate, rfl⟩
  exact (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans
    (gamma_normalizer_le 1 prime ambient _ hlineInclusion
      (embedded_coordinate_line_rank_at_least_one prime hprime embedding hinjective vector hvector))

def pairCoordinateMap {FieldType : Type*} [CommSemiring FieldType] :
    FieldType × FieldType →ₗ[FieldType] (Fin 2 → FieldType) where
  toFun coordinate := ![coordinate.1, coordinate.2]
  map_add' := by
    intro first second
    ext index
    fin_cases index <;> rfl
  map_smul' := by
    intro scalar coordinate
    ext index
    fin_cases index <;> rfl

theorem pairCoordinateMap_injective {FieldType : Type*} [CommSemiring FieldType] :
    Function.Injective (pairCoordinateMap (FieldType := FieldType)) := by
  intro first second hequal
  exact Prod.ext (congrFun hequal 0) (congrFun hequal 1)

theorem vector_space_rank_two_has_coordinate_embedding
    {FieldType Value : Type*} [Field FieldType] [AddCommGroup Value] [Module FieldType Value]
    [Module.Finite FieldType Value] (hrank : 2 ≤ Module.finrank FieldType Value) :
    ∃ embedding : FieldType × FieldType →+ Value, Function.Injective embedding := by
  classical
  let basis := Module.finBasis FieldType Value
  let selectedVectors : Fin 2 → Value := (fun index => basis index) ∘ Fin.castLEEmb hrank
  have hindependent : LinearIndependent FieldType selectedVectors :=
    basis.linearIndependent.comp _ (Fin.castLEEmb hrank).injective
  let embedding := (Fintype.linearCombination FieldType selectedVectors).comp pairCoordinateMap
  exact ⟨embedding.toAddMonoidHom,
    hindependent.fintypeLinearCombination_injective.comp pairCoordinateMap_injective⟩

theorem elementary_rank_two_has_coordinate_embedding
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (elementary : Subgroup G) (helementary : IsElemAbelian prime elementary)
    (exponent : ℕ) (hcard : Nat.card elementary = prime ^ exponent) (hrank : 2 ≤ exponent) :
    ∃ embedding : Multiplicative (ZMod prime × ZMod prime) →* G,
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
    @vector_space_rank_two_has_coordinate_embedding (ZMod prime) (Additive elementary)
      (inferInstance : Field (ZMod prime)) (inferInstance : AddCommGroup (Additive elementary))
      moduleStructure finiteStructure (hdimension ▸ hrank)
  let internalEmbedding := AddMonoidHom.toMultiplicativeLeft additiveEmbedding
  let embedding := elementary.subtype.comp internalEmbedding
  refine ⟨embedding, ?_, ?_⟩
  · exact Subtype.val_injective.comp (Additive.toMul.injective.comp
      (hadditiveInjective.comp Multiplicative.toAdd.injective))
  · rintro element ⟨coordinate, rfl⟩
    exact (internalEmbedding coordinate).property

theorem rank_two_has_coordinate_embedding
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (actingGroup : Subgroup G) (hrank : 2 ≤ pRank prime actingGroup) :
    ∃ embedding : Multiplicative (ZMod prime × ZMod prime) →* G,
      Function.Injective embedding ∧ embedding.range ≤ actingGroup := by
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime actingGroup
    (by omega)
  obtain ⟨embedding, hinjective, hrange⟩ := elementary_rank_two_has_coordinate_embedding
    prime hprime elementary helementary (pRank prime actingGroup) hcard hrank
  exact ⟨embedding, hinjective, hrange.trans hinclusion⟩

theorem rank_two_signalizer_le_gamma_one
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (ambient actingGroup signalizer : Subgroup G) (hinclusion : actingGroup ≤ ambient)
    (hrank : 2 ≤ pRank prime actingGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) :
    signalizer ≤ rankThreeGamma 1 prime ambient := by
  obtain ⟨embedding, hinjective, hrange⟩ := rank_two_has_coordinate_embedding
    prime hprime actingGroup hrank
  exact embedded_rank_two_signalizer_le_gamma_one prime hprime embedding hinjective
    ambient signalizer (hrange.trans hinclusion) (hrange.trans hinvariant) hcoprime

theorem rank_two_signalizer_join_le_gamma_one
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (ambient actingGroup : Subgroup G) (hinclusion : actingGroup ≤ ambient)
    (hrank : 2 ≤ pRank prime actingGroup) :
    rankTwoSignalizerJoin prime actingGroup ≤ rankThreeGamma 1 prime ambient := by
  apply (rankTwoSignalizerJoin_le_iff prime actingGroup _).mpr
  intro signalizer hcoprime hinvariant
  exact rank_two_signalizer_le_gamma_one prime hprime ambient actingGroup signalizer
    hinclusion hrank hinvariant hcoprime

end CFSG.RankThreeCoreUniqueness.Helpers
