module

public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalSubgroupAverage

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def normalSubgroupCharacterSupport {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (subgroup : Subgroup G) : Finset basis.index :=
  Finset.univ.filter (fun label => ∀ element : subgroup,
    (basis.representation label).representation element.val = 1)

theorem normalSubgroupAverage_action_one_iff {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) [Fintype subgroup] (cardUnit : ℂˣ)
    (hcard : (cardUnit : ℂ) = Nat.card subgroup) (data : FiniteComplexRepresentation G) :
    data.representation.asAlgebraHom (normalSubgroupAverage subgroup cardUnit) = 1 ↔
      ∀ element : subgroup, data.representation element.val = 1 := by
  constructor
  · intro haverage element
    have hfixed := congrArg data.representation.asAlgebraHom
      (single_mul_normalSubgroupAverage subgroup cardUnit element)
    rw [map_mul, Representation.asAlgebraHom_single, one_smul, haverage, mul_one] at hfixed
    exact hfixed
  · intro hkernel
    unfold normalSubgroupAverage
    change data.representation.asAlgebraHom
      (((cardUnit⁻¹ : ℂˣ) : ℂ) • (∑ element : subgroup,
        MonoidAlgebra.single element.val 1 : MonoidAlgebra ℂ G)) = 1
    rw [map_smul, map_sum]
    simp only [Representation.asAlgebraHom_single, one_smul, hkernel, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, ← hcard,
      smul_smul, Units.inv_mul, one_smul]

theorem normalSubgroupAverage_eq_characterSubsetIdempotent {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (subgroup : Subgroup G) [subgroup.Normal]
    [Fintype subgroup] (cardUnit : ℂˣ) (hcard : (cardUnit : ℂ) = Nat.card subgroup) :
    normalSubgroupAverage subgroup cardUnit =
      characterSubsetIdempotent basis (normalSubgroupCharacterSupport basis subgroup) := by
  have hcentral := normalSubgroupAverage_central subgroup cardUnit
  have hidempotent := normalSubgroupAverage_idempotent subgroup cardUnit hcard
  rw [centralCharacterScalar_reconstruction basis _ hcentral]
  unfold characterSubsetIdempotent
  congr 1
  funext label
  have haction := centralCharacterScalar_action basis _ hcentral label
  have hone : centralCharacterScalar basis (normalSubgroupAverage subgroup cardUnit) label = 1 ↔
      ∀ element : subgroup, (basis.representation label).representation element.val = 1 := by
    rw [← normalSubgroupAverage_action_one_iff subgroup cardUnit hcard]
    rw [haction]
    exact ⟨fun hequal => by rw [hequal, one_smul], fun hequal =>
      irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
        (hequal.trans (one_smul ℂ (1 : Module.End ℂ (basis.representation label).vector)).symm)⟩
  by_cases hkernel : ∀ element : subgroup, (basis.representation label).representation element.val = 1
  · have hmember : label ∈ normalSubgroupCharacterSupport basis subgroup := by
      simpa only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] using hkernel
    rw [ite_eq_left hmember]
    exact hone.mpr hkernel
  · rw [ite_eq_right (by simpa only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] using hkernel)]
    exact (central_idempotent_scalar_zero_or_one basis _ hcentral hidempotent label).resolve_right
      (fun hequal => hkernel (hone.mp hequal))

theorem normalSubgroupAverage_map_coefficients {ring G : Type*} [CommRing ring] [Group G] [Fintype G]
    (subgroup : Subgroup G) [Fintype subgroup] (cardUnit : ringˣ) (embedding : ring →+* ℂ) :
    MonoidAlgebra.mapRingHom G embedding (normalSubgroupAverage subgroup cardUnit) =
      normalSubgroupAverage subgroup (Units.map embedding.toMonoidHom cardUnit) := by
  ext element
  simp only [MonoidAlgebra.coeff_mapRingHom, normalSubgroupAverage, MonoidAlgebra.coeff_smul_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  change embedding ((↑(cardUnit⁻¹) : ring) * ∑ member : subgroup,
      (MonoidAlgebra.single member.val (1 : ring)).coeff element) =
    embedding (↑(cardUnit⁻¹)) * ∑ member : subgroup,
      (MonoidAlgebra.single member.val (1 : ℂ)).coeff element
  rw [map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem normalSubgroupCharacterSupport_admissible {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (subgroup : Subgroup G) [subgroup.Normal] [Fintype subgroup]
    (cardUnit : coefficientRingˣ) (hcard : (cardUnit : coefficientRing) = Nat.card subgroup) :
    characterSubsetAdmissible basis coefficientRing (normalSubgroupCharacterSupport basis subgroup) := by
  have hcomplexCard : ((Units.map coefficientRing.subtype.toMonoidHom cardUnit : ℂˣ) : ℂ) =
      Nat.card subgroup := by
    change coefficientRing.subtype (cardUnit : coefficientRing) = _
    rw [hcard, map_natCast]
  rw [characterSubsetAdmissible, ← normalSubgroupAverage_eq_characterSubsetIdempotent basis subgroup _ hcomplexCard,
    ← normalSubgroupAverage_map_coefficients subgroup cardUnit coefficientRing.subtype]
  intro element
  rw [MonoidAlgebra.coeff_mapRingHom]
  exact (normalSubgroupAverage subgroup cardUnit).coeff element |>.property

end CFSG.TwoRankLowerBound.Helpers
