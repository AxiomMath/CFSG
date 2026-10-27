module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionTransport

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

def productFactorizationEquivIntersection {G : Type u} [Group G]
    (first second : Subgroup G) (firstRepresentative : first) (secondRepresentative : second) :
    (first ⊓ second : Subgroup G) ≃
      {pair : first × second // (pair.1 : G) * pair.2 = firstRepresentative * secondRepresentative} where
  toFun member := ⟨(⟨firstRepresentative * member,
      first.mul_mem firstRepresentative.property member.property.1⟩,
    ⟨(member : G)⁻¹ * secondRepresentative,
      second.mul_mem (second.inv_mem member.property.2) secondRepresentative.property⟩), by
      simp only [mul_assoc, mul_inv_cancel_left]⟩
  invFun pair := ⟨(firstRepresentative : G)⁻¹ * pair.1.1,
    first.mul_mem (first.inv_mem firstRepresentative.property) pair.1.1.property, by
      have heq : (firstRepresentative : G)⁻¹ * pair.1.1 =
          secondRepresentative * ((pair.1.2 : G)⁻¹) := by
        have hmapped := congrArg (fun element : G =>
          (firstRepresentative : G)⁻¹ * element * ((pair.1.2 : G)⁻¹)) pair.property
        simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hmapped
      rw [heq]
      exact second.mul_mem secondRepresentative.property (second.inv_mem pair.1.2.property)⟩
  left_inv member := Subtype.ext (inv_mul_cancel_left (firstRepresentative : G) (member : G))
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (mul_inv_cancel_left (firstRepresentative : G) (pair.1.1 : G))
    · apply Subtype.ext
      change ((firstRepresentative : G)⁻¹ * pair.1.1)⁻¹ * secondRepresentative = pair.1.2
      have heq := congrArg (fun element : G => ((pair.1.1 : G)⁻¹) * element) pair.property
      have hsecondEq : (pair.1.2 : G) =
          ((pair.1.1 : G)⁻¹) * firstRepresentative * secondRepresentative := by
        simpa only [mul_assoc, inv_mul_cancel_left] using heq
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hsecondEq.symm

theorem exists_fixed_product_factorization_of_pGroup_action
    {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (first second : Subgroup acted)
    (hfirstInvariant : ∀ member : actor, ∀ element ∈ first, member • element ∈ first)
    (hsecondInvariant : ∀ member : actor, ∀ element ∈ second, member • element ∈ second)
    (hcomplement : ¬prime ∣ Nat.card (first ⊓ second : Subgroup acted))
    (element : acted) (hfixed : ∀ member : actor, member • element = element)
    (hfactorization : ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element) :
    ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      (∀ member : actor, member • firstElement = firstElement) ∧
      (∀ member : actor, member • secondElement = secondElement) ∧
      firstElement * secondElement = element := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨firstRepresentative, hfirstRepresentative, secondRepresentative, hsecondRepresentative,
    hrepresentatives⟩ := hfactorization
  let : MulDistribMulAction actor first := invariantSubgroupAction first hfirstInvariant
  let : MulDistribMulAction actor second := invariantSubgroupAction second hsecondInvariant
  let fiber := {pair : first × second // (pair.1 : acted) * pair.2 = element}
  let action : MulAction actor fiber :=
    { smul := fun member pair => ⟨(member • pair.1.1, member • pair.1.2), by
        change (member • (pair.1.1 : acted)) * (member • (pair.1.2 : acted)) = element
        rw [← smul_mul', pair.property, hfixed]⟩
      one_smul := fun pair => Subtype.ext (Prod.ext (one_smul actor pair.1.1) (one_smul actor pair.1.2))
      mul_smul := fun firstMember secondMember pair => Subtype.ext
        (Prod.ext (mul_smul firstMember secondMember pair.1.1) (mul_smul firstMember secondMember pair.1.2)) }
  let : MulAction actor fiber := action
  have hcard : Nat.card fiber = Nat.card (first ⊓ second : Subgroup acted) := by
    change Nat.card {pair : first × second // (pair.1 : acted) * pair.2 = element} = _
    rw [← hrepresentatives]
    exact (Nat.card_congr (productFactorizationEquivIntersection first second
      ⟨firstRepresentative, hfirstRepresentative⟩ ⟨secondRepresentative, hsecondRepresentative⟩)).symm
  obtain ⟨pair, hpair⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard.symm ▸ hcomplement)
  refine ⟨pair.1.1, pair.1.1.property, pair.1.2, pair.1.2.property, ?_, ?_, pair.property⟩
  · intro member
    have heq := congrArg (fun value : fiber => ((value.1.1 : first) : acted))
      (MulAction.mem_fixedPoints.mp hpair member)
    exact heq
  · intro member
    have heq := congrArg (fun value : fiber => ((value.1.2 : second) : acted))
      (MulAction.mem_fixedPoints.mp hpair member)
    exact heq

theorem normalized_sup_centralizer_eq_of_pGroup_prime_complement
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor first second : Subgroup G)
    (hpgroup : IsPGroup prime actor)
    (hfirstNormalized : actor ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalized : actor ≤ Subgroup.normalizer (second : Set G))
    (hsecondNormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hcomplement : ¬prime ∣ Nat.card (first ⊓ second : Subgroup G)) :
    (first ⊔ second) ⊓ Subgroup.centralizer (actor : Set G) =
      (first ⊓ Subgroup.centralizer (actor : Set G)) ⊔
        (second ⊓ Subgroup.centralizer (actor : Set G)) := by
  let action : MulDistribMulAction actor G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp actor.subtype)
  let : MulDistribMulAction actor G := action
  let : MulAction actor G := action.toMulAction
  have hfirstInvariant : ∀ member : actor, ∀ element ∈ first, member • element ∈ first :=
    fun member element helement => Subgroup.le_normalizer_iff.mp hfirstNormalized
      member member.property element helement
  have hsecondInvariant : ∀ member : actor, ∀ element ∈ second, member • element ∈ second :=
    fun member element helement => Subgroup.le_normalizer_iff.mp hsecondNormalized
      member member.property element helement
  apply le_antisymm
  · intro element helement
    have hfixed : ∀ member : actor, member • element = element := by
      intro member
      change (member : G) * element * (member : G)⁻¹ = element
      rw [Subgroup.mem_centralizer_iff.mp helement.2 member member.property, mul_inv_cancel_right]
    obtain ⟨firstElement, hfirst, secondElement, hsecond, hfirstFixed, hsecondFixed, rfl⟩ :=
      exists_fixed_product_factorization_of_pGroup_action prime hprime hpgroup first second
        hfirstInvariant hsecondInvariant hcomplement element hfixed
          (normalized_sup_factorization first second hsecondNormalizes element helement.1)
    apply Subgroup.mul_mem_sup
    · refine ⟨hfirst, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro member hmember
      have heq := hfirstFixed ⟨member, hmember⟩
      change member * firstElement * member⁻¹ = firstElement at heq
      have hmul := congrArg (fun element : G => element * member) heq
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
    · refine ⟨hsecond, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro member hmember
      have heq := hsecondFixed ⟨member, hmember⟩
      change member * secondElement * member⁻¹ = secondElement at heq
      have hmul := congrArg (fun element : G => element * member) heq
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl)

end CFSG.RankThreeEvenClassification.Helpers
