module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem exists_centralizer_with_same_image_of_trivial_quotient_action
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (homomorphism : subgroup →* H) (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (htrivial : ∀ (member : actor) (element : subgroup),
      homomorphism ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩ =
          homomorphism element) (element : subgroup) :
    ∃ fixedElement : subgroup, (fixedElement : G) ∈ Subgroup.centralizer (actor : Set G) ∧
      homomorphism fixedElement = homomorphism element := by
  have : Fact prime.Prime := ⟨hprime⟩
  let fiber := {other : subgroup // homomorphism other = homomorphism element}
  let action : MulAction actor fiber :=
    { smul := fun member other =>
        ⟨⟨member * (other : subgroup) * (member : G)⁻¹,
          Subgroup.le_normalizer_iff.mp hnormalizes member member.property
            (other : subgroup) (other : subgroup).property⟩,
          (htrivial member other).trans other.property⟩
      one_smul := fun other => Subtype.ext (Subtype.ext (by
        change (1 : G) * ((other : subgroup) : G) * (1 : G)⁻¹ = ((other : subgroup) : G)
        simp))
      mul_smul := fun first second other => Subtype.ext (Subtype.ext (by
        change ((first : G) * (second : G)) * ((other : subgroup) : G) *
            ((first : G) * (second : G))⁻¹ =
          (first : G) * ((second : G) * ((other : subgroup) : G) * (second : G)⁻¹) * (first : G)⁻¹
        simp [mul_assoc])) }
  let : MulAction actor fiber := action
  have hcard : Nat.card fiber = Nat.card homomorphism.ker :=
    (Nat.card_congr (kernelEquivFiber homomorphism element)).symm
  obtain ⟨fixedElement, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard.symm ▸ hkernelComplement)
  refine ⟨fixedElement, ?_, fixedElement.property⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have heq := congrArg (fun value : fiber => ((value : subgroup) : G))
    (MulAction.mem_fixedPoints.mp hfixed (⟨member, hmember⟩ : actor))
  change member * ((fixedElement : subgroup) : G) * member⁻¹ = ((fixedElement : subgroup) : G) at heq
  have hmul := congrArg (fun value : G => value * member) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

theorem coprime_commutator_centralizer_factorization {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    subgroup = ⁅subgroup, actor⁆ ⊔ (subgroup ⊓ Subgroup.centralizer (actor : Set G)) := by
  have hcommutatorLe : ⁅subgroup, actor⁆ ≤ subgroup :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizes
  let internalCommutator := (⁅subgroup, actor⁆).subgroupOf subgroup
  have hinternalNormal : internalCommutator.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommutatorLe).mpr
      (Subgroup.normalizer_commutator_ge_left subgroup actor)
  have : internalCommutator.Normal := hinternalNormal
  let quotient := QuotientGroup.mk' internalCommutator
  have hquotientKernel : quotient.ker = internalCommutator := QuotientGroup.ker_mk' _
  have hkernelComplement : ¬prime ∣ Nat.card quotient.ker := by
    rw [hquotientKernel]
    exact fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card _))
  have htrivial : ∀ (member : actor) (element : subgroup),
      quotient ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩ =
          quotient element := by
    intro member element
    let conjugate : subgroup := ⟨member * element * (member : G)⁻¹,
      Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩
    have hcommutator : conjugate * element⁻¹ ∈ quotient.ker := by
      rw [hquotientKernel]
      change (member : G) * (element : G) * (member : G)⁻¹ * (element : G)⁻¹ ∈ ⁅subgroup, actor⁆
      rw [← commutatorElement_def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator member.property element.property
    have hmapped := MonoidHom.mem_ker.mp hcommutator
    rw [map_mul, map_inv] at hmapped
    exact mul_inv_eq_one.mp hmapped
  apply le_antisymm
  · intro element helement
    obtain ⟨fixedElement, hcentralizer, heq⟩ :=
      exists_centralizer_with_same_image_of_trivial_quotient_action prime hprime actor subgroup
        hpgroup hnormalizes quotient hkernelComplement htrivial ⟨element, helement⟩
    have hdifference : (⟨element, helement⟩ : subgroup) * fixedElement⁻¹ ∈ quotient.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, ← heq, mul_inv_cancel]
    rw [hquotientKernel] at hdifference
    have hfactor : element * (fixedElement : G)⁻¹ ∈ ⁅subgroup, actor⁆ := hdifference
    have hproduct := Subgroup.mul_mem_sup hfactor
      (show (fixedElement : G) ∈ subgroup ⊓ Subgroup.centralizer (actor : Set G) from
        ⟨fixedElement.property, hcentralizer⟩)
    simpa only [inv_mul_cancel_right] using hproduct
  · exact sup_le hcommutatorLe inf_le_left

theorem normal_subgroup_sup_factorization {G : Type u} [Group G]
    (subgroup normalSubgroup other : Subgroup G) (hnormalLe : normalSubgroup ≤ subgroup)
    (hotherLe : other ≤ subgroup) (hnormal : (normalSubgroup.subgroupOf subgroup).Normal)
    (heq : subgroup = normalSubgroup ⊔ other) (element : G) (hmem : element ∈ subgroup) :
    ∃ first ∈ normalSubgroup, ∃ second ∈ other, first * second = element := by
  have : (normalSubgroup.subgroupOf subgroup).Normal := hnormal
  have hinternal : (⟨element, hmem⟩ : subgroup) ∈
      normalSubgroup.subgroupOf subgroup ⊔ other.subgroupOf subgroup := by
    rw [← Subgroup.subgroupOf_sup hnormalLe hotherLe, ← heq, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨first, hfirst, second, hsecond, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hinternal
  exact ⟨first, hfirst, second, hsecond, congrArg Subtype.val heq⟩

theorem coprime_commutator_idempotent {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    ⁅⁅subgroup, actor⁆, actor⁆ = ⁅subgroup, actor⁆ := by
  have hcommutatorLe : ⁅subgroup, actor⁆ ≤ subgroup :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizes
  have hcommutatorNormal : ((⁅subgroup, actor⁆).subgroupOf subgroup).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommutatorLe).mpr
      (Subgroup.normalizer_commutator_ge_left subgroup actor)
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.normalizer_commutator_ge_right subgroup actor)
  · apply Subgroup.commutator_le.mpr
    intro element helement member hmember
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ := normal_subgroup_sup_factorization
      subgroup ⁅subgroup, actor⁆ (subgroup ⊓ Subgroup.centralizer (actor : Set G))
      hcommutatorLe inf_le_left hcommutatorNormal
      (coprime_commutator_centralizer_factorization prime hprime actor subgroup hpgroup hcomplement
        hnormalizes) element helement
    have hsecondCommute : Commute second member :=
      (Subgroup.mem_centralizer_iff.mp hsecond.2 member hmember).symm
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hsecondCommute, mul_one, mul_inv_cancel, one_mul]
    exact Subgroup.commutator_mem_commutator hfirst hmember

end CFSG.RankThreeEvenClassification.Helpers
