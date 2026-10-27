module

public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupAugmentationNilpotent
public import CFSG.Open.LocalVocabulary

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem ideal_pow_succ_left {ring : Type*} [Semiring ring]
    (ideal : Ideal ring) [ideal.IsTwoSided] (exponent : ℕ) :
    ideal * ideal ^ exponent = ideal ^ (exponent + 1) := by
  induction exponent with
  | zero =>
    change ideal * 1 = 1 * ideal
    rw [Ideal.one_eq_top, Ideal.mul_top, Ideal.top_mul]
  | succ exponent hinduction =>
    change ideal * (ideal ^ exponent * ideal) = (ideal ^ exponent * ideal) * ideal
    rw [← Ideal.mul_assoc, hinduction]
    rfl

theorem nilpotent_ideal_exists_annihilated_vector {ring vector : Type*}
    [Ring ring] [AddCommGroup vector] [Module ring vector] [Nontrivial vector]
    (ideal : Ideal ring) [ideal.IsTwoSided] (hnilpotent : IsNilpotent ideal) :
    ∃ value : vector, value ≠ 0 ∧ ∀ coefficient ∈ ideal, coefficient • value = 0 := by
  have hexists : ∃ exponent : ℕ,
      ideal ^ exponent • (⊤ : Submodule ring vector) = ⊥ := by
    obtain ⟨exponent, hpower⟩ := hnilpotent
    refine ⟨exponent, ?_⟩
    rw [hpower, Ideal.zero_eq_bot, Submodule.bot_smul]
  let exponent := Nat.find hexists
  have hpositive : 0 < exponent := by
    by_contra hnot
    have hequal : exponent = 0 := by omega
    have hzero := Nat.find_spec hexists
    rw [← show exponent = Nat.find hexists from rfl, hequal] at hzero
    have hone : ideal ^ 0 • (⊤ : Submodule ring vector) = ⊤ := by
      apply le_antisymm le_top
      intro value _
      simpa only [one_smul] using
        (Submodule.smul_mem_smul (I := ideal ^ 0) (N := (⊤ : Submodule ring vector))
          (show (1 : ring) ∈ ideal ^ 0 from by
            change (1 : ring) ∈ (1 : Ideal ring)
            rw [Ideal.one_eq_top]
            exact Submodule.mem_top) (Submodule.mem_top : value ∈ ⊤))
    rw [hone] at hzero
    exact top_ne_bot hzero
  have hprevious : ideal ^ (exponent - 1) • (⊤ : Submodule ring vector) ≠ ⊥ :=
    Nat.find_min hexists (by change exponent - 1 < exponent; omega)
  obtain ⟨value, hmember, hnonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprevious
  refine ⟨value, hnonzero, ?_⟩
  intro coefficient hcoefficient
  have hproduct : coefficient • value ∈
      ideal • (ideal ^ (exponent - 1) • (⊤ : Submodule ring vector)) :=
    Submodule.smul_mem_smul hcoefficient hmember
  rw [← Submodule.mul_smul] at hproduct
  have hpower : ideal * ideal ^ (exponent - 1) = ideal ^ exponent := by
    have hsuccessor : exponent - 1 + 1 = exponent := by omega
    rw [ideal_pow_succ_left, hsuccessor]
  rw [hpower, Nat.find_spec hexists, Submodule.mem_bot] at hproduct
  exact hproduct

theorem p_group_representation_exists_fixed_vector {field group vector : Type*}
    [Field field] [Group group] [Finite group]
    [AddCommGroup vector] [Module field vector] [Nontrivial vector]
    (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (hgroup : IsPGroup prime group) (representation : Representation field group vector) :
    ∃ value : vector, value ≠ 0 ∧ ∀ element, representation element value = value := by
  let : Module (MonoidAlgebra field group) vector :=
    Module.compHom vector representation.asAlgebraHom.toRingHom
  obtain ⟨value, hnonzero, hannihilated⟩ := nilpotent_ideal_exists_annihilated_vector (vector := vector)
    (RingHom.ker (groupAlgebraAugmentation field group))
    (p_group_augmentation_nilpotent (field := field) prime hgroup)
  refine ⟨value, hnonzero, ?_⟩
  intro element
  have hmember : MonoidAlgebra.single element (1 : field) - 1 ∈
      RingHom.ker (groupAlgebraAugmentation field group) := by
    rw [RingHom.mem_ker, map_sub, groupAlgebraAugmentation_single, map_one, sub_self]
  have hzero := hannihilated _ hmember
  change representation.asAlgebraHom (MonoidAlgebra.single element 1 - 1) value = 0 at hzero
  rw [map_sub, Representation.asAlgebraHom_single, map_one, one_smul,
    LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hzero
  exact hzero

theorem normal_p_subgroup_irreducible_action_trivial {field group vector : Type*}
    [Field field] [Group group] [Finite group]
    [AddCommGroup vector] [Module field vector]
    (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (representation : Representation field group vector) [representation.IsIrreducible]
    (subgroup : Subgroup group) [subgroup.Normal] (hgroup : IsPGroup prime subgroup) :
    ∀ element : subgroup, representation element.val = 1 := by
  let : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra field group) representation.asModule
  let : Nontrivial vector := representation.asModuleEquiv.symm.toEquiv.nontrivial
  let restricted : Representation field subgroup vector := representation.comp subgroup.subtype
  obtain ⟨value, hnonzero, hfixed⟩ :=
    p_group_representation_exists_fixed_vector prime hgroup restricted
  let fixed : Submodule (MonoidAlgebra field group) representation.asModule :=
    { carrier := {value | ∀ element : subgroup,
        MonoidAlgebra.of field group element.val • value = value}
      zero_mem' := fun _ => smul_zero _
      add_mem' := fun hleft hright element => by rw [smul_add, hleft, hright]
      smul_mem' := by
        intro coefficient vectorValue hvector element
        induction coefficient using MonoidAlgebra.induction_on with
        | of conjugator =>
          have hconjugate : conjugator⁻¹ * element.val * conjugator ∈ subgroup :=
            (inferInstance : subgroup.Normal).conj_mem' element.val element.property conjugator
          have hfixedConjugate := hvector ⟨conjugator⁻¹ * element.val * conjugator, hconjugate⟩
          rw [← mul_smul, ← map_mul, show element.val * conjugator =
            conjugator * (conjugator⁻¹ * element.val * conjugator) by group, map_mul, mul_smul,
            hfixedConjugate]
        | add left right hleft hright => rw [add_smul, smul_add, hleft, hright]
        | smul scalar coefficient hcoefficient =>
          rw [smul_assoc, smul_comm (MonoidAlgebra.of field group element.val) scalar, hcoefficient] }
  have hnonbot : fixed ≠ ⊥ := by
    intro hbot
    have hmember : representation.asModuleEquiv.symm value ∈ fixed := by
      intro element
      have hequal := hfixed element
      change representation element.val value = value at hequal
      rw [← Representation.asModuleEquiv_symm_map_rho, hequal]
    rw [hbot, Submodule.mem_bot] at hmember
    exact hnonzero (representation.asModuleEquiv.symm.injective hmember)
  have htop : fixed = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top fixed).resolve_left hnonbot
  intro element
  ext vectorValue
  have hmember : representation.asModuleEquiv.symm vectorValue ∈ fixed := htop ▸ Submodule.mem_top
  have hequal := hmember element
  rw [← Representation.asModuleEquiv_symm_map_rho] at hequal
  exact representation.asModuleEquiv.symm.injective hequal

end CFSG.TwoRankLowerBound.Helpers
