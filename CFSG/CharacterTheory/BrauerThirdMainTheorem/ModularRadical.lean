module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ModularFixedPoints
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem modular_ofModule'_asAlgebraHom (field : Type*) [Field field]
    (G : Type*) [Group G] (space : Type*)
    [AddCommGroup space] [Module field space] [Module (MonoidAlgebra field G) space]
    [IsScalarTower field (MonoidAlgebra field G) space] :
    (Representation.ofModule' (k := field) (G := G) space).asAlgebraHom =
      Algebra.lsmul field field space := by
  rw [Representation.asAlgebraHom_def]
  exact (MonoidAlgebra.lift field (Module.End field space) G).apply_symm_apply _

theorem modular_ofModule'_isIrreducible (field : Type*) [Field field]
    (G : Type*) [Group G] (space : Type*)
    [AddCommGroup space] [Module field space] [Module (MonoidAlgebra field G) space]
    [IsScalarTower field (MonoidAlgebra field G) space]
    [IsSimpleModule (MonoidAlgebra field G) space] :
    (Representation.ofModule' (k := field) (G := G) space).IsIrreducible := by
  let representation := Representation.ofModule' (k := field) (G := G) space
  let equivalence : representation.asModule ≃ₗ[MonoidAlgebra field G] space := {
    __ := representation.asModuleEquiv.toAddEquiv
    map_smul' coefficient vector := by
      change representation.asModuleEquiv (coefficient • vector) =
        coefficient • representation.asModuleEquiv vector
      rw [representation.asModuleEquiv_map_smul, modular_ofModule'_asAlgebraHom]
      rfl
  }
  exact (representation.irreducible_iff_isSimpleModule_asModule).mpr
    (IsSimpleModule.congr equivalence)

theorem normalPSubgroup_quotient_representation_factor (prime : ℕ) (hprime : prime.Prime)
    (field : Type*) [Field field] [CharP field prime]
    (G : Type*) [Group G] (subgroup : Subgroup G) [subgroup.Normal] [Finite subgroup]
    (hpGroup : IsPGroup prime subgroup) (space : Type*) [AddCommGroup space] [Module field space]
    (representation : Representation field G space) [representation.IsIrreducible] :
    ∃ quotientRepresentation : Representation field (G ⧸ subgroup) space,
      quotientRepresentation.asAlgebraHom.comp
        (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)) =
          representation.asAlgebraHom := by
  have hkernel : subgroup ≤ representation.ker := by
    intro element hmember
    change representation element = 1
    exact normalPSubgroup_irreducible_trivial prime hprime G subgroup hpGroup field space
      representation ⟨element, hmember⟩
  let quotientRepresentation := QuotientGroup.lift subgroup representation hkernel
  refine ⟨quotientRepresentation, ?_⟩
  apply (MonoidAlgebra.lift field (Module.End field space) G).symm.injective
  apply MonoidHom.ext
  intro element
  simp only [MonoidAlgebra.lift_symm_apply,
    AlgHom.comp_apply, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single, one_smul]
  exact QuotientGroup.lift_mk subgroup hkernel element

theorem normalPSubgroup_quotient_kernel_le_jacobson (prime : ℕ) (hprime : prime.Prime)
    (field : Type*) [Field field] [CharP field prime]
    (G : Type*) [Group G] (subgroup : Subgroup G) [subgroup.Normal] [Finite subgroup]
    (hpGroup : IsPGroup prime subgroup) :
    RingHom.ker (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)).toRingHom ≤
      Ring.jacobson (MonoidAlgebra field G) := by
  intro coefficient hcoefficient
  rw [Ring.jacobson_eq_sInf_isMaximal]
  apply Submodule.mem_sInf.mpr
  intro maximal hmaximal
  let : IsSimpleModule (MonoidAlgebra field G) (MonoidAlgebra field G ⧸ maximal) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hmaximal)
  let representation := Representation.ofModule' (k := field) (G := G)
    (MonoidAlgebra field G ⧸ maximal)
  let : representation.IsIrreducible := modular_ofModule'_isIrreducible field G _
  obtain ⟨quotientRepresentation, hfactor⟩ := normalPSubgroup_quotient_representation_factor
    prime hprime field G subgroup hpGroup _ representation
  have hzero : representation.asAlgebraHom coefficient = 0 := by
    rw [← hfactor]
    change quotientRepresentation.asAlgebraHom
      ((MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)) coefficient) = 0
    rw [show (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)) coefficient = 0
      from hcoefficient, map_zero]
  rw [modular_ofModule'_asAlgebraHom] at hzero
  have hquotient := congrArg (fun operator => operator (Submodule.Quotient.mk (1 : MonoidAlgebra field G)))
    hzero
  rw [Algebra.lsmul_apply, ← Submodule.Quotient.mk_smul] at hquotient
  simp only [smul_eq_mul, mul_one, LinearMap.zero_apply] at hquotient
  exact (Submodule.Quotient.mk_eq_zero maximal).mp hquotient

theorem normalPSubgroup_quotient_kernel_nilpotent (prime : ℕ) (hprime : prime.Prime)
    (field : Type*) [Field field] [CharP field prime]
    (G : Type*) [Group G] [Finite G] (subgroup : Subgroup G) [subgroup.Normal]
    (hpGroup : IsPGroup prime subgroup) :
    IsNilpotent (RingHom.ker
      (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)).toRingHom) := by
  let : IsArtinianRing (MonoidAlgebra field G) := IsArtinianRing.of_finite field _
  obtain ⟨exponent, hexponent⟩ := IsArtinianRing.isNilpotent_jacobson_bot
    (R := MonoidAlgebra field G)
  refine ⟨exponent, ?_⟩
  apply bot_unique
  change RingHom.ker
    (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)).toRingHom ^ exponent ≤ ⊥
  rw [Ideal.jacobson_bot, Ideal.zero_eq_bot] at hexponent
  rw [← hexponent]
  have hle := normalPSubgroup_quotient_kernel_le_jacobson prime hprime field G subgroup hpGroup
  clear hexponent
  induction exponent with
  | zero => exact le_rfl
  | succ exponent hinduction =>
      exact Ideal.mul_mono hinduction hle

end CFSG.BrauerThirdMainTheorem.Helpers
