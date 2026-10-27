module

public import CFSG.CharacterTheory.TwoRankLowerBound.PiTrace
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

attribute [local instance] RestrictScalars.module

@[expose] noncomputable def restrictScalarsLinearEquiv {G module : Type*} [Group G]
    [AddCommGroup module] [Module ℂ module] [Module (MonoidAlgebra ℂ G) module]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) module] :
    RestrictScalars ℂ (MonoidAlgebra ℂ G) module ≃ₗ[ℂ] module :=
  { RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) module with
    map_smul' := by
      intro scalar element
      exact (RestrictScalars.addEquiv_map_smul ℂ (MonoidAlgebra ℂ G) module scalar element).trans
        (algebraMap_smul (MonoidAlgebra ℂ G) scalar
          (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) module element)) }

theorem ofModule_isIrreducible {G module : Type*} [Group G]
    [AddCommGroup module] [Module (MonoidAlgebra ℂ G) module]
    [IsSimpleModule (MonoidAlgebra ℂ G) module] :
    @Representation.IsIrreducible G ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) module)
      _ _ _ (RestrictScalars.module ℂ (MonoidAlgebra ℂ G) module)
      (Representation.ofModule (k := ℂ) (G := G) module) := by
  exact (Subrepresentation.submoduleSubrepresentationOrderIso
    (A := ℂ) (G := G) (M := module)).isSimpleOrder_iff.mp inferInstance

theorem representation_exists_simple_module_decomposition {G vector : Type*}
    [Group G] [Finite G] [AddCommGroup vector] [Module ℂ vector]
    [FiniteDimensional ℂ vector] (representation : Representation ℂ G vector) :
    ∃ (size : ℕ) (summand : Fin size → Submodule (MonoidAlgebra ℂ G) representation.asModule)
      (_equivalence : representation.asModule ≃ₗ[MonoidAlgebra ℂ G]
        (∀ label : Fin size, summand label)),
      ∀ label, IsSimpleModule (MonoidAlgebra ℂ G) (summand label) := by
  let : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let : Module.Finite ℂ representation.asModule :=
    Module.Finite.equiv representation.asModuleEquiv.symm
  let : Module.Finite (MonoidAlgebra ℂ G) representation.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ G) representation.asModule
  obtain ⟨size, summand, equivalence, hsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
      (MonoidAlgebra ℂ G) representation.asModule
  exact ⟨size, summand, equivalence.trans DFinsupp.linearEquivFunOnFintype, hsimple⟩

set_option backward.isDefEq.respectTransparency false in
theorem representation_character_eq_simple_module_sum {G vector : Type*}
    [Group G] [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) {size : ℕ}
    (summand : Fin size → Submodule (MonoidAlgebra ℂ G) representation.asModule)
    (equivalence : representation.asModule ≃ₗ[MonoidAlgebra ℂ G]
      (∀ label : Fin size, summand label)) (element : G) :
    representation.character element =
      ∑ label : Fin size,
        @Representation.character G ℂ
          (RestrictScalars ℂ (MonoidAlgebra ℂ G) (summand label)) _ _ _
          (RestrictScalars.module ℂ (MonoidAlgebra ℂ G) (summand label))
          (Representation.ofModule (k := ℂ) (G := G) (summand label)) element := by
  let : Module.Finite ℂ representation.asModule :=
    Module.Finite.equiv representation.asModuleEquiv.symm
  let : ∀ label : Fin size, FiniteDimensional ℂ (summand label) := fun label =>
    Module.Finite.of_injective ((summand label).subtype.restrictScalars ℂ)
      (summand label).subtype_injective
  let transport : vector ≃ₗ[ℂ] (∀ label : Fin size, summand label) :=
    representation.asModuleEquiv.symm.trans (equivalence.restrictScalars ℂ)
  let component := fun label : Fin size =>
    (MonoidAlgebra.of ℂ G element • (1 : Module.End ℂ (summand label)))
  have haction : ∀ function label,
      transport.conj (representation element) function label = component label (function label) := by
    intro function label
    change equivalence
      (representation.asModuleEquiv.symm
        (representation element (transport.symm function))) label = _
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
    simp [transport, component]
  have htrace := LinearMap.trace_conj' (representation element) transport
  have hsum := trace_pi_component_operator (fun label : Fin size => summand label)
    (transport.conj (representation element)) component haction
  change LinearMap.trace ℂ vector (representation element) = _
  rw [← htrace, hsum]
  apply Finset.sum_congr rfl
  intro label _
  let scalarTransport := restrictScalarsLinearEquiv (G := G) (module := summand label)
  have hconj : scalarTransport.conj
      (Representation.ofModule (k := ℂ) (G := G) (summand label) element) = component label := by
    ext member
    rfl
  rw [← hconj]
  exact LinearMap.trace_conj' _ scalarTransport

end CFSG.TwoRankLowerBound.Helpers
