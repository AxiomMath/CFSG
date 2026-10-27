module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterDecomposition

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse vectorUniverse otherVectorUniverse

structure FiniteComplexRepresentation (G : Type groupUniverse) [Group G] where
  vector : Type vectorUniverse
  [addCommGroup : AddCommGroup vector]
  [module : Module ℂ vector]
  [finiteDimensional : FiniteDimensional ℂ vector]
  representation : Representation ℂ G vector

attribute [instance] FiniteComplexRepresentation.addCommGroup
  FiniteComplexRepresentation.module FiniteComplexRepresentation.finiteDimensional

noncomputable abbrev FiniteComplexRepresentation.character {G : Type groupUniverse} [Group G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G) : G → ℂ :=
  data.representation.character

@[expose] def FiniteComplexRepresentation.IsIrreducible {G : Type groupUniverse} [Group G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G) : Prop :=
  data.representation.IsIrreducible

attribute [local instance] RestrictScalars.module

set_option backward.isDefEq.respectTransparency false in
@[expose] noncomputable def moduleFiniteComplexRepresentation {G module : Type*} [Group G]
    [AddCommGroup module] [Module ℂ module] [Module (MonoidAlgebra ℂ G) module]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) module] [FiniteDimensional ℂ module] :
    FiniteComplexRepresentation G :=
  { vector := RestrictScalars ℂ (MonoidAlgebra ℂ G) module
    module := RestrictScalars.module ℂ (MonoidAlgebra ℂ G) module
    finiteDimensional := Module.Finite.equiv
      (restrictScalarsLinearEquiv (G := G) (module := module)).symm
    representation := Representation.ofModule (k := ℂ) (G := G) module }

theorem moduleFiniteComplexRepresentation_isIrreducible {G module : Type*} [Group G]
    [AddCommGroup module] [Module ℂ module] [Module (MonoidAlgebra ℂ G) module]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) module] [FiniteDimensional ℂ module]
    [IsSimpleModule (MonoidAlgebra ℂ G) module] :
    (moduleFiniteComplexRepresentation (G := G) (module := module)).IsIrreducible :=
  ofModule_isIrreducible

set_option backward.isDefEq.respectTransparency false in
theorem finiteComplexRepresentation_exists_irreducible_character_sum
    {G : Type groupUniverse} [Group G] [Finite G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G) :
    ∃ (size : ℕ) (summand : Fin size → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G),
      (∀ label, (summand label).IsIrreducible) ∧
      ∀ element : G, data.character element = ∑ label, (summand label).character element := by
  obtain ⟨size, module, equivalence, hsimple⟩ :=
    representation_exists_simple_module_decomposition data.representation
  let : Module.Finite ℂ data.representation.asModule :=
    Module.Finite.equiv data.representation.asModuleEquiv.symm
  let : ∀ label : Fin size, FiniteDimensional ℂ (module label) := fun label =>
    Module.Finite.of_injective ((module label).subtype.restrictScalars ℂ)
      (module label).subtype_injective
  let summand := fun label : Fin size =>
    moduleFiniteComplexRepresentation (G := G) (module := module label)
  refine ⟨size, summand, ?_, ?_⟩
  · intro label
    let : IsSimpleModule (MonoidAlgebra ℂ G) (module label) := hsimple label
    exact moduleFiniteComplexRepresentation_isIrreducible
  · intro element
    exact representation_character_eq_simple_module_sum data.representation module equivalence element

@[expose] noncomputable def coinducedFiniteComplexRepresentation
    {G : Type groupUniverse} [Group G] [Fintype G] (subgroup : Subgroup G)
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} subgroup) :
    FiniteComplexRepresentation.{groupUniverse, max groupUniverse vectorUniverse} G :=
  { vector := Representation.coindV subgroup.subtype data.representation
    representation := Representation.coind subgroup.subtype data.representation }

theorem coinducedFiniteComplexRepresentation_character {G : Type groupUniverse}
    [Group G] [Fintype G] (subgroup : Subgroup G)
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} subgroup) (element : G) :
    (coinducedFiniteComplexRepresentation subgroup data).character element =
      inducedFunction subgroup data.character element :=
  coinduction_character_eq_inducedFunction subgroup data.representation element

@[expose] noncomputable def characterPairing {G : Type*} [Group G] [Fintype G]
    (left right : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ element : G, left element * right element⁻¹

theorem characterPairing_irreducible {G : Type groupUniverse} [Group G] [Fintype G]
    (left : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (right : FiniteComplexRepresentation.{groupUniverse, otherVectorUniverse} G)
    (hleft : left.IsIrreducible) (hright : right.IsIrreducible) :
    characterPairing left.character right.character = if left.character = right.character then 1
      else 0 := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : left.representation.IsIrreducible := hleft
  let : right.representation.IsIrreducible := hright
  have horth := Representation.char_orthonormal left.representation right.representation
  by_cases hequal : left.character = right.character
  · rw [ite_eq_left hequal, ← hequal]
    have hself := Representation.char_orthonormal left.representation left.representation
    simpa [characterPairing, FiniteComplexRepresentation.character,
      show Nonempty (left.representation.Equiv left.representation) from
        ⟨Representation.Equiv.refl _⟩] using hself
  · have hnequiv : ¬Nonempty (right.representation.Equiv left.representation) := by
      rintro ⟨equivalence⟩
      exact hequal (Representation.char_iso equivalence).symm
    simpa [characterPairing, hequal, hnequiv] using horth

theorem irreducible_character_degree_ne_zero {G : Type groupUniverse} [Group G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : data.IsIrreducible) : data.character 1 ≠ 0 := by
  let : data.representation.IsIrreducible := hirreducible
  let : Nontrivial data.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) data.representation.asModule
  let : Nontrivial data.vector := data.representation.asModuleEquiv.symm.toEquiv.nontrivial
  rw [FiniteComplexRepresentation.character, Representation.char_one]
  exact Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := data.vector)).ne'

theorem characterPairing_expansion_right {G index : Type*} [Group G] [Fintype G] [Fintype index]
    (function : G → ℂ) (character : index → G → ℂ) (coefficient : index → ℂ) :
    characterPairing function (fun element => ∑ label, coefficient label * character label element) =
      ∑ label, coefficient label * characterPairing function (character label) := by
  unfold characterPairing
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro element _
  ring

theorem characterPairing_expansion_left {G index : Type*} [Group G] [Fintype G] [Fintype index]
    (function : G → ℂ) (character : index → G → ℂ) (coefficient : index → ℂ) :
    characterPairing (fun element => ∑ label, coefficient label * character label element) function =
      ∑ label, coefficient label * characterPairing (character label) function := by
  unfold characterPairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

@[expose] noncomputable def principalFiniteComplexRepresentation (G : Type groupUniverse) [Group G] :
    FiniteComplexRepresentation.{groupUniverse, 0} G :=
  { vector := ℂ
    representation := Representation.trivial ℂ G ℂ }

theorem principalFiniteComplexRepresentation_character (G : Type groupUniverse) [Group G] :
    (principalFiniteComplexRepresentation G).character = 1 := by
  ext element
  change LinearMap.trace ℂ ℂ (1 : Module.End ℂ ℂ) = 1
  simp

theorem principalFiniteComplexRepresentation_isIrreducible
    (G : Type groupUniverse) [Group G] :
    (principalFiniteComplexRepresentation G).IsIrreducible := by
  let representation : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  change IsSimpleOrder (Subrepresentation representation)
  have hnontrivial : (⊥ : Subrepresentation representation) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊥ : Subrepresentation representation) := by
      rw [hequal]
      trivial
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation representation) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro subrepresentation
  obtain hbot | htop := eq_bot_or_eq_top subrepresentation.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

end CFSG.TwoRankLowerBound.Helpers
