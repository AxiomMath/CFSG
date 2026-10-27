module

public import CFSG.Assembly.OrderReductions.TIInductionIsometry
public import CFSG.Assembly.OrderReductions.InducedRepresentation

public section

namespace CFSG.OrderReductions.CharacterSpan

universe level

@[expose] def irreducibleCharacters (field group : Type level) [Field field] [Group group] : Set (group → field) :=
  {function | ∃ representation : FDRep field group,
    Representation.IsIrreducible representation.ρ ∧ representation.character = function}

@[expose] def virtualCharacters (field group : Type level) [Field field] [Group group] : Submodule ℤ (group → field) :=
  Submodule.span ℤ (irreducibleCharacters field group)

theorem complementary_submodules {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (representation : Representation field group vector)
    (first second : Subrepresentation representation) (complementary : IsCompl first second) :
    IsCompl first.toSubmodule second.toSubmodule := by
  apply IsCompl.mk
  · apply disjoint_iff.mpr
    rw [← Subrepresentation.toSubmodule_inf, complementary.inf_eq_bot]
    rfl
  · apply codisjoint_iff.mpr
    rw [← Subrepresentation.toSubmodule_sup, complementary.sup_eq_top]
    rfl

theorem complementary_character_sum {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (representation : Representation field group vector) (first second : Subrepresentation representation)
    (complementary : IsCompl first second) :
    representation.character = first.toRepresentation.character + second.toRepresentation.character := by
  have subspaces_complementary := complementary_submodules representation first second complementary
  have first_projection : LinearMap.IsProj first.toSubmodule
      (first.toSubmodule.projection second.toSubmodule subspaces_complementary) := by
    refine ⟨fun element => Submodule.projection_apply_mem subspaces_complementary element, ?_⟩
    intro element membership
    exact Submodule.projection_apply_left subspaces_complementary ⟨element, membership⟩
  have second_projection : LinearMap.IsProj second.toSubmodule
      (second.toSubmodule.projection first.toSubmodule subspaces_complementary.symm) := by
    refine ⟨fun element => Submodule.projection_apply_mem subspaces_complementary.symm element, ?_⟩
    intro element membership
    exact Submodule.projection_apply_left subspaces_complementary.symm ⟨element, membership⟩
  funext actor
  change LinearMap.trace field vector (representation actor) =
    LinearMap.trace field first.toSubmodule ((representation actor).restrict
      (fun element membership => first.apply_mem_toSubmodule actor membership)) +
      LinearMap.trace field second.toSubmodule ((representation actor).restrict
        (fun element membership => second.apply_mem_toSubmodule actor membership))
  rw [CFSG.OrderReductions.InducedRepresentation.trace_restrict_projection _ _ _ _ first_projection,
    CFSG.OrderReductions.InducedRepresentation.trace_restrict_projection _ _ _ _ second_projection,
    Submodule.projection_eq_id_sub_projection subspaces_complementary,
    LinearMap.comp_sub, LinearMap.comp_id, map_sub]
  abel

theorem character_mem_virtualCharacters {field group vector : Type level} [Field field] [CharZero field]
    [Group group] [Finite group] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (representation : Representation field group vector) :
    representation.character ∈ virtualCharacters field group := by
  classical
  have : NeZero (Nat.card group : field) := ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩
  generalize dimension_eq : Module.finrank field vector = dimension
  induction dimension using Nat.strong_induction_on generalizing vector with
  | h dimension induction_hypothesis =>
      by_cases nontrivial : Nontrivial vector
      · have : Nontrivial vector := nontrivial
        by_cases irreducible : representation.IsIrreducible
        · apply Submodule.subset_span
          exact ⟨FDRep.of representation, irreducible, rfl⟩
        · have : Nontrivial (Subrepresentation representation) :=
            nontrivial_of_ne (⊥ : Subrepresentation representation) ⊤ (by
              intro equal
              exact bot_ne_top (congrArg Subrepresentation.toSubmodule equal))
          have exists_proper : ∃ first : Subrepresentation representation, first ≠ ⊥ ∧ first ≠ ⊤ := by
            by_contra none
            apply irreducible
            apply (isSimpleOrder_iff _).mpr
            refine ⟨inferInstance, ?_⟩
            intro first
            by_contra neither
            push Not at neither
            exact none ⟨first, neither⟩
          obtain ⟨first, first_ne_bot, first_ne_top⟩ := exists_proper
          obtain ⟨second, complementary⟩ := ComplementedLattice.exists_isCompl first
          have subspaces_complementary := complementary_submodules representation first second complementary
          have first_subspace_ne_bot : first.toSubmodule ≠ ⊥ := by
            intro equal
            exact first_ne_bot (Subrepresentation.ext equal)
          have first_subspace_ne_top : first.toSubmodule ≠ ⊤ := by
            intro equal
            exact first_ne_top (Subrepresentation.ext equal)
          have second_subspace_ne_top : second.toSubmodule ≠ ⊤ := by
            intro equal
            have inf_eq := subspaces_complementary.inf_eq_bot
            rw [equal, inf_top_eq] at inf_eq
            exact first_subspace_ne_bot inf_eq
          have first_smaller : Module.finrank field first.toSubmodule < dimension := by
            rw [← dimension_eq]
            exact Submodule.finrank_lt first_subspace_ne_top
          have second_smaller : Module.finrank field second.toSubmodule < dimension := by
            rw [← dimension_eq]
            exact Submodule.finrank_lt second_subspace_ne_top
          have first_mem := induction_hypothesis _ first_smaller first.toRepresentation rfl
          have second_mem := induction_hypothesis _ second_smaller second.toRepresentation rfl
          rw [complementary_character_sum representation first second complementary]
          exact (virtualCharacters field group).add_mem first_mem second_mem
      · have : Subsingleton vector := not_nontrivial_iff_subsingleton.mp nontrivial
        have character_zero : representation.character = 0 := by
          funext actor
          change LinearMap.trace field vector (representation actor) = 0
          rw [Subsingleton.elim (representation actor) 0, map_zero]
        rw [character_zero]
        exact (virtualCharacters field group).zero_mem

theorem induced_mem_virtualCharacters {field group : Type level} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (function : subgroup → field)
    (virtuality : function ∈ virtualCharacters field subgroup) :
    CFSG.OrderReductions.TIClassFunctionInduction.inducedFunction subgroup function ∈ virtualCharacters field group := by
  change (CFSG.OrderReductions.InducedRepresentation.linearInduction subgroup) function ∈ virtualCharacters field group
  induction virtuality using Submodule.span_induction with
  | mem function membership =>
      obtain ⟨representation, _, character_eq⟩ := membership
      rw [← character_eq]
      change CFSG.OrderReductions.TIClassFunctionInduction.inducedFunction subgroup (Representation.character representation.ρ) ∈ _
      rw [← CFSG.OrderReductions.InducedRepresentation.induced_character]
      exact character_mem_virtualCharacters _
  | zero =>
      rw [map_zero]
      exact (virtualCharacters field group).zero_mem
  | add first second _ _ first_mem second_mem =>
      rw [map_add]
      exact (virtualCharacters field group).add_mem first_mem second_mem
  | smul coefficient function _ membership =>
      rw [map_zsmul]
      exact (virtualCharacters field group).smul_mem coefficient membership

@[expose] noncomputable def irreducibleRepresentative {field group : Type level} [Field field] [Group group]
    (current : irreducibleCharacters field group) : FDRep field group :=
  Classical.choose current.property

theorem irreducibleRepresentative_irreducible {field group : Type level} [Field field] [Group group]
    (current : irreducibleCharacters field group) :
    Representation.IsIrreducible (irreducibleRepresentative current).ρ :=
  (Classical.choose_spec current.property).1

theorem irreducibleRepresentative_character {field group : Type level} [Field field] [Group group]
    (current : irreducibleCharacters field group) :
    Representation.character (irreducibleRepresentative current).ρ = current.val :=
  (Classical.choose_spec current.property).2

theorem irreducibleRepresentatives_inequivalent {field group : Type level} [Field field] [Group group]
    (first second : irreducibleCharacters field group) (distinct : first ≠ second) :
    IsEmpty (Representation.Equiv (irreducibleRepresentative first).ρ (irreducibleRepresentative second).ρ) := by
  refine ⟨fun equivalent => distinct ?_⟩
  apply Subtype.ext
  have equal := Representation.char_iso equivalent
  rwa [irreducibleRepresentative_character, irreducibleRepresentative_character] at equal

theorem virtualCharacters_expansion {field group : Type level} [Field field] [Group group]
    (function : group → field) (membership : function ∈ virtualCharacters field group) :
    ∃ coefficients : (irreducibleCharacters field group) →₀ ℤ,
      ∀ element, function element = CFSG.OrderReductions.CharacterCoefficients.virtualCombination
        (fun current => Representation.character (irreducibleRepresentative current).ρ) coefficients element := by
  obtain ⟨coefficients, expansion⟩ := (Finsupp.mem_span_iff_linearCombination ℤ _ _).mp membership
  refine ⟨coefficients, ?_⟩
  intro element
  have pointwise := congrArg (fun function : group → field => function element) expansion
  rw [Finsupp.linearCombination_apply] at pointwise
  simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, ← Int.cast_smul_eq_zsmul field,
    smul_eq_mul, irreducibleRepresentative_character, CFSG.OrderReductions.CharacterCoefficients.virtualCombination]
    using pointwise.symm

theorem trivial_irreducible {field group : Type*} [Field field] [Group group] :
    (1 : Representation field group field).IsIrreducible := by
  have : Nontrivial (Subrepresentation (1 : Representation field group field)) :=
    nontrivial_of_ne ⊥ ⊤ (by
      intro equal
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule equal))
  apply (isSimpleOrder_iff _).mpr
  refine ⟨inferInstance, ?_⟩
  intro subrepresentation
  rcases IsSimpleOrder.eq_bot_or_eq_top subrepresentation.toSubmodule with equal | equal
  · exact Or.inl (Subrepresentation.ext equal)
  · exact Or.inr (Subrepresentation.ext equal)

theorem principal_mem_irreducibleCharacters {field group : Type level} [Field field] [Group group] :
    (fun _ : group => (1 : field)) ∈ irreducibleCharacters field group := by
  refine ⟨FDRep.of (1 : Representation field group field), trivial_irreducible, ?_⟩
  funext element
  change LinearMap.trace field field (1 : Module.End field field) = 1
  simp

theorem virtualCharacters_class {field group : Type level} [Field field] [Group group]
    (function : group → field) (membership : function ∈ virtualCharacters field group) :
    CFSG.OrderReductions.TIInductionIsometry.ClassFunction function := by
  induction membership using Submodule.span_induction with
  | mem function membership =>
      obtain ⟨representation, _, character_eq⟩ := membership
      rw [← character_eq]
      exact Representation.char_conj representation.ρ
  | zero =>
      intro element conjugator
      rfl
  | add first second _ _ first_class second_class =>
      intro element conjugator
      simp only [Pi.add_apply, first_class element conjugator, second_class element conjugator]
  | smul coefficient function _ class_function =>
      intro element conjugator
      simp only [Pi.smul_apply, class_function element conjugator]

end CFSG.OrderReductions.CharacterSpan
