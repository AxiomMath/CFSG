module

public import CFSG.Assembly.OrderReductions.TwoDimensionalScalars
public import CFSG.Assembly.OrderReductions.EigenlineGeometry

public section

namespace CFSG.OrderReductions.TwoDimensionalOdd

open CFSG.OrderReductions.TwoDimensionalScalars CFSG.OrderReductions.EigenlineGeometry

theorem commuting_preserves_eigenspace {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] (first second : Module.End field vector)
    (commutes : Commute first second) (scalar : field) :
    ∀ element ∈ first.eigenspace scalar, second element ∈ first.eigenspace scalar := by
  intro element membership
  apply Module.End.mem_eigenspace_iff.mpr
  have equal := congrArg (fun linear : Module.End field vector => linear element) commutes.eq
  change first (second element) = second (first element) at equal
  rw [Module.End.mem_eigenspace_iff.mp membership, map_smul] at equal
  exact equal

theorem normal_preserves_mapped_common_line {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (normal : Subgroup actors) [normal.Normal]
    (line : Submodule field vector)
    (common : ∀ member : normal, ∀ element ∈ line, representation member.val element ∈ line)
    (actor : actors) (member : normal) :
    ∀ element ∈ line.map (representation actor), representation member.val element ∈ line.map (representation actor) := by
  intro element membership
  obtain ⟨original, original_mem, rfl⟩ := Submodule.mem_map.mp membership
  let conjugated : normal := ⟨actor⁻¹ * member.val * actor,
    (inferInstance : normal.Normal).conj_mem' member.val member.property actor⟩
  have equal : representation member.val * representation actor = representation actor * representation conjugated.val := by
    rw [← map_mul, ← map_mul]
    congr 1
    dsimp [conjugated]
    group
  have applied := congrArg (fun linear : Module.End field vector => linear original) equal
  change representation member.val (representation actor original) =
    representation actor (representation conjugated.val original) at applied
  rw [applied]
  exact Submodule.mem_map.mpr ⟨representation conjugated.val original, common conjugated original original_mem, rfl⟩

theorem eigenline_invariant_of_normal_commuting {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] (representation : Representation field actors vector)
    (dimension : Module.finrank field vector = 2) (odd_order : Odd (Nat.card actors))
    (normal : Subgroup actors) [normal.Normal]
    (commuting : ∀ first second : normal, Commute (representation first.val) (representation second.val))
    (member : normal) (nonscalar : ¬ scalarImage representation member.val)
    (eigenvalue : Module.End.Eigenvalues (representation member.val)) :
    ∀ actor : actors, (Module.End.eigenspace (representation member.val) eigenvalue.val).map (representation actor) =
      Module.End.eigenspace (representation member.val) eigenvalue.val := by
  let operator : Module.End field vector := representation member.val
  let line := operator.eigenspace eigenvalue.val
  let := submoduleAction representation
  have line_dimension := nonscalar_eigenspace_finrank_one dimension operator nonscalar eigenvalue
  have common : ∀ other : normal, ∀ element ∈ line, representation other.val element ∈ line := by
    intro other
    exact commuting_preserves_eigenspace operator (representation other.val) (commuting member other) eigenvalue.val
  have orbit_le : MulAction.orbit actors line ⊆ eigenlineSet operator := by
    intro image membership
    obtain ⟨actor, rfl⟩ := membership
    have image_dimension : Module.finrank field ↥(actor • line) = 1 :=
      (mapped_finrank_eq representation actor line).trans line_dimension
    obtain ⟨image_eigenvalue, equal⟩ := invariant_line_is_eigenspace dimension operator nonscalar (actor • line)
      image_dimension (normal_preserves_mapped_common_line representation normal line common actor member)
    exact ⟨image_eigenvalue, equal.symm⟩
  have orbit_card_le : Nat.card (MulAction.orbit actors line) ≤ 2 := by
    have finite_lines : Finite (eigenlineSet operator) := (eigenlineSet_finite operator).to_subtype
    have cardinal := Nat.card_le_card_of_injective
      (fun image : MulAction.orbit actors line => (⟨image.val, orbit_le image.property⟩ : eigenlineSet operator))
      (fun _ _ equal => Subtype.ext
        (congrArg (fun image : eigenlineSet operator => image.val) equal))
    exact cardinal.trans ((eigenlineSet_card_le_finrank operator).trans dimension.le)
  exact odd_action_small_orbit_fixed odd_order line orbit_card_le

theorem not_irreducible_of_dimension_two_solvable_odd {field vector actors : Type*} [Field field]
    [IsAlgClosed field] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (representation : Representation field actors vector)
    (dimension : Module.finrank field vector = 2) (odd_order : Odd (Nat.card actors)) :
    ¬ representation.IsIrreducible := by
  intro irreducible
  have : representation.IsIrreducible := irreducible
  have vector_nontrivial : Nontrivial vector := Module.nontrivial_of_finrank_pos (R := field) (M := vector) (by omega)
  have exists_line : ∃ line : Submodule field vector, Module.finrank field line = 1 ∧
      ∀ actor : actors, ∀ element ∈ line, representation actor element ∈ line := by
    by_cases nonscalar : ∃ actor : actors, ¬ scalarImage representation actor
    · obtain ⟨normal, normal_instance, commuting, member, not_scalar⟩ :=
        exists_normal_commutative_image_nonscalar representation dimension odd_order nonscalar
      have : normal.Normal := normal_instance
      obtain ⟨scalar, scalar_eigen⟩ := Module.End.exists_eigenvalue (representation member.val)
      let eigenvalue : Module.End.Eigenvalues (representation member.val) := ⟨scalar, scalar_eigen⟩
      let line := Module.End.eigenspace (representation member.val) scalar
      have line_dimension := nonscalar_eigenspace_finrank_one dimension (representation member.val) not_scalar eigenvalue
      rw [Module.End.Eigenvalues.val_mk] at line_dimension
      refine ⟨line, line_dimension, ?_⟩
      intro actor element membership
      have equal := eigenline_invariant_of_normal_commuting representation dimension odd_order normal commuting member
        not_scalar eigenvalue actor
      rw [Module.End.Eigenvalues.val_mk] at equal
      change representation actor element ∈ Module.End.eigenspace (representation member.val) scalar
      exact equal ▸ Submodule.mem_map.mpr ⟨element, membership, rfl⟩
    · push Not at nonscalar
      obtain ⟨element, element_ne⟩ := exists_ne (0 : vector)
      refine ⟨Submodule.span field {element}, finrank_span_singleton element_ne, ?_⟩
      intro actor member membership
      obtain ⟨scalar, equal⟩ := nonscalar actor
      rw [equal]
      exact (Submodule.span field {element}).smul_mem scalar membership
  obtain ⟨line, line_dimension, invariant⟩ := exists_line
  let subrepresentation : Subrepresentation representation :=
    { toSubmodule := line
      apply_mem_toSubmodule := invariant }
  rcases IsSimpleOrder.eq_bot_or_eq_top subrepresentation with equal | equal
  · have line_bot : line = ⊥ := congrArg Subrepresentation.toSubmodule equal
    rw [line_bot, finrank_bot] at line_dimension
    omega
  · have line_top : line = ⊤ := congrArg Subrepresentation.toSubmodule equal
    rw [line_top, finrank_top, dimension] at line_dimension
    omega

end CFSG.OrderReductions.TwoDimensionalOdd
