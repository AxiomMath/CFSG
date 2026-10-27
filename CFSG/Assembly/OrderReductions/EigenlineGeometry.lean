module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.EigenlineGeometry

theorem nonscalar_eigenspace_finrank_one {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (dimension : Module.finrank field vector = 2) (operator : Module.End field vector)
    (nonscalar : ¬ ∃ scalar : field, operator = scalar • (1 : Module.End field vector))
    (eigenvalue : operator.Eigenvalues) :
    Module.finrank field (operator.eigenspace eigenvalue.val) = 1 := by
  have proper : operator.eigenspace eigenvalue.val ≠ ⊤ := by
    intro equal
    apply nonscalar
    refine ⟨eigenvalue.val, ?_⟩
    ext element
    exact Module.End.mem_eigenspace_iff.mp (equal ▸ (Submodule.mem_top : element ∈ (⊤ : Submodule field vector)))
  have nonzero : operator.eigenspace eigenvalue.val ≠ ⊥ :=
    Module.End.hasEigenvalue_iff.mp eigenvalue.property
  have nontrivial : Nontrivial (operator.eigenspace eigenvalue.val) :=
    Submodule.nontrivial_iff_ne_bot.mpr nonzero
  have positive := Module.finrank_pos (R := field) (M := operator.eigenspace eigenvalue.val)
  have smaller := Submodule.finrank_lt proper
  omega

theorem invariant_line_is_eigenspace {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (dimension : Module.finrank field vector = 2) (operator : Module.End field vector)
    (nonscalar : ¬ ∃ scalar : field, operator = scalar • (1 : Module.End field vector))
    (line : Submodule field vector) (line_dimension : Module.finrank field line = 1)
    (invariant : ∀ element ∈ line, operator element ∈ line) :
    ∃ eigenvalue : operator.Eigenvalues, line = operator.eigenspace eigenvalue.val := by
  let restricted : Module.End field line := operator.restrict invariant
  obtain ⟨scalar, scalar_eq, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one line_dimension restricted
  have line_le : line ≤ operator.eigenspace scalar := by
    intro element membership
    apply Module.End.mem_eigenspace_iff.mpr
    have equal := congrArg (fun linear : Module.End field line => (linear ⟨element, membership⟩).val) scalar_eq
    exact equal
  have line_nonzero : line ≠ ⊥ := by
    intro equal
    rw [equal, finrank_bot] at line_dimension
    omega
  have eigenvalue : operator.HasEigenvalue scalar := Module.End.hasEigenvalue_iff.mpr (by
    intro equal
    exact line_nonzero (le_bot_iff.mp (equal ▸ line_le)))
  refine ⟨⟨scalar, eigenvalue⟩, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq line_le
  have eigenspace_dimension := nonscalar_eigenspace_finrank_one dimension operator nonscalar ⟨scalar, eigenvalue⟩
  rw [Module.End.Eigenvalues.val_mk] at eigenspace_dimension
  exact line_dimension.trans eigenspace_dimension.symm

theorem eigenvalue_card_le_finrank {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field vector) : Nat.card operator.Eigenvalues ≤ Module.finrank field vector := by
  classical
  have : Finite operator.Eigenvalues := operator.finite_hasEigenvalue.to_subtype
  let := Fintype.ofFinite operator.Eigenvalues
  choose vectors vector_eigen using fun eigenvalue : operator.Eigenvalues =>
    Module.End.HasEigenvalue.exists_hasEigenvector (show operator.HasEigenvalue eigenvalue.val from eigenvalue.property)
  have independent := operator.eigenvectors_linearIndependent' (fun eigenvalue : operator.Eigenvalues => eigenvalue.val)
    Subtype.val_injective vectors vector_eigen
  simpa only [Nat.card_eq_fintype_card] using independent.fintype_card_le_finrank

@[expose] def eigenlineSet {field vector : Type*} [Field field] [AddCommGroup vector] [Module field vector]
    (operator : Module.End field vector) : Set (Submodule field vector) :=
  Set.range (fun eigenvalue : operator.Eigenvalues => operator.eigenspace eigenvalue.val)

theorem eigenlineSet_finite {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field vector) : (eigenlineSet operator).Finite := by
  have : Finite operator.Eigenvalues := operator.finite_hasEigenvalue.to_subtype
  exact Set.finite_range _

theorem eigenlineSet_card_le_finrank {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field vector) :
    Nat.card (eigenlineSet operator) ≤ Module.finrank field vector := by
  have : Finite operator.Eigenvalues := operator.finite_hasEigenvalue.to_subtype
  exact (Finite.card_range_le (fun eigenvalue : operator.Eigenvalues => operator.eigenspace eigenvalue.val)).trans
    (eigenvalue_card_le_finrank operator)

@[expose, instance_reducible] def submoduleAction {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) : MulAction actors (Submodule field vector) where
  smul actor line := line.map (representation actor)
  one_smul line := by
    change line.map (representation 1) = line
    rw [map_one]
    exact Submodule.map_id line
  mul_smul first second line := by
    change line.map (representation (first * second)) = (line.map (representation second)).map (representation first)
    rw [map_mul]
    exact Submodule.map_comp (representation second) (representation first) line

theorem mapped_finrank_eq {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector] [Group actors]
    (representation : Representation field actors vector) (actor : actors) (line : Submodule field vector) :
    Module.finrank field (line.map (representation actor)) = Module.finrank field line := by
  let := submoduleAction representation
  have forward := line.finrank_map_le (representation actor)
  have reverse := (line.map (representation actor)).finrank_map_le (representation actor⁻¹)
  change Module.finrank field ↥(actor⁻¹ • (actor • line)) ≤ _ at reverse
  rw [inv_smul_smul] at reverse
  exact le_antisymm forward reverse

theorem odd_action_small_orbit_fixed {actors points : Type*} [Group actors] [Finite actors]
    [MulAction actors points] (odd_order : Odd (Nat.card actors)) (point : points)
    (small : Nat.card (MulAction.orbit actors point) ≤ 2) :
    ∀ actor : actors, actor • point = point := by
  classical
  have orbit_divides : Nat.card (MulAction.orbit actors point) ∣ Nat.card actors := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer actors point)]
    exact Subgroup.card_quotient_dvd_card _
  have orbit_odd := odd_order.of_dvd_nat orbit_divides
  have : Finite (MulAction.orbit actors point) := Finite.of_equiv
    (actors ⧸ MulAction.stabilizer actors point) (MulAction.orbitEquivQuotientStabilizer actors point).symm
  let := Fintype.ofFinite (MulAction.orbit actors point)
  have card_one : Fintype.card (MulAction.orbit actors point) = 1 := by
    rw [Nat.card_eq_fintype_card] at small orbit_odd
    have parity := Nat.odd_iff.mp orbit_odd
    omega
  exact MulAction.mem_fixedPoints.mp (MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr card_one)

end CFSG.OrderReductions.EigenlineGeometry
