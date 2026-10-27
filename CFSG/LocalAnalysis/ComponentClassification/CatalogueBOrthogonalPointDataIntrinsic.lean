module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalPointAction

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {G : Type w} [Group G]

theorem pointAction_injective_of_properties (Q : QuadraticForm K V)
    (rho : G →* Equiv.Perm (Points Q)) (ha : ActionProperties Q rho) :
    Function.Injective rho := by
  let := MulAction.compHom (Points Q) rho
  let := ha.2.2.2.1
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Points Q)
  intro L
  change rho g L = rho h L
  exact congrArg (fun p : Equiv.Perm (Points Q) => p L) hgh

theorem pointStabilizer_injective_of_properties (Q : QuadraticForm K V)
    (rho : G →* Equiv.Perm (Points Q)) (ha : ActionProperties Q rho) :
    Function.Injective (actionStabilizer Q rho) := ha.2.2.2.2.2.1

theorem pointFamily_eq_conjugacy_of_properties (Q : QuadraticForm K V)
    (rho : G →* Equiv.Perm (Points Q)) (ha : ActionProperties Q rho) (L : Points Q) :
    actionStabilizerFamily Q rho =
      Set.range (fun g : G => (actionStabilizer Q rho L).map (MulAut.conj g).toMonoidHom) := by
  let := MulAction.compHom (Points Q) rho
  let := ha.2.2.2.2.1
  ext U
  constructor
  · rintro ⟨M, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G L M
    refine ⟨g, ?_⟩
    change (CatalogueBStabilizerFamily.pointStabilizer rho L).map
      (MulAut.conj g).toMonoidHom = CatalogueBStabilizerFamily.pointStabilizer rho M
    rw [CatalogueBStabilizerFamily.pointStabilizer_conj]
    exact congrArg (CatalogueBStabilizerFamily.pointStabilizer rho) hg
  · rintro ⟨g, rfl⟩
    refine ⟨rho g L, ?_⟩
    exact (CatalogueBStabilizerFamily.pointStabilizer_conj rho g L).symm

theorem pointStabilizer_isCoatom_of_properties (Q : QuadraticForm K V)
    (rho : G →* Equiv.Perm (Points Q)) (ha : ActionProperties Q rho) (L : Points Q) :
    IsCoatom (actionStabilizer Q rho L) := by
  let := MulAction.compHom (Points Q) rho
  let := ha.2.1
  let := ha.2.2.2.2.1
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G L

theorem pointStabilizer_index_of_properties (Q : QuadraticForm K V)
    (rho : G →* Equiv.Perm (Points Q)) (ha : ActionProperties Q rho) (L : Points Q) :
    (actionStabilizer Q rho L).index = Nat.card (Points Q) := by
  let := MulAction.compHom (Points Q) rho
  let := ha.2.2.2.2.1
  exact MulAction.index_stabilizer_of_transitive G L

theorem quadratic_ne_zero_of_regular_three [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Q ≠ 0 := by
  obtain ⟨T, hdim, _⟩ := hT
  have hpos : 0 < Module.finrank K V := by
    have hle := T.finrank_le
    rw [hdim] at hle
    omega
  let := Module.nontrivial_of_finrank_pos hpos
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply hQ.1 x
  intro y
  simp [hzero, QuadraticMap.polarBilin, QuadraticMap.polar]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
