module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

section Local

variable {F : Type} [Group F] [Finite F]

theorem mem_normalizer_of_trivial {r : F} (hr2 : r * r = 1) {I : Subgroup F}
    (htriv : ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) : r ∈ Subgroup.normalizer (I : Set F) := by
  have key : ∀ j ∈ I, r * j * r⁻¹ ∈ I := fun j hj => by
    have h1 : r * j * r⁻¹ = ⁅r, j⁆ * j := by rw [commutatorElement_def]; group
    rw [h1]
    exact I.mul_mem (oddCoreOf_le_self I (htriv j hj)) hj
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨key j, fun hj => ?_⟩
  have h2 := key _ hj
  have e : r * (r * j * r⁻¹) * r⁻¹ = j := by
    rw [hri]
    calc r * (r * j * r) * r = (r * r) * j * (r * r) := by group
      _ = j := by rw [hr2]; group
  rwa [e] at h2

end Local

section Statements

variable {F : Type} [Group F] [Finite F]

@[expose] def NoTrivialSwapOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {Q : Subgroup F} {r u : F}, Mem3 Q r → r ∈ S → u ∈ S → u * u = 1 → u * r = r * u →
    Q ≠ conjSub u Q → ∀ {I : Subgroup F}, Mem3 I u → ¬ ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I

end Statements

end CFSG.ClassicalInvolution.Q3.Q3T6X
