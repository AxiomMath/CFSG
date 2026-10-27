module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonal

public section

namespace CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def signChangeSubgroup (c : Basis ι K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∃ S : Finset ι, g = signEquiv c S}
  one_mem' := ⟨∅, (signEquiv_empty c).symm⟩
  mul_mem' := by
    rintro g h ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨symmDiff S T, signEquiv_mul c S T⟩
  inv_mem' := by
    rintro g ⟨S, rfl⟩
    exact ⟨S, inv_eq_of_mul_eq_one_left (signEquiv_mul_self c S)⟩

theorem signEquiv_mem_signChangeSubgroup (c : Basis ι K V) (S : Finset ι) :
    signEquiv c S ∈ signChangeSubgroup c :=
  ⟨S, rfl⟩

theorem signChangeSubgroup_mul_self {c : Basis ι K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ signChangeSubgroup c) : g * g = 1 := by
  obtain ⟨S, rfl⟩ := hg
  exact signEquiv_mul_self c S

theorem isPGroup_signChangeSubgroup (c : Basis ι K V) :
    IsPGroup 2 ↥(signChangeSubgroup c) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro e
  refine ⟨1, ?_⟩
  show e ^ (2 ^ 1) = 1
  rw [pow_one, pow_two]
  exact Subtype.ext (signChangeSubgroup_mul_self e.2)

end CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare

end
