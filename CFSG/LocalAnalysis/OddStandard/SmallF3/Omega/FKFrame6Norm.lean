module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenRefl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fk_fr_eq_one_of_isSquare_units {a : (ZMod 3)ˣ} (ha : IsSquare a) : a = 1 := by
  obtain ⟨b, rfl⟩ := ha
  rcases aux_units_zmod3 b with h | h <;> rw [h] <;> decide

theorem fk_fr_norm_eq (hQ : Q.Nondegenerate) {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (h : reflOf Q u hu * reflOf Q v hv ∈ omegaGroup hQ) : Q u = Q v := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  letI : Invertible (Q v) := invertibleOfNonzero hv
  rw [mem_omegaGroup_iff hQ, reflOf_eq u hu, reflOf_eq v hv, map_mul,
    CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal hQ u,
    CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal hQ v] at h
  have h2 : TauCeti.squareClassHom (unitOfInvertible (Q u)) *
      TauCeti.squareClassHom (unitOfInvertible (Q v)) = 1 := by
    simpa using congrArg Prod.snd h
  have h3 : TauCeti.squareClassHom
      (unitOfInvertible (Q u) * unitOfInvertible (Q v)) = 1 := by
    rw [map_mul]
    exact h2
  have hsq : IsSquare (unitOfInvertible (Q u) * unitOfInvertible (Q v)) := by
    rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square] at h3
    exact h3
  have hp : unitOfInvertible (Q u) * unitOfInvertible (Q v) = 1 :=
    fk_fr_eq_one_of_isSquare_units hsq
  have hbb : unitOfInvertible (Q v) * unitOfInvertible (Q v) = 1 := by
    rcases aux_units_zmod3 (unitOfInvertible (Q v)) with h' | h' <;> rw [h'] <;> decide
  have hab : unitOfInvertible (Q u) = unitOfInvertible (Q v) := by
    calc unitOfInvertible (Q u)
        = unitOfInvertible (Q u) *
            (unitOfInvertible (Q v) * unitOfInvertible (Q v)) := by rw [hbb, mul_one]
      _ = (unitOfInvertible (Q u) * unitOfInvertible (Q v)) *
            unitOfInvertible (Q v) := by rw [← mul_assoc]
      _ = 1 * unitOfInvertible (Q v) := by rw [hp]
      _ = unitOfInvertible (Q v) := by rw [one_mul]
  calc Q u = (unitOfInvertible (Q u) : ZMod 3) := rfl
    _ = (unitOfInvertible (Q v) : ZMod 3) := by rw [hab]
    _ = Q v := rfl

end CFSG.OddStandard.SmallF3.Omega
