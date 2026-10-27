module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def IsProjective (x : ProjOrth Q) : Prop :=
  x ≠ 1 ∧ x * x = 1 ∧ ∃ p : OGroup Q, p * p = piOrth Q ∧ toProj Q p = x

theorem exists_lift_of_mul_self_eq_one (hQ : Q.Nondegenerate)
    (h : ¬ (Even (Module.finrank (ZMod 3) V) ∧
      quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2)))
    {x : ProjOrth Q} (hx : x * x = 1) : ∃ t : OGroup Q, t * t = 1 ∧ toProj Q t = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) x
  have hg1 : (g * g) ∈ piGroup Q := by
    apply (QuotientGroup.eq_one_iff (g * g)).mp
    change toProj Q (g * g) = 1
    rw [map_mul]
    exact hx
  rcases (mem_piGroup_iff.mp hg1) with hgg | hgg
  · exact ⟨g, hgg, rfl⟩
  · exact absurd ((exists_mul_self_eq_piOrth_iff hQ).mp ⟨g, hgg⟩) h

end CFSG.OddStandard.SmallF3.Omega
