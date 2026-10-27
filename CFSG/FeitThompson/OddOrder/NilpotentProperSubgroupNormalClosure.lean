module

public import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {H : Type*} [Group H] {D : Subgroup H}

theorem normal_of_isCoatom_of_isNilpotent [Group.IsNilpotent H] (hD : IsCoatom D) : D.Normal :=
  Subgroup.NormalizerCondition.normal_of_coatom D Group.normalizerCondition_of_isNilpotent hD

theorem exists_normal_lt_top_of_lt_top [Finite H] [Group.IsNilpotent H] (hD : D < ⊤) :
    ∃ N : Subgroup H, N.Normal ∧ D ≤ N ∧ N < ⊤ := by
  obtain ⟨E, hE, hDE⟩ := (IsCoatomic.eq_top_or_exists_le_coatom D).resolve_left hD.ne
  exact ⟨E, normal_of_isCoatom_of_isNilpotent hE, hDE, hE.lt_top⟩

theorem closure_conj_eq_normalClosure (D : Subgroup H) :
    Subgroup.closure {x : H | ∃ h : H, ∃ d ∈ D, x = h⁻¹ * d * h}
      = Subgroup.normalClosure (D : Set H) := by
  have hset : {x : H | ∃ h : H, ∃ d ∈ D, x = h⁻¹ * d * h} = Group.conjugatesOfSet (D : Set H) := by
    ext x
    simp only [Group.mem_conjugatesOfSet_iff, isConj_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨h, d, hd, rfl⟩
      exact ⟨d, hd, h⁻¹, by group⟩
    · rintro ⟨d, hd, c, rfl⟩
      exact ⟨c⁻¹, d, hd, by group⟩
  rw [Subgroup.normalClosure, hset]

theorem normalClosure_lt_top_of_lt_top [Finite H] [Group.IsNilpotent H] (hD : D < ⊤) :
    Subgroup.normalClosure (D : Set H) < ⊤ := by
  obtain ⟨N, _, hDN, hNtop⟩ := exists_normal_lt_top_of_lt_top hD
  exact lt_of_le_of_lt (Subgroup.normalClosure_le_normal hDN) hNtop

theorem closure_conj_lt_top_of_lt_top [Finite H] [Group.IsNilpotent H] (hD : D < ⊤) :
    Subgroup.closure {x : H | ∃ h : H, ∃ d ∈ D, x = h⁻¹ * d * h} < ⊤ := by
  rw [closure_conj_eq_normalClosure]
  exact normalClosure_lt_top_of_lt_top hD

theorem le_normalClosure_coe (D : Subgroup H) : D ≤ Subgroup.normalClosure (D : Set H) :=
  Subgroup.le_normalClosure

end

end CFSG.FeitThompson
