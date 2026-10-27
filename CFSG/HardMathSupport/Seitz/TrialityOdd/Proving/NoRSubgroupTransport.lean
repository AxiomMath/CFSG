module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

theorem no_prime_subgroup_normalized_congr_iff
    {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (r : ℕ) (E : Subgroup (MulAut K)) :
    (∃ R : Subgroup K, R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ α ∈ E, R.map α.toMonoidHom = R) ↔
    (∃ S : Subgroup L, S ≠ ⊥ ∧ IsPGroup r S ∧
      ∀ β ∈ E.map (MulAut.congr e).toMonoidHom,
        S.map β.toMonoidHom = S) := by
  constructor
  · rintro ⟨R, hR0, hRp, hRE⟩
    refine ⟨R.map e.toMonoidHom, ?_, hRp.map e.toMonoidHom, ?_⟩
    · intro hbot
      apply hR0
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hx' : e.toMonoidHom x ∈ R.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
      rw [hbot] at hx'
      simpa using hx'
    · rintro β hβ
      obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hβ
      have hcomp : ((MulAut.congr e).toMonoidHom α).toMonoidHom.comp e.toMonoidHom
          = e.toMonoidHom.comp α.toMonoidHom := by
        ext x
        simp [MulAut.congr_apply]
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hRE α hα]
  · rintro ⟨S, hS0, hSp, hSE⟩
    refine ⟨S.map e.symm.toMonoidHom, ?_, hSp.map e.symm.toMonoidHom, ?_⟩
    · intro hbot
      apply hS0
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hy' : e.symm.toMonoidHom y ∈ S.map e.symm.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rw [hbot] at hy'
      simpa using hy'
    · intro α hα
      have hβ : (MulAut.congr e).toMonoidHom α ∈ E.map (MulAut.congr e).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hα
      have hSβ := hSE _ hβ
      have hcomp : α.toMonoidHom.comp e.symm.toMonoidHom
          = e.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom α).toMonoidHom := by
        ext y
        simp [MulAut.congr_apply]
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hSβ]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

end
