module

public import CFSG.LieType.Steinberg.CentralExt.SLMilnor

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Matrix

theorem toGL_surjective_zmod_two {n : Type*} [Fintype n] [DecidableEq n] :
    Function.Surjective (SpecialLinearGroup.toGL (n := n) (R := ZMod 2)) := by
  intro g
  have hdet : (g : Matrix n n (ZMod 2)).det = 1 := by
    have h := Matrix.isUnits_det_units g
    generalize (g : Matrix n n (ZMod 2)).det = x at h
    fin_cases x
    · exact absurd h not_isUnit_zero
    · rfl
  exact ⟨⟨g, hdet⟩, Matrix.GeneralLinearGroup.ext fun _ _ => rfl⟩

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

@[expose] noncomputable def linearEquivMulEquivSL {n : ℕ} (hn : finrank (ZMod 2) E = n) :
    (E ≃ₗ[ZMod 2] E) ≃* SpecialLinearGroup (Fin n) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).symm.trans <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (Module.finBasisOfFinrankEq (ZMod 2) E hn).equivFun).trans <|
    Matrix.GeneralLinearGroup.toLin.symm.trans <|
    (MulEquiv.ofBijective (SpecialLinearGroup.toGL (n := Fin n) (R := ZMod 2))
      ⟨SpecialLinearGroup.toGL_injective, toGL_surjective_zmod_two⟩).symm

theorem isPerfect_linearEquiv (hE : 3 ≤ finrank (ZMod 2) E) :
    Group.IsPerfect (E ≃ₗ[ZMod 2] E) :=
  have := CFSG.LinearGroups.special_linear_isPerfect (K := ZMod 2) (by omega) (Or.inl hE)
  Group.IsPerfect.ofSurjective (f := (linearEquivMulEquivSL rfl).symm.toMonoidHom)
    (linearEquivMulEquivSL rfl).symm.surjective

theorem exists_section_of_ker_le_center (hE : 5 ≤ finrank (ZMod 2) E) {C : Type*} [Group C]
    {η : C →* (E ≃ₗ[ZMod 2] E)} (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center C) : ∃ s : (E ≃ₗ[ZMod 2] E) →* C, ∀ g, η (s g) = g := by
  obtain ⟨m, hm⟩ : ∃ m, finrank (ZMod 2) E = m + 1 := ⟨finrank (ZMod 2) E - 1, by omega⟩
  let e := linearEquivMulEquivSL hm
  have hker : (e.toMonoidHom.comp η).ker ≤ Subgroup.center C := fun x hx => hcen <| by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.injective (hx.trans (map_one e).symm)
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le
    (by omega) (e.surjective.comp hη) hker
  exact ⟨s.comp e.toMonoidHom, fun g => e.injective (hs (e g))⟩

end CFSG.GroupTheory.GLnTwoSplitting
