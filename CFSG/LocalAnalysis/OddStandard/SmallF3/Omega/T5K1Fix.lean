module

public import CFSG.CharacterTheory.Wreathed.ExchangedEigensubgroupFiveSupport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem t5_perfect_fix_of_finrank_two {A V : Type} [Group A] [AddCommGroup V]
    [Module (ZMod 3) V] (ρ : A →* (V ≃ₗ[ZMod 3] V)) (W : Submodule (ZMod 3) V)
    (hW : Module.finrank (ZMod 3) W = 2) (hinv : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W)
    {P : Subgroup A} (hP : Group.IsPerfect ↥P) : ∀ p ∈ P, ∀ w ∈ W, ρ p w = w := by
  haveI := hP
  have hstab : ∀ a : A, W.map (ρ a : V →ₗ[ZMod 3] V) = W := by
    intro a
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      exact hinv a
    · intro w hw
      refine ⟨(ρ a⁻¹) w, hinv a⁻¹ w hw, ?_⟩
      rw [map_inv]
      simp
  let rW : A →* (W ≃ₗ[ZMod 3] W) :=
    { toFun := fun a => (ρ a).ofSubmodules W W (hstab a)
      map_one' := by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        simp
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        simp [map_mul, LinearEquiv.mul_apply] }
  haveI : Module.Finite (ZMod 3) W :=
    Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  let b : Module.Basis (Fin 2) (ZMod 3) W := Module.finBasisOfFinrankEq (ZMod 3) W hW
  let Φ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) ≃* (W ≃ₗ[ZMod 3] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W)
  let τ : ↥P →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
    (Φ.symm.toMonoidHom).comp (rW.comp P.subtype)
  intro p hp w hw
  have hτ : τ ⟨p, hp⟩ = 1 :=
    CFSG.Wreathed.ExchangedEigensubgroupFive.eq_one_of_GL_two_three τ ⟨p, hp⟩
  have h1 : rW p = 1 := by
    have h := congrArg Φ hτ
    simpa [τ] using h
  calc ρ p w = ((ρ p).ofSubmodules W W (hstab p) ⟨w, hw⟩ : V) := rfl
    _ = ((rW p) ⟨w, hw⟩ : V) := rfl
    _ = ((1 : W ≃ₗ[ZMod 3] W) ⟨w, hw⟩ : V) := by rw [h1]
    _ = w := rfl

end CFSG.OddStandard.SmallF3.Omega
