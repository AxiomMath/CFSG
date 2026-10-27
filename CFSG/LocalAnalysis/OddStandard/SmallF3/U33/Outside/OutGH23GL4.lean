module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

private noncomputable def linMulAutAux (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ₗ[ZMod 2] V) →* MulAut (Multiplicative V) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem linMulAutAux_injective (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (linMulAutAux V) := by
  intro f g h
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun φ : MulAut (Multiplicative V) => Multiplicative.toAdd
    (φ (Multiplicative.ofAdd v))) h
  exact this

private theorem linMulAutAux_surjective (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Surjective (linMulAutAux V) := by
  intro φ
  let F : V →+ V :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun a b => by simp }
  let G : V →+ V :=
    { toFun := fun v => Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hFG : (F.toZModLinearMap 2).comp (G.toZModLinearMap 2) = LinearMap.id := by
    ext v
    simp [F, G]
  have hGF : (G.toZModLinearMap 2).comp (F.toZModLinearMap 2) = LinearMap.id := by
    ext v
    simp [F, G]
  refine ⟨LinearEquiv.ofLinearMap (F.toZModLinearMap 2) (G.toZModLinearMap 2) hFG hGF, ?_⟩
  ext x
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  rfl

theorem gh23_mulAut_equiv_GL4 :
    Nonempty (MulAut (E2 4) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) := by
  exact ⟨((Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := ZMod 2)).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2)).trans
      (MulEquiv.ofBijective (linMulAutAux (Fin 4 → ZMod 2))
        ⟨linMulAutAux_injective (Fin 4 → ZMod 2),
          linMulAutAux_surjective (Fin 4 → ZMod 2)⟩))).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
