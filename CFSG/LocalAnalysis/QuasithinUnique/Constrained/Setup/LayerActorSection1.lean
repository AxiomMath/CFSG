module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import CFSG.Quasithin.Background.Module
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open scoped Multiplicative

section Linear

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def linToMulAut : (M ≃ₗ[ZMod 2] M) →* MulAut (Multiplicative M) :=
  (binPsi (MulEquiv.refl (Multiplicative M))).symm.toMonoidHom

theorem linToMulAut_apply (f : M ≃ₗ[ZMod 2] M) (m : Multiplicative M) :
    linToMulAut f m = Multiplicative.ofAdd (f (Multiplicative.toAdd m)) := rfl

theorem linToMulAut_injective : Function.Injective (linToMulAut (M := M)) :=
  (binPsi (MulEquiv.refl (Multiplicative M))).symm.injective

theorem linToMulAut_eq_one_iff (f : M ≃ₗ[ZMod 2] M) :
    linToMulAut f = 1 ↔ ∀ m : M, f m = m := by
  constructor
  · intro h m
    have := congrArg (fun g : MulAut (Multiplicative M) => Multiplicative.toAdd (g
        (Multiplicative.ofAdd m))) h
    simpa [linToMulAut_apply] using this
  · intro h
    apply MulEquiv.ext
    intro m
    show Multiplicative.ofAdd (f (Multiplicative.toAdd m)) = m
    rw [h]
    rfl

theorem map_linToMulAut (X : Subgroup (M ≃ₗ[ZMod 2] M)) :
    (X.map (linToMulAut (M := M))).map
        (binPsi (MulEquiv.refl (Multiplicative M))).toMonoidHom = X :=
  CFSG.LocalCores.map_map_symm (binPsi (MulEquiv.refl (Multiplicative M))).symm X

end Linear

section Quadratic

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem binPsi_toAdd (x : MulAut V) (v : V) :
    binPsi θ x (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ (x v)) := by
  rw [binPsi_apply]
  simp

theorem binPsi_sub (x : MulAut V) (v : V) :
    binPsi θ x (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v) =
      Multiplicative.toAdd (θ (x v * v⁻¹)) := by
  rw [binPsi_toAdd]
  simp [map_mul, map_inv, sub_eq_add_neg]

theorem isQuadratic_iff_map (X : Subgroup (MulAut V)) :
    IsQuadratic X ↔
      QuadAct (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (X.map (binPsi θ).toMonoidHom) := by
  unfold IsQuadratic commV
  rw [Subgroup.closure_le]
  constructor
  · intro h b hb c hc w
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.toAdd (θ v) = w :=
      ⟨θ.symm (Multiplicative.ofAdd w), by simp⟩
    have h1 : y (x v * v⁻¹) = x v * v⁻¹ := h ⟨x, hx, v, rfl⟩ y hy
    change binPsi θ y (binPsi θ x (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v)) =
      binPsi θ x (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v)
    rw [binPsi_sub, binPsi_toAdd, h1]
  · intro h w hw
    obtain ⟨x, hx, v, rfl⟩ := hw
    intro y hy
    have h1 := h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (Multiplicative.toAdd (θ v))
    change binPsi θ y (binPsi θ x (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v)) =
      binPsi θ x (Multiplicative.toAdd (θ v)) - Multiplicative.toAdd (θ v) at h1
    rw [binPsi_sub, binPsi_toAdd] at h1
    exact θ.injective (Multiplicative.toAdd.injective h1)

end Quadratic

end CFSG.QuasithinUnique.Setup.Layer.Actor
