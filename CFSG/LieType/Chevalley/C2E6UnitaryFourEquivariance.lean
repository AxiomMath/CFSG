module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem Pf_param_aux : ∀ a b c d e f : ZMod 2,
    Pf (param ![a, b, c, d, e, f]) = algebraMap (ZMod 2) K (Q ![a, b, c, d, e, f]) := by
  decide

theorem Pf_param (x : X) : Pf (param x) = algebraMap (ZMod 2) K (Q x) := by
  rw [eta_X x]
  exact Pf_param_aux _ _ _ _ _ _

theorem Pf_eq_Q {w : W} (hw : w ∈ W₀) : Pf w = algebraMap (ZMod 2) K (Q (psiLin w)) := by
  conv_lhs => rw [← param_psiLin hw]
  exact Pf_param _

theorem algebraMap_injective : Function.Injective (algebraMap (ZMod 2) K) :=
  (algebraMap (ZMod 2) K).injective

@[expose] def paramLin : X →ₗ[ZMod 2] W := W₀.subtype ∘ₗ (Ψ.symm : X →ₗ[ZMod 2] W₀)

theorem paramLin_apply (x : X) : paramLin x = param x := rfl

theorem map_fixed_of_commute (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) {S S' : Submodule K W} (hS : (S' : Set W) = φ '' S) :
    (S'.restrictScalars (ZMod 2) ⊓ W₀).map psiLin =
      ((S.restrictScalars (ZMod 2) ⊓ W₀).map psiLin).map (psiLin ∘ₗ φ ∘ₗ paramLin) := by
  rw [← Submodule.map_comp]
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_W₀,
    LinearMap.coe_comp, Function.comp_apply, paramLin_apply]
  constructor
  · rintro ⟨w, ⟨hw, hTw⟩, rfl⟩
    have hw' : w ∈ (S' : Set W) := hw
    rw [hS] at hw'
    obtain ⟨y, hy, rfl⟩ := hw'
    have hTy : T y = y := hinj (by rw [← hT, hTw])
    exact ⟨y, ⟨hy, hTy⟩, by rw [param_psiLin hTy]⟩
  · rintro ⟨y, ⟨hy, hTy⟩, rfl⟩
    refine ⟨φ y, ⟨?_, by rw [hT, hTy]⟩, by rw [param_psiLin hTy]⟩
    have : φ y ∈ (S' : Set W) := by
      rw [hS]
      exact ⟨y, hy, rfl⟩
    exact this

@[expose] def isoOfCommute (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) (hPf : ∀ w ∈ W₀, Pf (φ w) = Pf w) :
    QuadraticMap.IsometryEquiv Q Q :=
  have hmem : ∀ w ∈ W₀, φ w ∈ W₀ := fun w hw => by
    rw [mem_W₀] at hw ⊢
    rw [hT, hw]
  ⟨LinearEquiv.ofInjectiveEndo (psiLin ∘ₗ φ ∘ₗ paramLin) (by
    intro x y hxy
    simp only [LinearMap.coe_comp, Function.comp_apply, paramLin_apply] at hxy
    have h := congrArg param hxy
    rw [param_psiLin (hmem _ (param_mem_W₀ x)), param_psiLin (hmem _ (param_mem_W₀ y))] at h
    rw [← psiLin_param x, ← psiLin_param y, hinj h]), fun x => by
    change Q (psiLin (φ (param x))) = Q x
    apply algebraMap_injective
    rw [← Pf_eq_Q (hmem _ (param_mem_W₀ x)), hPf _ (param_mem_W₀ x), Pf_param]⟩

theorem isoOfCommute_apply (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) (hPf : ∀ w ∈ W₀, Pf (φ w) = Pf w) (x : X) :
    isoOfCommute φ hinj hT hPf x = psiLin (φ (param x)) := rfl

theorem isoOfCommute_psiLin (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) (hPf : ∀ w ∈ W₀, Pf (φ w) = Pf w) {w : W} (hw : w ∈ W₀) :
    isoOfCommute φ hinj hT hPf (psiLin w) = psiLin (φ w) := by
  rw [isoOfCommute_apply, param_psiLin hw]

theorem map_fixed_iso (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) (hPf : ∀ w ∈ W₀, Pf (φ w) = Pf w) {S S' : Submodule K W}
    (hS : (S' : Set W) = φ '' S) :
    (S'.restrictScalars (ZMod 2) ⊓ W₀).map psiLin =
      ((S.restrictScalars (ZMod 2) ⊓ W₀).map psiLin).map
        ((isoOfCommute φ hinj hT hPf).toLinearEquiv : X →ₗ[ZMod 2] X) :=
  map_fixed_of_commute φ hinj hT hS

@[expose] def ext2Lin (g : GL (Fin 4) K) : W →ₗ[ZMod 2] W :=
  (Matrix.mulVecLin (ext2GL g)).restrictScalars (ZMod 2)

theorem ext2Lin_apply (g : GL (Fin 4) K) (x : W) : ext2Lin g x = ext2GL g *ᵥ x := rfl

@[expose] def suIso {g : GL (Fin 4) K} (hg : g ∈ SU) : QuadraticMap.IsometryEquiv Q Q :=
  isoOfCommute (ext2Lin g) (ext2GL_injective g) (T_ext2 hg) fun w _ => Pf_ext2GL hg w

theorem suIso_psiLin {g : GL (Fin 4) K} (hg : g ∈ SU) {w : W} (hw : w ∈ W₀) :
    suIso hg (psiLin w) = psiLin (ext2GL g *ᵥ w) :=
  isoOfCommute_psiLin _ _ _ _ hw

abbrev linOf (g : GL (Fin 4) K) : V →ₗ[K] V := Matrix.mulVecLin (g : Matrix (Fin 4) (Fin 4) K)

theorem L_map (g : GL (Fin 4) K) (P : Submodule K V) :
    L (P.map (linOf g)) = (L P).map (Matrix.mulVecLin (ext2GL g)) := by
  rw [L, L, Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Submodule.mem_map, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨wedge x y, ⟨x, hx, y, hy, rfl⟩, ext2_mulVec_wedge _ x y⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, ext2_mulVec_wedge _ x y⟩

theorem perp_map_SU {g : GL (Fin 4) K} (hg : g ∈ SU) (ℓ : Submodule K V) :
    perp (ℓ.map (linOf g)) = (perp ℓ).map (linOf g) := by
  have hinv : ∀ v, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ (((g⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  ext v
  simp only [mem_perp, Submodule.mem_map, Matrix.mulVecLin_apply]
  constructor
  · intro h
    refine ⟨((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v, fun x hx => ?_, hinv v⟩
    rw [← hg.2, hinv]
    exact h _ ⟨x, hx, rfl⟩
  · rintro ⟨v', hv', rfl⟩ _ ⟨x, hx, rfl⟩
    rw [hg.2]
    exact hv' x hx

theorem M_map_SU {g : GL (Fin 4) K} (hg : g ∈ SU) (ℓ : Submodule K V) :
    M (ℓ.map (linOf g)) = (M ℓ).map (Matrix.mulVecLin (ext2GL g)) := by
  rw [M, M, Submodule.map_span, perp_map_SU hg]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Submodule.mem_map, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨wedge x y, ⟨x, hx, y, hy, rfl⟩, ext2_mulVec_wedge _ x y⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, ext2_mulVec_wedge _ x y⟩

theorem pointMap_map_SU {g : GL (Fin 4) K} (hg : g ∈ SU) (P : Submodule K V) :
    pointMap (P.map (linOf g)) =
      (pointMap P).map ((suIso hg).toLinearEquiv : X →ₗ[ZMod 2] X) := by
  refine map_fixed_iso _ _ _ _ ?_
  rw [L_map, Submodule.map_coe]
  rfl

theorem lineMap_map_SU {g : GL (Fin 4) K} (hg : g ∈ SU) (ℓ : Submodule K V) :
    lineMap (ℓ.map (linOf g)) =
      (lineMap ℓ).map ((suIso hg).toLinearEquiv : X →ₗ[ZMod 2] X) := by
  refine map_fixed_iso _ _ _ _ ?_
  rw [M_map_SU hg, Submodule.map_coe]
  rfl

end CFSG.LieType.Chevalley.C2E6Overlap
