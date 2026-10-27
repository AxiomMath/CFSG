module

public import CFSG.GroupTheory.WeirSylow.FormSpace
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module

variable {K : Type} [Field K] {R : Type} [AddCommMonoid R]

@[expose] noncomputable def piDiagIsom (S₀ : FormSpace K R) (r : ℕ) :
    (Fin r → S₀.isom) →* (FormSpace.pi fun _ : Fin r => S₀).isom :=
  piIsometryHom K fun _ : Fin r => S₀.F

theorem piDiagIsom_apply (S₀ : FormSpace K R) (r : ℕ) (g : Fin r → S₀.isom) (v : Fin r → S₀.V)
    (i : Fin r) :
    ((piDiagIsom S₀ r g : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)) v) i =
      (g i : S₀.V ≃ₗ[K] S₀.V) (v i) :=
  rfl

theorem piDiagIsom_injective (S₀ : FormSpace K R) (r : ℕ) :
    Function.Injective (piDiagIsom S₀ r) :=
  piIsometryHom_injective K fun _ : Fin r => S₀.F

@[expose] noncomputable def piPermIsom (S₀ : FormSpace K R) (r : ℕ) :
    Equiv.Perm (Fin r) →* (FormSpace.pi fun _ : Fin r => S₀).isom where
  toFun σ := ⟨LinearEquiv.funCongrLeft K S₀.V σ⁻¹, fun x y =>
    Equiv.sum_comp σ⁻¹ (fun i => S₀.F (x i) (y i))⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun v => funext fun i => rfl)
  map_mul' σ τ := Subtype.ext (LinearEquiv.ext fun v => funext fun i => by
    change v ((σ * τ)⁻¹ i) = v (τ⁻¹ (σ⁻¹ i))
    rw [mul_inv_rev, Equiv.Perm.mul_apply])

theorem piPermIsom_apply (S₀ : FormSpace K R) (r : ℕ) (σ : Equiv.Perm (Fin r))
    (v : Fin r → S₀.V) (i : Fin r) :
    ((piPermIsom S₀ r σ : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)) v) i = v (σ⁻¹ i) :=
  rfl

theorem piPermIsom_conj (S₀ : FormSpace K R) (r : ℕ) (σ : Equiv.Perm (Fin r))
    (g : Fin r → S₀.isom) :
    piPermIsom S₀ r σ * piDiagIsom S₀ r g * (piPermIsom S₀ r σ)⁻¹ =
      piDiagIsom S₀ r (g ∘ ⇑σ⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (LinearEquiv.ext fun v => funext fun j => rfl)

theorem det_piDiagIsom (S₀ : FormSpace K R) (r : ℕ) (g : Fin r → S₀.isom) :
    LinearMap.det ((piDiagIsom S₀ r g : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)) :
      (Fin r → S₀.V) →ₗ[K] (Fin r → S₀.V)) =
      ∏ i, LinearMap.det ((g i : S₀.V ≃ₗ[K] S₀.V) : S₀.V →ₗ[K] S₀.V) := by
  have h : ((piDiagIsom S₀ r g : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)) :
      (Fin r → S₀.V) →ₗ[K] (Fin r → S₀.V)) =
      LinearMap.pi (fun i => ((g i : S₀.V ≃ₗ[K] S₀.V) : S₀.V →ₗ[K] S₀.V).comp
        (LinearMap.proj i)) := by
    ext v i
    rfl
  rw [h, LinearMap.det_pi]

section PermDet

variable {L : Type} [AddCommGroup L] [Module K L]

private noncomputable def piPermBasis {e : ℕ} (b : Module.Basis (Fin e) K L) (r : ℕ) :
    Module.Basis (Fin r × Fin e) K (Fin r → L) :=
  (Pi.basis fun _ : Fin r => b).reindex (Equiv.sigmaEquivProd (Fin r) (Fin e))

private theorem piPermBasis_apply {e : ℕ} (b : Module.Basis (Fin e) K L) (r : ℕ) (j : Fin r)
    (l : Fin e) : piPermBasis b r (j, l) = Pi.single j (b l) := by
  simp [piPermBasis]

private theorem piPerm_single {r : ℕ} (σ : Equiv.Perm (Fin r)) (j : Fin r) (x : L) :
    LinearEquiv.funCongrLeft K L σ⁻¹ (Pi.single j x) = Pi.single (σ j) x := by
  funext m
  show (Pi.single j x : Fin r → L) (σ⁻¹ m) = (Pi.single (σ j) x : Fin r → L) m
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private theorem piPerm_basis {e : ℕ} (b : Module.Basis (Fin e) K L) {r : ℕ}
    (σ : Equiv.Perm (Fin r)) (j : Fin r) (l : Fin e) :
    (LinearEquiv.funCongrLeft K L σ⁻¹ : (Fin r → L) →ₗ[K] (Fin r → L)) (piPermBasis b r (j, l)) =
      piPermBasis b r (σ j, l) := by
  rw [piPermBasis_apply, piPermBasis_apply]
  exact piPerm_single σ j (b l)

private theorem piPerm_det {e : ℕ} (b : Module.Basis (Fin e) K L) {r : ℕ}
    (σ : Equiv.Perm (Fin r)) :
    LinearMap.det ((LinearEquiv.funCongrLeft K L σ⁻¹ : (Fin r → L) ≃ₗ[K] (Fin r → L)) :
        (Fin r → L) →ₗ[K] (Fin r → L)) = (((Equiv.Perm.sign σ ^ e : ℤˣ) : ℤ) : K) := by
  have hmat : LinearMap.toMatrix (piPermBasis b r) (piPermBasis b r)
      ((LinearEquiv.funCongrLeft K L σ⁻¹ : (Fin r → L) ≃ₗ[K] (Fin r → L)) :
        (Fin r → L) →ₗ[K] (Fin r → L)) =
      Matrix.transpose (Equiv.Perm.permMatrix K (Equiv.prodCongr σ (Equiv.refl (Fin e))) :
        Matrix (Fin r × Fin e) (Fin r × Fin e) K) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [LinearMap.toMatrix_apply, piPerm_basis, Module.Basis.repr_self, Finsupp.single_apply]
    simp
  have hsign : Equiv.Perm.sign (Equiv.prodCongr σ (Equiv.refl (Fin e))) =
      Equiv.Perm.sign σ ^ e := by
    rw [Equiv.prodCongr_refl_right, Equiv.Perm.sign_prodCongrLeft]
    simp
  rw [← LinearMap.det_toMatrix (piPermBasis b r), hmat, Matrix.det_transpose,
    Matrix.det_permutation, hsign]

end PermDet

theorem det_piPermIsom (S₀ : FormSpace K R) (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    LinearMap.det ((piPermIsom S₀ r σ : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)) :
      (Fin r → S₀.V) →ₗ[K] (Fin r → S₀.V)) =
      (((Equiv.Perm.sign σ ^ finrank K S₀.V : ℤˣ) : ℤ) : K) :=
  piPerm_det (Module.finBasis K S₀.V) σ

@[expose] noncomputable def prodLeftIsom (S T₀ : FormSpace K R) :
    S.isom →* (FormSpace.prod S T₀).isom :=
  (prodIsometryHom K S.F T₀.F).comp ((MonoidHom.id _).prod 1)

theorem prodLeftIsom_injective (S T₀ : FormSpace K R) :
    Function.Injective (prodLeftIsom S T₀) := by
  intro g h hgh
  have h' : prodIsometryHom K S.F T₀.F (g, 1) = prodIsometryHom K S.F T₀.F (h, 1) := hgh
  exact congrArg Prod.fst (prodIsometryHom_injective K S.F T₀.F h')

theorem det_prodLeftIsom (S T₀ : FormSpace K R) (g : S.isom) :
    LinearMap.det ((prodLeftIsom S T₀ g : (S.V × T₀.V) ≃ₗ[K] (S.V × T₀.V)) :
      (S.V × T₀.V) →ₗ[K] (S.V × T₀.V)) =
      LinearMap.det ((g : S.V ≃ₗ[K] S.V) : S.V →ₗ[K] S.V) := by
  have h : ((prodLeftIsom S T₀ g : (S.V × T₀.V) ≃ₗ[K] (S.V × T₀.V)) :
      (S.V × T₀.V) →ₗ[K] (S.V × T₀.V)) =
      LinearMap.prodMap ((g : S.V ≃ₗ[K] S.V) : S.V →ₗ[K] S.V) LinearMap.id :=
    LinearMap.ext fun _ => rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
