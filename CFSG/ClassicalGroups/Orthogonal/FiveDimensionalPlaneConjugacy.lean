module

public import CFSG.ClassicalGroups.Orthogonal.UnitPlaneConjugacy
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizer
import all CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizer

public section

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel

open QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem tO_mem_C0 (F : FrameData Q) : F.tO ∈ C0 F := by
  refine ⟨F.t_so, ?_⟩
  show F.tO ∈ Subgroup.centralizer ({F.zO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply F.e.ext
  intro i
  change F.t (F.z (F.e i)) = F.z (F.t (F.e i))
  fin_cases i <;> simp [F.t_e, F.z_e]

theorem exists_C0_conj_tO_eq_iota_of_unit_plane_actions
    (F : FrameData Q)
    (b : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype))
    {u v : U F}
    (hu : (Q.comp (U F).subtype) u = 1)
    (hv : (Q.comp (U F).subtype) v = 1)
    (huv : (Q.comp (U F).subtype).polarBilin u v = 0)
    (hbu : (b : U F ≃ₗ[K] U F) u = -u)
    (hbv : (b : U F ≃ₗ[K] U F) v = -v)
    (hbfix : ∀ x : U F,
      (Q.comp (U F).subtype).polarBilin u x = 0 →
      (Q.comp (U F).subtype).polarBilin v x = 0 →
      (b : U F ≃ₗ[K] U F) x = x) :
    ∃ g : C0 F,
      (g : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
        (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ = iota F b := by
  let t0 : C0 F := ⟨F.tO, tO_mem_C0 F⟩
  let E : C0 F ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) :=
    (centralizerSubtypeEquiv F).symm.trans (centralizerEquiv F)
  let s : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) := E t0
  let u0 : U F := ⟨F.e 0, by
    rw [U, Module.End.mem_eigenspace_iff]
    change F.z (F.e 0) = (-1 : K) • F.e 0
    simpa using F.z_e (0 : Fin 5)⟩
  let v0 : U F := ⟨F.e 1, by
    rw [U, Module.End.mem_eigenspace_iff]
    change F.z (F.e 1) = (-1 : K) • F.e 1
    simpa using F.z_e (1 : Fin 5)⟩
  have hcomp : ∀ (y z : U F),
      (Q.comp (U F).subtype).polarBilin y z = Q.polarBilin (y : V) (z : V) :=
    fun _ _ => rfl
  have hu0 : (Q.comp (U F).subtype) u0 = 1 := by
    change Q (F.e 0) = 1
    exact F.norm 0 (by norm_num)
  have hv0 : (Q.comp (U F).subtype) v0 = 1 := by
    change Q (F.e 1) = 1
    exact F.norm 1 (by norm_num)
  have huv0 : (Q.comp (U F).subtype).polarBilin u0 v0 = 0 := by
    rw [hcomp]
    have h := F.orth 0 1 (by norm_num)
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  have hrestrict : ∀ (g : H F) (x : U F),
      (((restrictU F g : U F ≃ₗ[K] U F) x : U F) : V) = g.val.val.val x := by
    intro g x
    unfold restrictU soCentralizerToOperator
    rfl
  let gH : H F := (centralizerSubtypeEquiv F).symm t0
  have hE_apply : ∀ x : U F,
      (((s : U F ≃ₗ[K] U F) x : U F) : V) = F.t (x : V) := by
    intro x
    have h : s = restrictU F gH := rfl
    rw [h, hrestrict gH x]
    rfl
  have hs_u0 : (s : U F ≃ₗ[K] U F) u0 = -u0 := by
    apply Subtype.ext
    change (((s : U F ≃ₗ[K] U F) u0 : U F) : V) = -(((u0 : U F) : V))
    rw [hE_apply u0]
    change F.t (F.e 0) = -F.e 0
    simpa using F.t_e (0 : Fin 5)
  have hs_v0 : (s : U F ≃ₗ[K] U F) v0 = -v0 := by
    apply Subtype.ext
    change (((s : U F ≃ₗ[K] U F) v0 : U F) : V) = -(((v0 : U F) : V))
    rw [hE_apply v0]
    change F.t (F.e 1) = -F.e 1
    simpa using F.t_e (1 : Fin 5)
  have hsfix : ∀ x : U F,
      (Q.comp (U F).subtype).polarBilin u0 x = 0 →
      (Q.comp (U F).subtype).polarBilin v0 x = 0 →
      (s : U F ≃ₗ[K] U F) x = x := by
    intro x hx hx'
    have hx0 : polar Q (F.e 0) (x : V) = 0 := by
      rw [hcomp] at hx
      simpa only [QuadraticMap.polarBilin_apply_apply] using hx
    have hx1 : polar Q (F.e 1) (x : V) = 0 := by
      rw [hcomp] at hx'
      simpa only [QuadraticMap.polarBilin_apply_apply] using hx'
    apply Subtype.ext
    change (((s : U F ≃ₗ[K] U F) x : U F) : V) = (x : V)
    rw [hE_apply x, F.t_eq_reflect_mul, LinearEquiv.mul_apply,
      reflect_apply_of_polar_eq_zero hx1, reflect_apply_of_polar_eq_zero hx0]
  obtain ⟨γ, _, _, hγconj⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_conj_of_unit_plane_actions
      (Q.comp (U F).subtype) F.two_ne_zero s b hu0 hv0 huv0 hu hv huv
      hs_u0 hs_v0 hsfix hbu hbv hbfix
  let g : C0 F := E.symm γ
  have hEconj : (g * t0 * g⁻¹ : C0 F) = E.symm b := by
    have h := congrArg
      (fun x : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) => E.symm x)
      hγconj
    simpa [g, s] using h
  have hsub : ((g * t0 * g⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) =
      ((E.symm b : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) :=
    congrArg (fun x : C0 F => (x : TauCeti.QuadraticMap.orthogonalGroup Q)) hEconj
  have hiota : iota F = (C0 F).subtype.comp E.symm.toMonoidHom := by
    ext h
    rfl
  refine ⟨g, ?_⟩
  calc (g : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
        (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹
      = ((g * t0 * g⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) := rfl
    _ = ((E.symm b : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) := hsub
    _ = iota F b := by
      rw [hiota]
      rfl

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
