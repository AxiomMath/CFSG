module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

universe u

theorem exists_field_equiv_type (K : Type u) [Field K] [Finite K] :
    ∃ (K₀ : Type) (_ : Field K₀), Nonempty (K₀ ≃+* K) :=
  ⟨Shrink.{0} K, inferInstance, ⟨(Shrink.ringEquiv.{0} K : Shrink.{0} K ≃+* K)⟩⟩

section Transport

variable {K₀ K V : Type*} [Field K₀] [Field K] [AddCommGroup V] [Module K V] [Module K₀ V]
  (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)

include hsmul

@[expose] noncomputable def formOfRingEquiv (Q : QuadraticForm K V) : QuadraticForm K₀ V where
  toFun v := e.symm (Q v)
  toFun_smul a v := by
    rw [hsmul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      RingEquiv.symm_apply_apply]
  exists_companion' := by
    refine ⟨LinearMap.mk₂ K₀ (fun x y => e.symm (polar Q x y)) ?_ ?_ ?_ ?_, fun x y => ?_⟩
    · intro x x' y
      simp only [polar_add_left, map_add]
    · intro c x y
      simp only [hsmul, polar_smul_left, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    · intro x y y'
      simp only [polar_add_right, map_add]
    · intro c x y
      simp only [hsmul, polar_smul_right, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    · simp only [QuadraticMap.map_add Q x y, map_add, LinearMap.mk₂_apply]

variable {e hsmul}

theorem formOfRingEquiv_apply (Q : QuadraticForm K V) (v : V) :
    formOfRingEquiv e hsmul Q v = e.symm (Q v) := rfl

theorem polar_formOfRingEquiv (Q : QuadraticForm K V) (x y : V) :
    polar (formOfRingEquiv e hsmul Q) x y = e.symm (polar Q x y) := by
  simp only [polar, formOfRingEquiv_apply, map_sub, map_add]

theorem nondegenerate_formOfRingEquiv {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin (formOfRingEquiv e hsmul Q)).Nondegenerate := by
  refine ⟨fun x hx => hQ.1 x fun y => ?_, fun y hy => hQ.2 y fun x => ?_⟩
  · have := hx y
    rw [polarBilin_apply_apply, polar_formOfRingEquiv, map_eq_zero_iff _ e.symm.injective] at this
    simpa using this
  · have := hy x
    rw [polarBilin_apply_apply, polar_formOfRingEquiv, map_eq_zero_iff _ e.symm.injective] at this
    simpa using this

variable (e hsmul)

@[expose] def restrictScalarsEquiv (g : V ≃ₗ[K₀] V) : V ≃ₗ[K] V where
  toFun := g
  map_add' := g.map_add
  map_smul' c x := by
    have h := g.map_smul (e.symm c) x
    rw [hsmul, hsmul, RingEquiv.apply_symm_apply] at h
    exact h
  invFun := g.symm
  left_inv := g.left_inv
  right_inv := g.right_inv

@[expose] def restrictScalarsHom : (V ≃ₗ[K₀] V) →* (V ≃ₗ[K] V) where
  toFun := restrictScalarsEquiv e hsmul
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

variable {e hsmul}

theorem restrictScalarsHom_apply (g : V ≃ₗ[K₀] V) (v : V) :
    restrictScalarsHom e hsmul g v = g v := rfl

theorem restrictScalarsHom_injective : Function.Injective (restrictScalarsHom e hsmul) :=
  fun g h H => LinearEquiv.ext fun v => by
    simpa [restrictScalarsHom_apply] using DFunLike.congr_fun H v

theorem restrictScalarsHom_eichler (Q : QuadraticForm K V) (u w : V) :
    restrictScalarsHom e hsmul (eichler (formOfRingEquiv e hsmul Q) u w) = eichler Q u w := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h' : formOfRingEquiv e hsmul Q u = 0 ∧ polar (formOfRingEquiv e hsmul Q) u w = 0 := by
      rw [formOfRingEquiv_apply, polar_formOfRingEquiv, h.1, h.2, map_zero]
      exact ⟨rfl, rfl⟩
    refine LinearEquiv.ext fun x => ?_
    rw [restrictScalarsHom_apply, eichler_apply h'.1 h'.2, eichler_apply h.1 h.2]
    simp only [polar_formOfRingEquiv, formOfRingEquiv_apply, hsmul, map_add, map_mul,
      RingEquiv.apply_symm_apply]
  · have h' : ¬(formOfRingEquiv e hsmul Q u = 0 ∧ polar (formOfRingEquiv e hsmul Q) u w = 0) := by
      rw [formOfRingEquiv_apply, polar_formOfRingEquiv, map_eq_zero_iff _ e.symm.injective,
        map_eq_zero_iff _ e.symm.injective]
      exact h
    rw [eichler_of_not h, eichler_of_not h', map_one]

theorem mem_orthogonalGroup_restrictScalarsHom {Q : QuadraticForm K V} {g : V ≃ₗ[K₀] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)) :
    restrictScalarsHom e hsmul g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
  intro x
  have := hg x
  rw [formOfRingEquiv_apply, formOfRingEquiv_apply] at this
  exact e.symm.injective this

theorem mem_rootGroup_restrictScalarsHom {Q : QuadraticForm K V} {u : V} {g : V ≃ₗ[K₀] V}
    (hg : g ∈ rootGroup (formOfRingEquiv e hsmul Q) u) :
    restrictScalarsHom e hsmul g ∈ rootGroup Q u := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  rw [polar_formOfRingEquiv, map_eq_zero_iff _ e.symm.injective] at hw
  exact mem_rootGroup.mpr ⟨w, hw, (restrictScalarsHom_eichler Q u w).symm⟩

end Transport

end CFSG.ClassicalGroups.Orthogonal
