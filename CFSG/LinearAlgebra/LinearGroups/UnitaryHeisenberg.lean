module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def heisenbergForm (h : UnitaryFieldData p f K) :
    (Fin 3 → K) →ₛₗ[h.bar] (Fin 3 → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K)
    (fun x y => h.bar (x 0) * y 2 + h.bar (x 1) * y 1 + h.bar (x 2) * y 0)
    (fun x x' y => by simp only [Pi.add_apply, map_add]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem heisenbergForm_apply (h : UnitaryFieldData p f K) (x y : Fin 3 → K) :
    heisenbergForm h x y = h.bar (x 0) * y 2 + h.bar (x 1) * y 1 + h.bar (x 2) * y 0 :=
  rfl

theorem heisenbergMatrix_mulVec_apply (h : UnitaryFieldData p f K) (a b : K) (x : Fin 3 → K) :
    (heisenbergMatrix h a b *ᵥ x) 0 = x 0 - h.bar a * x 1 + b * x 2 ∧
      (heisenbergMatrix h a b *ᵥ x) 1 = x 1 + a * x 2 ∧ (heisenbergMatrix h a b *ᵥ x) 2 = x 2 := by
  simp only [heisenbergMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩
  · simp
    ring
  · simp
  · simp

theorem unitary_heisenberg_identities (h : UnitaryFieldData p f K) :
    (∀ a b : K, h.norm a + h.trace b = 0 →
      (heisenbergMatrix h a b).det = 1 ∧
        ∀ x y : Fin 3 → K, heisenbergForm h (heisenbergMatrix h a b *ᵥ x)
          (heisenbergMatrix h a b *ᵥ y) = heisenbergForm h x y) ∧
      (∀ a b c d : K, h.norm a + h.trace b = 0 → h.norm c + h.trace d = 0 →
        heisenbergMatrix h a b * heisenbergMatrix h c d =
            heisenbergMatrix h (a + c) (b + d - h.bar a * c) ∧
          h.norm (a + c) + h.trace (b + d - h.bar a * c) = 0) ∧
      ∀ a b : K, h.norm a + h.trace b = 0 →
        (heisenbergMatrix h a b)⁻¹ = heisenbergMatrix h (-a) (h.bar b) := by
  have hrel : ∀ {a b : K}, h.norm a + h.trace b = 0 → h.bar a * a = -b - h.bar b := by
    intro a b hab
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace] at hab
    linear_combination hab
  refine ⟨fun a b hab => ⟨?_, fun x y => ?_⟩,
    fun a b c d hab hcd => ⟨heisenbergMatrix_mul h a b c d, ?_⟩, fun a b hab => ?_⟩
  · simp [heisenbergMatrix, Matrix.det_fin_three]
  · have hab' := hab
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace] at hab'
    obtain ⟨hx0, hx1, hx2⟩ := heisenbergMatrix_mulVec_apply h a b x
    obtain ⟨hy0, hy1, hy2⟩ := heisenbergMatrix_mulVec_apply h a b y
    rw [heisenbergForm_apply, heisenbergForm_apply, hx0, hx1, hx2, hy0, hy1, hy2]
    simp only [map_add, map_sub, map_mul, h.bar_bar]
    linear_combination (h.bar (x 2) * y 2) * hab'
  · have h1 := hrel hab
    have h2 := hrel hcd
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_add, map_sub, map_mul,
      h.bar_bar]
    linear_combination h1 + h2
  · rw [heisenbergMatrix_inv, hrel hab]
    congr 1
    ring

end CFSG.LinearGroups
