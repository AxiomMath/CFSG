module

public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

namespace CFSG.CGT.T75P

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

@[expose] def sZ1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def sZ2 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

theorem sZ1_sq : sZ1 * sZ1 = 1 := by decide +kernel

theorem sZ2_sq : sZ2 * sZ2 = 1 := by decide +kernel

theorem sZ12_pow4 : (sZ1 * sZ2) ^ 4 = 1 := by decide +kernel

theorem sZ12_pow2 : (sZ1 * sZ2) ^ 2 ≠ 1 := by decide +kernel

theorem sZ1_det : sZ1.det = 1 := by simp [sZ1, Matrix.det_fin_three]

theorem sZ2_det : sZ2.det = 1 := by simp [sZ2, Matrix.det_fin_three]

theorem isTransvection_of_apply {F : Type} [Field F] {n : ℕ} (u : SL(n, F))
    (f : Module.Dual F (Fin n → F)) (v : Fin n → F) (hfv : f v = 0)
    (hu : ∀ x : Fin n → F, (u : Matrix (Fin n) (Fin n) F) *ᵥ x = x + f x • v) (hne : u ≠ 1) :
    IsTransvection u := by
  refine ⟨hne, f, v, hfv, ?_⟩
  ext x i
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, hu]
  simp [LinearEquiv.transvection, LinearMap.transvection]

theorem exists_transvection_pair (F : Type) [Field F] [CharP F 2] :
    ∃ s₁ s₂ : SL(3, F), IsTransvection s₁ ∧ IsTransvection s₂ ∧ s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧
      (s₁ * s₂) ^ 4 = 1 ∧ (s₁ * s₂) ^ 2 ≠ 1 := by
  let κ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let a : Matrix (Fin 3) (Fin 3) F := κ.mapMatrix sZ1
  let b : Matrix (Fin 3) (Fin 3) F := κ.mapMatrix sZ2
  have ha : a.det = 1 := by
    have := RingHom.map_det κ sZ1
    rw [sZ1_det, map_one] at this
    exact this.symm
  have hb : b.det = 1 := by
    have := RingHom.map_det κ sZ2
    rw [sZ2_det, map_one] at this
    exact this.symm
  let s₁ : SL(3, F) := ⟨a, ha⟩
  let s₂ : SL(3, F) := ⟨b, hb⟩
  have h11 : s₁ * s₁ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show κ.mapMatrix sZ1 * κ.mapMatrix sZ1 = 1
    rw [← map_mul, sZ1_sq, map_one]
  have h22 : s₂ * s₂ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show κ.mapMatrix sZ2 * κ.mapMatrix sZ2 = 1
    rw [← map_mul, sZ2_sq, map_one]
  have hmap : ∀ k : ℕ, (((s₁ * s₂) ^ k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      κ.mapMatrix ((sZ1 * sZ2) ^ k) := fun k => by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, map_pow, map_mul]
  have hinj : Function.Injective (κ.mapMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) →+*
      Matrix (Fin 3) (Fin 3) F) := Matrix.map_injective κ.injective
  refine ⟨s₁, s₂, ?_, ?_, h11, h22, ?_, ?_⟩
  · refine isTransvection_of_apply s₁ (LinearMap.proj 1) (Pi.single 0 1) (by simp) (fun x => ?_) ?_
    · funext i
      fin_cases i <;> simp [s₁, a, κ, sZ1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro h
      have := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F) 0 1) h
      simp [s₁, a, κ, sZ1] at this
  · refine isTransvection_of_apply s₂ (LinearMap.proj 2) (Pi.single 1 1) (by simp) (fun x => ?_) ?_
    · funext i
      fin_cases i <;> simp [s₂, b, κ, sZ2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro h
      have := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F) 1 2) h
      simp [s₂, b, κ, sZ2] at this
  · apply Subtype.ext
    rw [hmap, sZ12_pow4, map_one, Matrix.SpecialLinearGroup.coe_one]
  · intro h
    have h' := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F)) h
    simp only [hmap, Matrix.SpecialLinearGroup.coe_one] at h'
    exact sZ12_pow2 (hinj (by rw [h', map_one]))

end CFSG.CGT.T75P
