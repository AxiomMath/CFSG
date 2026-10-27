module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.QTGen4.DSGen4.Lin2A

open Matrix

section Unipotent

variable {F : Type*} [Field F] [CharP F 2]

theorem fixed_eq_zero (A : Matrix (Fin 2) (Fin 2) F) (hdet : A.det = 1) (h3 : A ^ 3 = 1)
    (h1 : A ≠ 1) (v : Fin 2 → F) (hv : A *ᵥ v = v) : v = 0 := by
  by_contra hv0
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hd0 : (A - 1).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  have hd' : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
    have := hd0
    rw [Matrix.det_fin_two] at this
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  have hsum : A 0 0 + A 1 1 = 0 := by linear_combination hdet' - hd' + h2
  have hdd : A 1 1 = A 0 0 := by linear_combination hsum - A 0 0 * h2
  have hA00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    linear_combination hdet' - A 0 0 * hdd + A 0 1 * A 1 0 * h2
  have hA2 : A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hA00
    · linear_combination A 0 1 * hsum
    · linear_combination A 1 0 * hsum
    · linear_combination hA00 + (A 1 1 - A 0 0) * hsum
  rw [pow_three, hA2, mul_one] at h3
  exact h1 h3

end Unipotent

section Natural

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

@[expose] noncomputable def natLin :
    Matrix.SpecialLinearGroup (Fin 2) F →* Module.End (ZMod 2) (Fin 2 → F) where
  toFun g := LinearMap.restrictScalars (ZMod 2) (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) F))
  map_one' := by
    ext v i
    simp
  map_mul' g h := by
    ext v i
    simp [Matrix.mulVec_mulVec]

theorem natLin_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    natLin F g v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v :=
  rfl

theorem eq_one_of_natLin_eq_one {g : Matrix.SpecialLinearGroup (Fin 2) F} (h : natLin F g = 1) :
    g = 1 := by
  have key : ∀ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j
    have := LinearMap.congr_fun h (Pi.single j 1)
    simpa [natLin_apply] using this
  apply Subtype.ext
  ext i j
  have hc := congrFun (key j) i
  rw [Matrix.mulVec_single_one] at hc
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hc

@[expose] def conjK {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Module (ZMod 2) W] (κ : V ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W →* Module.End (ZMod 2) V where
  toFun f := κ.symm.toLinearMap ∘ₗ f ∘ₗ κ.toLinearMap
  map_one' := by
    ext v
    simp
  map_mul' f g := by
    ext v
    simp

theorem conjK_apply {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Module (ZMod 2) W] (κ : V ≃ₗ[ZMod 2] W) (f : Module.End (ZMod 2) W) (x : V) :
    conjK κ f x = κ.symm (f (κ x)) :=
  rfl

variable [Module.Finite (ZMod 2) F]

@[expose] noncomputable def kappa (hF : Module.finrank (ZMod 2) F = 2) :
    (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp [hF])

@[expose] noncomputable def natMat (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F)) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  (LinearMap.toMatrixAlgEquiv' (R := ZMod 2) (n := Fin 4)).toAlgHom.toMonoidHom.comp
    ((conjK κ).comp (natLin F))

theorem natMat_mulVec (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 4 → ZMod 2) :
    natMat F κ g *ᵥ x = κ.symm (natLin F g (κ x)) := by
  have h : natMat F κ g = LinearMap.toMatrix' (conjK κ (natLin F g)) := rfl
  rw [h, LinearMap.toMatrix'_mulVec, conjK_apply]

end Natural

section Projective

variable (F : Type*) [Field F] [CharP F 2]

theorem center_sl_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - r * h2 + h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linear_combination this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

noncomputable def pslEquivSL :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq (center_sl_eq_bot F)).trans QuotientGroup.quotientBot

end Projective

section Units

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

@[expose] def toUnitsHom (f : G →* Matrix n n R) : G →* (Matrix n n R)ˣ where
  toFun g :=
    ⟨f g, f g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  map_one' := Units.ext (map_one f)
  map_mul' g h := Units.ext (map_mul f g h)

end Units

end CFSG.GH74.QTGen4.DSGen4.Lin2A
