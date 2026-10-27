module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer
open scoped IsMulCommutative

section ScalarHom

theorem f4_cases (x : F4) : x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by
  revert x
  decide

@[expose] def veeScalarFun {R : Type*} [Ring R] (w : R) (x : F4) : R :=
  if x = 0 then 0 else if x = 1 then 1 else if x = F4.ω then w else w + 1

theorem veeScalarFun_zero {R : Type*} [Ring R] (w : R) : veeScalarFun w 0 = 0 := by
  simp [veeScalarFun]

theorem veeScalarFun_one {R : Type*} [Ring R] (w : R) : veeScalarFun w 1 = 1 := by
  simp [veeScalarFun]

theorem veeScalarFun_omega {R : Type*} [Ring R] (w : R) : veeScalarFun w F4.ω = w := by
  simp (config := { decide := true }) [veeScalarFun]

theorem veeScalarFun_omega_sq {R : Type*} [Ring R] (w : R) :
    veeScalarFun w (F4.ω * F4.ω) = w + 1 := by
  simp (config := { decide := true }) [veeScalarFun]

theorem exists_ringHom_omega {R : Type*} [Ring R] (w : R) (hw : w * w + w + 1 = 0)
    (h2 : (2 : R) = 0) : ∃ φ : F4 →+* R, (∀ x, φ x = veeScalarFun w x) ∧ φ F4.ω = w := by
  obtain ⟨S, hS, hwS, -⟩ := exists_isMulCommutative_subring_pair (a := w) (b := w) rfl
  let w' : S := ⟨w, hwS⟩
  have hw' : w' * w' + w' + 1 = 0 := Subtype.ext (by simp [w', hw])
  have h2' : (2 : S) = 0 := Subtype.ext (by push_cast; exact h2)
  have hval : ∀ x, ((veeScalarFun w' x : S) : R) = veeScalarFun w x := by
    intro x
    rcases f4_cases x with rfl | rfl | rfl | rfl
    · rw [veeScalarFun_zero, veeScalarFun_zero]; rfl
    · rw [veeScalarFun_one, veeScalarFun_one]; rfl
    · rw [veeScalarFun_omega, veeScalarFun_omega]
    · rw [veeScalarFun_omega_sq, veeScalarFun_omega_sq]; rfl
  let φS : F4 →+* S :=
    { toFun := veeScalarFun w'
      map_one' := veeScalarFun_one w'
      map_zero' := veeScalarFun_zero w'
      map_mul' := by
        intro x y
        rcases f4_cases x with rfl | rfl | rfl | rfl <;>
          rcases f4_cases y with rfl | rfl | rfl | rfl <;>
          simp only [mul_zero, zero_mul, mul_one, one_mul, veeScalarFun_zero, veeScalarFun_one,
            veeScalarFun_omega, veeScalarFun_omega_sq,
            show F4.ω * (F4.ω * F4.ω) = 1 from by decide,
            show F4.ω * F4.ω * F4.ω = 1 from by decide,
            show F4.ω * F4.ω * (F4.ω * F4.ω) = F4.ω from by decide] <;>
          grind
      map_add' := by
        intro x y
        rcases f4_cases x with rfl | rfl | rfl | rfl <;>
          rcases f4_cases y with rfl | rfl | rfl | rfl <;>
          simp only [add_zero, zero_add, veeScalarFun_zero, veeScalarFun_one,
            veeScalarFun_omega, veeScalarFun_omega_sq,
            show (1 : F4) + 1 = 0 from by decide,
            show (1 : F4) + F4.ω = F4.ω * F4.ω from by decide,
            show (1 : F4) + F4.ω * F4.ω = F4.ω from by decide,
            show F4.ω + 1 = F4.ω * F4.ω from by decide,
            show F4.ω + F4.ω = 0 from by decide,
            show F4.ω + F4.ω * F4.ω = 1 from by decide,
            show F4.ω * F4.ω + 1 = F4.ω from by decide,
            show F4.ω * F4.ω + F4.ω = 1 from by decide,
            show F4.ω * F4.ω + F4.ω * F4.ω = 0 from by decide] <;>
          grind }
  refine ⟨S.subtype.comp φS, fun x => hval x, ?_⟩
  change ((veeScalarFun w' F4.ω : S) : R) = w
  rw [veeScalarFun_omega]

end ScalarHom

section LinAlg

theorem mem_range_scalar_of_forall_commute_sl_four {F : Type*} [Field F]
    (M : Matrix (Fin 4) (Fin 4) F)
    (h : ∀ g : SpecialLinearGroup (Fin 4) F,
      M * (g : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F) * M) :
    M ∈ Set.range (Matrix.scalar (Fin 4)) := by
  apply mem_range_scalar_of_commute_single
  intro i j hij
  have h1 := h ⟨transvection i j 1, det_transvection_of_ne i j hij 1⟩
  change M * transvection i j 1 = transvection i j 1 * M at h1
  rw [transvection, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (add_left_cancel h1).symm

theorem isSimpleGroup_specialLinearGroup_four_F4 :
    IsSimpleGroup (SpecialLinearGroup (Fin 4) F4) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 4) (by norm_num)
    (Or.inl (by norm_num))).2.1
  exact ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    4 F4).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL F4)).symm.isSimpleGroup

theorem eq_one_of_apply_eq_one {E : Type*} [AddCommGroup E]
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E) {x : SpecialLinearGroup (Fin 4) F4}
    (hx : ρ x ≠ 1) (g : SpecialLinearGroup (Fin 4) F4) (hg : ρ g = 1) : g = 1 := by
  have := isSimpleGroup_specialLinearGroup_four_F4
  set ρu := ρ.toHomUnits with hρu
  have hker : ∀ y, y ∈ ρu.ker ↔ ρ y = 1 := fun y => by
    rw [MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρu.ker with h | h
  · have hg' : g ∈ ρu.ker := (hker g).2 hg
    rw [h] at hg'
    exact hg'
  · exfalso
    apply hx
    have hx' : x ∈ ρu.ker := by rw [h]; exact Subgroup.mem_top x
    exact (hker x).1 hx'

theorem symm_comp_map_mulVec {F : Type*} [Field F] (σ : F ≃+* F) (N : Matrix (Fin 4) (Fin 4) F)
    (v : Fin 4 → F) : σ.symm ∘ ((N.map σ) *ᵥ v) = N *ᵥ (σ.symm ∘ v) := by
  funext i
  simp only [Function.comp_apply, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    RingEquiv.symm_apply_apply]

theorem veeFrobHom_comp_mulVec (N : Matrix (Fin 4) (Fin 4) F4) (v : Fin 4 → F4) :
    veeFrobHom ∘ (N *ᵥ v) = (N.map veeFrobHom) *ᵥ (veeFrobHom ∘ v) := by
  funext i
  simp only [Function.comp_apply, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem veeFrobHom_veeFrobHom (x : F4) : veeFrobHom (veeFrobHom x) = x := by
  revert x
  decide

theorem coe_veeFrob (g : SpecialLinearGroup (Fin 4) F4) :
    ((veeFrob g : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      (g : Matrix (Fin 4) (Fin 4) F4).map veeFrobHom :=
  rfl

theorem exists_smul_of_commute {F : Type*} [Field F] (f : (Fin 4 → F) →+ (Fin 4 → F))
    (hlin : ∀ (a : F) v, f (a • v) = a • f v)
    (hcomm : ∀ (g : SpecialLinearGroup (Fin 4) F) v,
      f ((g : Matrix (Fin 4) (Fin 4) F) *ᵥ v) = (g : Matrix (Fin 4) (Fin 4) F) *ᵥ f v) :
    ∃ c : F, ∀ v, f v = c • v := by
  let fl : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := f
      map_add' := map_add f
      map_smul' := hlin }
  have hM : ∀ g : SpecialLinearGroup (Fin 4) F,
      LinearMap.toMatrix' fl * (g : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) * LinearMap.toMatrix' fl := by
    intro g
    apply (Matrix.toLin' (R := F) (m := Fin 4) (n := Fin 4)).injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    change fl (Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) F) v) =
      Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) F) (fl v)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hcomm g v
  obtain ⟨c, hc⟩ := mem_range_scalar_of_forall_commute_sl_four _ hM
  refine ⟨c, fun v => ?_⟩
  have h1 : fl v = (LinearMap.toMatrix' fl) *ᵥ v := by
    rw [LinearMap.toMatrix'_mulVec]
  change fl v = c • v
  rw [h1, ← hc, scalar_apply]
  funext i
  rw [mulVec_diagonal]
  rfl

end LinAlg

end CFSG.SeitzReduction.LinearPilot
