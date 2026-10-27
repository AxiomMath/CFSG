module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermField
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem hermForm_nondegenerate (n : ℕ) : (hermForm n).Nondegenerate := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨h0, h1⟩ := QuadraticMap.mem_radical_iff'.mp hx
  have hp : ∀ y, QuadraticMap.polar (hermForm n) x y = 0 := by
    intro y
    rw [QuadraticMap.polar, h1 y, h0]
    ring
  have key : ∀ (i : Fin n) (b : F9), (x i).re * b.re + (x i).im * b.im = 0 := by
    intro i b
    have h := hp (Pi.single i b)
    rw [polar_hermForm, herm9_re, Finset.sum_eq_single i] at h
    · simp only [Pi.single_eq_same] at h
      linear_combination -h
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  funext i
  apply QuadraticAlgebra.ext
  · simpa [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] using key i 1
  · simpa [omega9, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega] using key i omega9

@[expose] noncomputable def omegaLin (n : ℕ) : (Fin n → F9) →ₗ[ZMod 3] (Fin n → F9) where
  toFun x := omega9 • x
  map_add' x y := smul_add _ _ _
  map_smul' c x := smul_comm _ _ _

theorem omegaLin_apply {n : ℕ} (x : Fin n → F9) : omegaLin n x = omega9 • x := rfl

theorem omega9_mul_omega9 : omega9 * omega9 = -1 := by
  apply QuadraticAlgebra.ext
  · simp [omega9, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one]
  · simp [omega9, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_one]

@[expose] noncomputable def omegaEquiv (n : ℕ) : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9) :=
  LinearEquiv.ofLinear (omegaLin n) (-omegaLin n)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, omegaLin_apply, LinearMap.id_apply,
        smul_neg, smul_smul, omega9_mul_omega9, neg_smul, one_smul, neg_neg])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, omegaLin_apply, LinearMap.id_apply,
        smul_neg, smul_smul, omega9_mul_omega9, neg_smul, one_smul, neg_neg])

theorem hermForm_omega_smul {n : ℕ} (x : Fin n → F9) : hermForm n (omega9 • x) = hermForm n x := by
  rw [hermForm_apply, hermForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, omega9, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
  ring

@[expose] noncomputable def omegaOrth (n : ℕ) : OGroup (hermForm n) :=
  ⟨omegaEquiv n, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x =>
    hermForm_omega_smul x⟩

theorem omegaOrth_mul_self (n : ℕ) : omegaOrth n * omegaOrth n = piOrth (hermForm n) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change omega9 • (omega9 • x) = _
  rw [smul_smul, omega9_mul_omega9, neg_smul, one_smul]
  exact (coe_piOrth_apply x).symm

theorem quadSign_hermForm_four : quadSign (hermForm 4) = 1 := by
  have h := (exists_mul_self_eq_piOrth_iff (hermForm_nondegenerate 4)).mp
    ⟨omegaOrth 4, omegaOrth_mul_self 4⟩
  rw [finrank_hermSpace] at h
  rw [h.2]
  decide

end CFSG.OddStandard.SmallF3.Omega
