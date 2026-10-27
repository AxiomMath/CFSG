module

public import CFSG.ClassicalGroups.Unitary.Form

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

abbrev F9 : Type := QuadraticAlgebra (ZMod 3) (-1) 0

instance : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩

instance : CharP F9 3 :=
  charP_of_injective_algebraMap
    (QuadraticAlgebra.algebraMap_injective (R := ZMod 3) (a := -1) (b := 0)) 3

instance : Finite F9 := Module.finite_of_finite (ZMod 3)

theorem natCard_F9 : Nat.card F9 = (3 ^ 1) ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0), Nat.card_prod]
  simp [Nat.card_zmod]

noncomputable abbrev σ9 : F9 ≃+* F9 := unitaryInvolution F9 3 1

abbrev omega9 : F9 := QuadraticAlgebra.omega

theorem σ9_re (z : F9) : (σ9 z).re = z.re := by
  rw [σ9, unitaryInvolution_apply]
  simp only [pow_succ, pow_zero, one_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  generalize z.re = a
  generalize z.im = b
  revert a b
  decide

theorem σ9_im (z : F9) : (σ9 z).im = -z.im := by
  rw [σ9, unitaryInvolution_apply]
  simp only [pow_succ, pow_zero, one_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  generalize z.re = a
  generalize z.im = b
  revert a b
  decide

theorem re_sum9 {ι : Type*} (s : Finset ι) (f : ι → F9) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (QuadraticAlgebra.reₗ (-1 : ZMod 3) 0) f s

theorem herm9_re {n : ℕ} (x y : Fin n → F9) :
    (herm σ9 x y).re = ∑ i, ((x i).re * (y i).re + (x i).im * (y i).im) := by
  rw [herm_def, re_sum9]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QuadraticAlgebra.re_mul, σ9_re, σ9_im]
  ring

@[expose] noncomputable def normForm : QuadraticForm (ZMod 3) F9 :=
  (QuadraticMap.sq.comp (QuadraticAlgebra.reₗ (-1) 0)) +
    (QuadraticMap.sq.comp (QuadraticAlgebra.imₗ (-1) 0))

theorem normForm_apply (z : F9) : normForm z = z.re * z.re + z.im * z.im := by
  simp [normForm]

@[expose] noncomputable def hermForm (n : ℕ) : QuadraticForm (ZMod 3) (Fin n → F9) :=
  QuadraticMap.pi fun _ => normForm

theorem hermForm_apply {n : ℕ} (x : Fin n → F9) :
    hermForm n x = ∑ i, ((x i).re * (x i).re + (x i).im * (x i).im) := by
  simp [hermForm, QuadraticMap.pi_apply, normForm_apply]

theorem hermForm_eq_re {n : ℕ} (x : Fin n → F9) : hermForm n x = (herm σ9 x x).re := by
  rw [hermForm_apply, herm9_re]

theorem polar_normForm (a b : F9) :
    QuadraticMap.polar normForm a b = -(a.re * b.re + a.im * b.im) := by
  simp only [QuadraticMap.polar, normForm_apply, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (a.re * b.re + a.im * b.im) * h3

theorem polar_hermForm {n : ℕ} (x y : Fin n → F9) :
    QuadraticMap.polar (hermForm n) x y = -(herm σ9 x y).re := by
  rw [hermForm, QuadraticMap.Ring.polar_pi, herm9_re, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => polar_normForm _ _

theorem herm9_re_eq {n : ℕ} (x y : Fin n → F9) :
    (herm σ9 x y).re = -QuadraticMap.polar (hermForm n) x y := by
  rw [polar_hermForm, neg_neg]

theorem herm9_im_eq {n : ℕ} (x y : Fin n → F9) :
    (herm σ9 x y).im = QuadraticMap.polar (hermForm n) x (omega9 • y) := by
  rw [polar_hermForm, herm_smul_right, QuadraticAlgebra.re_mul]
  simp only [omega9, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
  ring

theorem herm9_eq {n : ℕ} (x y : Fin n → F9) :
    herm σ9 x y = ⟨-QuadraticMap.polar (hermForm n) x y,
      QuadraticMap.polar (hermForm n) x (omega9 • y)⟩ :=
  QuadraticAlgebra.ext (herm9_re_eq x y) (herm9_im_eq x y)

theorem finrank_F9 : Module.finrank (ZMod 3) F9 = 2 := by
  rw [Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-1 : ZMod 3) 0), Fintype.card_fin]

theorem finrank_hermSpace (n : ℕ) : Module.finrank (ZMod 3) (Fin n → F9) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_F9, mul_comm]

end CFSG.OddStandard.SmallF3.Omega
