module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGBlock
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFHyp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

section Polar

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (GaussField F) V] [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V}
  {a : V ≃ₗ[F] V}

theorem re_polar_gaussQuad (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (x y : V) :
    (polar (gaussQuad Q hω hg) x y).re = 2 * polar Q x y := by
  rw [polar_gaussQuad, QuadraticAlgebra.re_mul, gaussBilin_apply]
  have h3 : (2 : GaussField F).re = 2 := rfl
  have h4 : (2 : GaussField F).im = 0 := rfl
  rw [h3, h4]
  ring

theorem im_polar_gaussQuad (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (x y : V) :
    (polar (gaussQuad Q hω hg) x y).im = -(2 * polar Q (a x) y) := by
  rw [polar_gaussQuad, QuadraticAlgebra.im_mul, gaussBilin_apply]
  have h3 : (2 : GaussField F).re = 2 := rfl
  have h4 : (2 : GaussField F).im = 0 := rfl
  rw [h3, h4]
  ring

theorem polar_eq_zero_of_gauss (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {x y : V}
    (h : polar (gaussQuad Q hω hg) x y = 0) :
    polar Q x y = 0 ∧ polar Q (a x) y = 0 ∧ polar Q x (a y) = 0 ∧ polar Q (a x) (a y) = 0 := by
  have h1 := re_polar_gaussQuad hω hg x y
  have h3 := im_polar_gaussQuad hω hg x y
  rw [h, QuadraticAlgebra.re_zero] at h1
  rw [h, QuadraticAlgebra.im_zero] at h3
  have e1 : polar Q x y = 0 := (mul_eq_zero.mp h1.symm).resolve_left h2
  have e2 : polar Q (a x) y = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp h3.symm)).resolve_left h2
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [polar_a_right hω hg]
    exact e2
  · rw [polar_a_a hg, e1, neg_zero]

theorem polar_of_gauss_one (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {x y : V}
    (h : polar (gaussQuad Q hω hg) x y = 1) :
    2 * polar Q x y = 1 ∧ polar Q (a x) y = 0 ∧ polar Q x (a y) = 0 ∧
      2 * polar Q (a x) (a y) = -1 := by
  have h1 := re_polar_gaussQuad hω hg x y
  have h3 := im_polar_gaussQuad hω hg x y
  rw [h, QuadraticAlgebra.re_one] at h1
  rw [h, QuadraticAlgebra.im_one] at h3
  have e2 : polar Q (a x) y = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp h3.symm)).resolve_left h2
  refine ⟨h1.symm, e2, ?_, ?_⟩
  · rw [polar_a_right hω hg]
    exact e2
  · rw [polar_a_a hg]
    linear_combination h1

theorem singular_of_gauss (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {x : V} (h : gaussQuad Q hω hg x = 0) :
    Q x = 0 ∧ Q (a x) = 0 ∧ polar Q x x = 0 ∧ polar Q (a x) x = 0 ∧ polar Q x (a x) = 0 ∧
      polar Q (a x) (a x) = 0 := by
  have hp : polar (gaussQuad Q hω hg) x x = 0 := by rw [QuadraticMap.polar_self, h, smul_zero]
  obtain ⟨e1, e2, e3, e4⟩ := polar_eq_zero_of_gauss h2 hω hg hp
  have hQx : Q x = 0 := by
    have := polar_self Q x
    rw [e1, nsmul_eq_mul, Nat.cast_ofNat] at this
    exact (mul_eq_zero.mp this.symm).resolve_left h2
  refine ⟨hQx, by rw [hg, hQx, mul_zero], e1, e2, e3, e4⟩

end Polar

section Witt

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [Module (GaussField F) V] [IsScalarTower F (GaussField F) V]
  {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

theorem isHypFam_of_orth_gauss (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {P P' : HypPair (gaussQuad Q hω hg)}
    (hPP : P.Orth P') : ∃ v : Fin 4 → Bool → V, IsHypFam Q v := by
  have pee := singular_of_gauss h2 hω hg P.Q_e
  have pff := singular_of_gauss h2 hω hg P.Q_f
  have pee' := singular_of_gauss h2 hω hg P'.Q_e
  have pff' := singular_of_gauss h2 hω hg P'.Q_f
  have hef := polar_of_gauss_one h2 hω hg P.polar_ef
  have hef' := polar_of_gauss_one h2 hω hg P'.polar_ef
  have hee := polar_eq_zero_of_gauss h2 hω hg hPP.ee
  have hef2 := polar_eq_zero_of_gauss h2 hω hg hPP.ef
  have hfe2 := polar_eq_zero_of_gauss h2 hω hg hPP.fe
  have hff := polar_eq_zero_of_gauss h2 hω hg hPP.ff
  have c : ∀ x y : V, polar Q x y = polar Q y x := fun x y => polar_comm Q x y
  refine ⟨_, isHypFam_of_table_n ![P.e, a P.e, P'.e, a P'.e]
    ![(2 : F) • P.f, (-2 : F) • a P.f, (2 : F) • P'.f, (-2 : F) • a P'.f] ?_ ?_ ?_ ?_ ?_⟩
  · intro i
    fin_cases i <;> simp [pee.1, pee.2.1, pee'.1, pee'.2.1]
  · intro i
    fin_cases i <;> simp [QuadraticMap.map_smul, pff.1, pff.2.1, pff'.1, pff'.2.1]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pee.2.2.1, pee.2.2.2.1, pee.2.2.2.2.1, pee.2.2.2.2.2, pee'.2.2.1, pee'.2.2.2.1,
        pee'.2.2.2.2.1, pee'.2.2.2.2.2, hee.1, hee.2.1, hee.2.2.1, hee.2.2.2,
        c P'.e P.e, c P'.e (a P.e), c (a P'.e) P.e, c (a P'.e) (a P.e)]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [polar_smul_left, polar_smul_right, QuadraticMap.map_smul, pff.1, pff.2.1, pff'.1,
        pff'.2.1, pff.2.2.2.1, pff.2.2.2.2.1, pff'.2.2.2.1, pff'.2.2.2.2.1, hff.1, hff.2.1,
        hff.2.2.1, hff.2.2.2, c P'.f P.f, c P'.f (a P.f), c (a P'.f) P.f, c (a P'.f) (a P.f)]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [polar_smul_right, hef.1, hef.2.1, hef.2.2.1, hef.2.2.2, hef'.1, hef'.2.1,
        hef'.2.2.1, hef'.2.2.2, hef2.1, hef2.2.1, hef2.2.2.1, hef2.2.2.2, c P'.e P.f,
        c P'.e (a P.f), c (a P'.e) P.f, c (a P'.e) (a P.f), hfe2.1, hfe2.2.1, hfe2.2.2.1,
        hfe2.2.2.2]

end Witt

section Case

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem finrank_gauss [Fact (Nat.card F = 3)] [Module (GaussField F) V]
    [IsScalarTower F (GaussField F) V] :
    Module.finrank F V = 2 * Module.finrank (GaussField F) V := by
  have := finiteDimensional_gauss F V
  rw [← Module.finrank_mul_finrank F (GaussField F) V, QuadraticAlgebra.finrank_eq_two]

theorem oddCoreIn_fixed_conjES_of_sq_neg_one (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate)
    (hE : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {a : V ≃ₗ[F] V} (ha : ∀ v, a (a v) = -v) (hg : ∀ v, Q (a v) = (-1 : F) * Q v)
    (hdim : 10 ≤ Module.finrank F V ∨
      (Module.finrank F V = 8 ∧ ∀ v : Fin 4 → Bool → V, ¬ IsHypFam Q v)) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
      (Q3MFOD.conjES Q hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  let _ : Module (GaussField F) V := gaussModule a ha
  have : IsScalarTower F (GaussField F) V := ⟨fun c z v => by
    show (c • z).re • v + (c • z).im • a v = c • (z.re • v + z.im • a v)
    rw [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_add, smul_eq_mul, smul_eq_mul,
      mul_smul, mul_smul]⟩
  have hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v := fun v => by
    show (QuadraticAlgebra.omega : GaussField F).re • v +
      (QuadraticAlgebra.omega : GaussField F).im • a v = a v
    rw [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul, zero_add]
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hfr := finrank_gauss (F := F) (V := V)
  have hodd : Odd (Nat.card (GaussField F)) := by rw [card_gaussField_eq_nine hF]; decide
  have h9 : 5 ≤ Nat.card (GaussField F) := by rw [card_gaussField_eq_nine hF]; norm_num
  have := finiteDimensional_gauss F V
  have hQq := nondegenerate_gaussQuad h2 hω hg hQ
  have hdim3 : 3 ≤ Module.finrank F V := by omega
  have h3 : 3 ≤ Module.finrank (GaussField F) V := by omega
  have hq : CFSG.Open.IsQuasisimple ↥(elementaryGroup (gaussQuad Q hω hg)) := by
    refine isQuasisimple_elementaryGroup_small hodd h9 hQq h3 ?_
    rcases hdim with h | ⟨-, hW⟩
    · left
      omega
    · right
      intro P P' hPP
      obtain ⟨v, hv⟩ := isHypFam_of_orth_gauss h2 hω hg hPP
      exact hW v hv
  exact oddCoreIn_fixed_conjES_of_gauss hF hQ hdim3 hE hω hg h3 hq

end Case

end CFSG.ClassicalInvolution.Q3.TL4.Gauss
