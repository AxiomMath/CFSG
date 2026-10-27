module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
import CFSG.Quasithin.Background.F7TwoInvU3OddBar

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Module Matrix

theorem exists_hyperbolic_three {F W : Type} [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0)
    [AddCommGroup W] [Module F W] (hW : finrank F W = 3)
    (B : LinearMap.BilinForm F W) (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∃ e f w : W, B e e = 0 ∧ B e f = 1 ∧ B f f = 0 ∧ B e w = 0 ∧ B f w = 0 ∧
      LinearIndependent F ![e, f, w] := by
  classical
  haveI : Finite F := Finite.of_fintype F
  have hfin : Module.Finite F W := Module.finite_of_finrank_pos (by omega)
  have hs : ∀ x y, B x y = B y x := fun x y => (hB.eq y x).symm
  obtain ⟨e, he0, hee⟩ := CFSG.Quasithin.F7Two.U3Odd.exists_isotropic_of_finrank_three hW B
  obtain ⟨f', hf'⟩ : ∃ f', B e f' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (hnd.1 e hcon)
  obtain ⟨f₀, hef₀⟩ : ∃ f₀, B e f₀ = 1 :=
    ⟨(B e f')⁻¹ • f', by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf']⟩
  obtain ⟨f, hef, hff⟩ : ∃ f, B e f = 1 ∧ B f f = 0 := by
    have h1 : B f₀ e = 1 := by rw [hs, hef₀]
    refine ⟨f₀ - (B f₀ f₀ / 2) • e, ?_, ?_⟩
    · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee,
        hef₀, mul_zero, sub_zero]
    · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee, h1,
        hef₀, mul_zero, sub_zero, mul_one]
      field_simp
      ring
  have hfe : B f e = 1 := by rw [hs, hef]
  let φ : W →ₗ[F] (Fin 2 → F) := LinearMap.pi ![B e, B f]
  have hφ : Function.Surjective φ := by
    intro v
    refine ⟨v 0 • f + v 1 • e, ?_⟩
    ext i
    fin_cases i
    · simp [φ, hef, hee, hff]
    · simp [φ, hfe, hee, hff, hef]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, Module.finrank_fin_fun, hW] at hrk
  have hker : 0 < finrank F (LinearMap.ker φ) := by omega
  obtain ⟨⟨w, hwk⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hker
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hew : B e w = 0 := by
    have := congrFun hwk 0
    simpa [φ] using this
  have hfw : B f w = 0 := by
    have := congrFun (LinearMap.mem_ker.mp hwk) 1
    simpa [φ] using this
  refine ⟨e, f, w, hee, hef, hff, hew, hfw, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hwe : B w e = 0 := by rw [hs, hew]
  have hwf : B w f = 0 := by rw [hs, hfw]
  have h1 := congrArg (B e) hg
  have h2' := congrArg (B f) hg
  simp only [map_add, map_smul, map_zero, hee, hef, hew, hfe, hff, hfw, smul_eq_mul, mul_zero,
    mul_one, zero_add, add_zero] at h1 h2'
  have hg1 : g 1 = 0 := by simpa using h1
  have hg0 : g 0 = 0 := by simpa [hg1] using h2'
  have hg2 : g 2 = 0 := by
    rw [hg0, hg1] at hg
    simpa [hw0'] using hg
  intro i
  fin_cases i <;> simp [hg0, hg1, hg2]

theorem exists_isometry_two_three {F W : Type} [Field F] [Fintype F] (hF : Fintype.card F = 5)
    [AddCommGroup W] [Module F W] (hW : finrank F W = 3)
    (B : LinearMap.BilinForm F W) (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∃ (b : Basis (Fin 3) F W) (y : W ≃ₗ[F] W), (∀ v w, B (y v) (y w) = B v w) ∧
      y (b 0) = (2 : F) • b 0 ∧ y (b 1) = (3 : F) • b 1 ∧ y (b 2) = b 2 := by
  classical
  have h5 : (5 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rwa [hF, Nat.cast_ofNat] at this
  have h23 : (2 : F) * 3 = 1 := by linear_combination h5
  have h32 : (3 : F) * 2 = 1 := by rw [mul_comm]; exact h23
  have h2 : (2 : F) ≠ 0 := fun h => by rw [h] at h23; simp at h23
  have h3 : (3 : F) ≠ 0 := fun h => by rw [h] at h23; simp at h23
  haveI : Nonempty (Fin 3) := ⟨0⟩
  obtain ⟨e, f, w, hee, hef, hff, hew, hfw, hli⟩ := exists_hyperbolic_three h2 hW B hB hnd
  have hs : ∀ x y, B x y = B y x := fun x y => (hB.eq y x).symm
  let b : Basis (Fin 3) F W :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hW])
  have hb : ⇑b = ![e, f, w] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb0 : b 0 = e := by simp [hb]
  have hb1 : b 1 = f := by simp [hb]
  have hb2 : b 2 = w := by simp [hb]
  let u : Fin 3 → Fˣ := ![Units.mk0 2 h2, Units.mk0 3 h3, 1]
  let y : W ≃ₗ[F] W := b.equiv (b.unitsSMul u) (Equiv.refl _)
  have hy : ∀ i, y (b i) = (u i : F) • b i := by
    intro i
    simp [y, Basis.equiv_apply, Basis.unitsSMul_apply, Units.smul_def]
  have hy0 : y (b 0) = (2 : F) • b 0 := by simpa [u] using hy 0
  have hy1 : y (b 1) = (3 : F) • b 1 := by simpa [u] using hy 1
  have hy2 : y (b 2) = b 2 := by simpa [u] using hy 2
  refine ⟨b, y, ?_, hy0, hy1, hy2⟩
  have hext : B = B.compl₁₂ (y : W →ₗ[F] W) (y : W →ₗ[F] W) := by
    refine LinearMap.BilinForm.ext_basis b fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hy i, hy j]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [u, hb0, hb1, hb2, hee, hef, hff, hew, hfw, hs w e, hs w f, hs f e, h23, h32] <;>
      first | rfl | skip
  intro v v'
  have := LinearMap.congr_fun₂ hext v v'
  simpa using this.symm

end CFSG.OddStandard.SmallF3.Omega
