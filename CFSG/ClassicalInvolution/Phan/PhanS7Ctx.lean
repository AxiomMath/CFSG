module

public import CFSG.ClassicalInvolution.Phan.PhanS5Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.PhanB3.H (mk7 polar_mk7 quad_mk7)

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

@[expose] noncomputable def hrm (x y : W7 K) : K := polar (quadOdd 3 K) x (conjV D y)

@[expose] def IsFF7 (x : W7 K) : Prop := quadOdd 3 K x = 0 ∧ hrm D x x ≠ 0

@[expose] def vXi : W7 K := mk7 1 0 0 1 0 0 D.θ

@[expose] def vE2 : W7 K := mk7 0 1 (-D.θ) 0 (-1) D.θ 0

@[expose] def vE3 : W7 K := mk7 0 1 D.θ 0 1 D.θ 0

@[expose] def LineFix (g : spinGroup (quadOdd 3 F)) (x : W7 K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ actK g x = c • x

theorem conjV_apply (x : W7 K) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : conjV D x s = D.τ (x s) := rfl

theorem conjV_conjV (x : W7 K) : conjV D (conjV D x) = x := by
  funext s
  simp [conjV_apply, D.tau_tau]

theorem conjV_smul (c : K) (x : W7 K) : conjV D (c • x) = D.τ c • conjV D x := by
  funext s
  simp [conjV_apply]

theorem conjV_add (x y : W7 K) : conjV D (x + y) = conjV D x + conjV D y := by
  funext s
  simp [conjV_apply]

theorem actK_conjV (g : spinGroup (quadOdd 3 F)) (x : W7 K) :
    actK g (conjV D x) = conjV D (actK g x) :=
  extK_mapV D.τ D.tau_alg _ x

theorem hrm_smul_left (c : K) (x y : W7 K) : hrm D (c • x) y = c * hrm D x y := by
  simp [hrm, QuadraticMap.polar_smul_left]

theorem hrm_smul_right (c : K) (x y : W7 K) : hrm D x (c • y) = D.τ c * hrm D x y := by
  simp [hrm, conjV_smul, QuadraticMap.polar_smul_right]

theorem hrm_actK (g : spinGroup (quadOdd 3 F)) (x y : W7 K) :
    hrm D (actK g x) (actK g y) = hrm D x y := by
  rw [hrm, hrm, ← actK_conjV, polar_actK]

theorem quad_actK (h2 : (2 : K) ≠ 0) (g : spinGroup (quadOdd 3 F)) (x : W7 K) :
    quadOdd 3 K (actK g x) = quadOdd 3 K x := by
  have h := polar_actK (K := K) g x x
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at h
  have h' : (2 : K) * quadOdd 3 K (actK g x) = 2 * quadOdd 3 K x := by
    rw [two_mul, two_mul]
    simpa [two_smul] using h
  exact mul_left_cancel₀ h2 h'

theorem isFF7_actK (h2 : (2 : K) ≠ 0) (g : spinGroup (quadOdd 3 F)) {x : W7 K}
    (hx : IsFF7 D x) : IsFF7 D (actK g x) := by
  refine ⟨by rw [quad_actK h2, hx.1], ?_⟩
  rw [hrm_actK]
  exact hx.2

theorem polar_vXi_vE2 : polar (quadOdd 3 K) (vXi D) (vE2 D) = 0 := by
  simp [vXi, vE2, polar_mk7]

theorem polar_vXi_vE3 : polar (quadOdd 3 K) (vXi D) (vE3 D) = 0 := by
  simp [vXi, vE3, polar_mk7]

theorem polar_vE2_vE3 : polar (quadOdd 3 K) (vE2 D) (vE3 D) = 0 := by
  simp only [vE2, vE3, polar_mk7]
  ring

end CFSG.ClassicalInvolution.PhanB3.S
