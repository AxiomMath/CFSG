module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux7

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section StepD3

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {H : Subgroup (ModGL Tag.F4 L)}

theorem stepD_mem (E : Elts Fr H) {a ζ t : L} (ha : InE Fr a) (hζ : Fr ζ = ζ) (hζ0 : ζ ≠ 0)
    (ht : Fr t = t) (hv : vA a (Fr a) ∈ H) (hv' : vA (ζ * a) (ζ * Fr a) ∈ H) :
    pinnedX Tag.F4 L z0122 ((Fr a) ^ 2 * t - (ζ * Fr a) ^ 2 * (ζ⁻¹ * t)) *
      pinnedX Tag.F4 L v0100n (a ^ 2 * t - (ζ * a) ^ 2 * (ζ⁻¹ * t)) ∈ H := by
  have hFF : Fr (Fr a) = a := ha
  have hY : pinnedX Tag.F4 L negT t ∈ H := by rw [← negT_eq]; exact E.ethn t ht
  have hY' : pinnedX Tag.F4 L negT (ζ⁻¹ * t) ∈ H := by
    rw [← negT_eq]
    exact E.ethn _ (by rw [map_mul, map_inv₀, hζ, ht])
  have hc : (vA a (Fr a)) * pinnedX Tag.F4 L negT t * (vA a (Fr a))⁻¹ *
      (pinnedX Tag.F4 L negT t)⁻¹ ∈ H := mul_mem (mul_mem (mul_mem hv hY) (inv_mem hv)) (inv_mem hY)
  have hc' : (vA (ζ * a) (ζ * Fr a)) * pinnedX Tag.F4 L negT (ζ⁻¹ * t) *
      (vA (ζ * a) (ζ * Fr a))⁻¹ * (pinnedX Tag.F4 L negT (ζ⁻¹ * t))⁻¹ ∈ H :=
    mul_mem (mul_mem (mul_mem hv' hY') (inv_mem hv')) (inv_mem hY')
  have e1 := comm_vY a (Fr a) t
  have e2 := comm_vY (ζ * a) (ζ * Fr a) (ζ⁻¹ * t)
  have ex : ζ * Fr a * (ζ⁻¹ * t) = Fr a * t := by field_simp
  have ew : ζ * a * (ζ⁻¹ * t) = a * t := by field_simp
  unfold vA at hc hc'
  rw [e1] at hc
  rw [e2, ex, ew] at hc'
  have hcc := mul_mem hc (inv_mem hc')
  rw [five_cancel] at hcc
  have hP : pinnedX Tag.F4 L g5 (a * Fr a * t - ζ * a * (ζ * Fr a) * (ζ⁻¹ * t)) ∈ H := by
    refine E.eg5 _ ?_
    simp only [map_sub, map_mul, map_inv₀, hζ, ht, hFF]
    ring
  have := mul_mem (inv_mem hP) hcc
  convert this using 1
  group

theorem pA3_deg : pA3 0 = 1 := by decide
theorem pA3_mem_Deg1 : pA3 ∈ Deg1 Tag.F4 := ⟨mem_rootFinset.1 (by decide +kernel), pA3_deg⟩
theorem rA3_mem_Deg1 : rA3 ∈ Deg1 Tag.F4 := ⟨mem_rootFinset.1 rA3_root, rA3_deg⟩

variable (AD : ActData L)

theorem a1_cast_zero {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ rootFinset Tag.F4) (hγ0 : γ 0 = 0)
    (hμ : μ ∈ Deg1 Tag.F4) (h : γ + μ ∉ rootFinset Tag.F4) : (AD.a1 γ μ : L) = 0 := by
  rw [(AD.adm1 γ hγ hγ0 μ (mem_deg1Roots hμ)).2 h]
  simp

theorem a1_cast_one {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ rootFinset Tag.F4) (hγ0 : γ 0 = 0)
    (hμ : μ ∈ Deg1 Tag.F4) (h1 : γ + μ ∈ rootFinset Tag.F4) (h2 : μ - γ ∉ rootFinset Tag.F4) :
    (AD.a1 γ μ : L) = 1 := by
  have := (AD.adm1 γ hγ hγ0 μ (mem_deg1Roots hμ)).1 h1
  rw [if_neg h2] at this
  exact cast_one_of_abs this

theorem a2_cast_zero {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ rootFinset Tag.F4) (hγ0 : γ 0 = 0)
    (hμ : μ ∈ Deg1 Tag.F4) (h : 2 • γ + μ ∉ rootFinset Tag.F4) : (AD.a2 γ μ : L) = 0 := by
  rw [(AD.adm2 γ hγ hγ0 μ (mem_deg1Roots hμ)).2 h]
  simp

theorem z0122_deg : z0122 0 = 0 := by decide
theorem v0100n_deg : v0100n 0 = 0 := by decide

theorem A_v_S (Fr : L →+* L) (t b₀ : L) :
    actFun AD.a1 AD.a2 v0100n t (fv Fr rS b₀) = fv Fr rS b₀ + Pi.single pA3 (t * Fr b₀) := by
  have e1 : (AD.a1 v0100n rS : L) = 0 :=
    a1_cast_zero AD v0100n_root v0100n_deg rS_mem_Deg1 (by decide +kernel)
  have e2 : (AD.a2 v0100n rS : L) = 0 :=
    a2_cast_zero AD v0100n_root v0100n_deg rS_mem_Deg1 (by decide +kernel)
  have e3 : (AD.a1 v0100n pS : L) = 1 :=
    a1_cast_one AD v0100n_root v0100n_deg pS_mem_Deg1 (by decide +kernel) (by decide +kernel)
  have e4 : (AD.a2 v0100n pS : L) = 0 :=
    a2_cast_zero AD v0100n_root v0100n_deg pS_mem_Deg1 (by decide +kernel)
  have e5 : pS + v0100n = pA3 := by decide
  unfold fv
  rw [w_rS, ActionAux.actFun_add, ActionAux.actFun_single, ActionAux.actFun_single, e1, e2, e3, e4,
    e5]
  simp only [mul_zero, zero_mul, Pi.single_zero, add_zero, mul_one, one_mul]
  abel

theorem A_z_S (Fr : L →+* L) (t b₀ e : L) :
    actFun AD.a1 AD.a2 z0122 t (fv Fr rS b₀ + Pi.single pA3 e) =
      fv Fr rS b₀ + Pi.single pA3 e + Pi.single rA3 (t * b₀) := by
  have e1 : (AD.a1 z0122 rS : L) = 1 :=
    a1_cast_one AD z0122_root z0122_deg rS_mem_Deg1 (by decide +kernel) (by decide +kernel)
  have e2 : (AD.a2 z0122 rS : L) = 0 :=
    a2_cast_zero AD z0122_root z0122_deg rS_mem_Deg1 (by decide +kernel)
  have e3 : (AD.a1 z0122 pS : L) = 0 :=
    a1_cast_zero AD z0122_root z0122_deg pS_mem_Deg1 (by decide +kernel)
  have e4 : (AD.a2 z0122 pS : L) = 0 :=
    a2_cast_zero AD z0122_root z0122_deg pS_mem_Deg1 (by decide +kernel)
  have e5 : (AD.a1 z0122 pA3 : L) = 0 :=
    a1_cast_zero AD z0122_root z0122_deg pA3_mem_Deg1 (by decide +kernel)
  have e6 : (AD.a2 z0122 pA3 : L) = 0 :=
    a2_cast_zero AD z0122_root z0122_deg pA3_mem_Deg1 (by decide +kernel)
  have e7 : rS + z0122 = rA3 := by decide
  unfold fv
  rw [w_rS, ActionAux.actFun_add, ActionAux.actFun_add, ActionAux.actFun_single,
    ActionAux.actFun_single, ActionAux.actFun_single, e1, e2, e3, e4, e5, e6, e7]
  simp only [mul_zero, zero_mul, Pi.single_zero, add_zero, mul_one, one_mul]
  abel

end StepD3

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
