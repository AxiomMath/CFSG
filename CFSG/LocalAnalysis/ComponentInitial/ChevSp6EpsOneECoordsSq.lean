module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneECoordsIdent

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "𝔽" => Fin 3 → ZMod 2

variable {G : Type} [Group G]

@[expose] def cE (Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) : G → M₃ :=
  Function.invFun (Phi Jh cV)

@[expose] def pv (Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) (x : 𝔽) : M₃ :=
  cE Jh cV (lift Jh cV (0, x) * lift Jh cV (0, x))

namespace ECBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {C E Jh : Subgroup G} {cV : G → 𝔽 × 𝔽}

theorem cE_Phi (h : ECBase τ lev z ν C E Jh cV) (B : M₃) : cE Jh cV (Phi Jh cV B) = B :=
  Function.leftInverse_invFun h.Phi_injective B

theorem Phi_cE (h : ECBase τ lev z ν C E Jh cV) {e : G} (he : e ∈ E) :
    Phi Jh cV (cE Jh cV e) = e :=
  Function.invFun_eq (h.Phi_surj he)

theorem cE_mul (h : ECBase τ lev z ν C E Jh cV) {e e' : G} (he : e ∈ E) (he' : e' ∈ E) :
    cE Jh cV (e * e') = cE Jh cV e + cE Jh cV e' := by
  obtain ⟨B, rfl⟩ := h.Phi_surj he
  obtain ⟨B', rfl⟩ := h.Phi_surj he'
  rw [← h.Phi_add, h.cE_Phi, h.cE_Phi, h.cE_Phi]

theorem cE_lev (h : ECBase τ lev z ν C E Jh cV) (g : GL (Fin 3) (ZMod 2)) {e : G} (he : e ∈ E) :
    cE Jh cV (lev g * e * (lev g)⁻¹) = (g : M₃) * cE Jh cV e * (g : M₃)ᵀ := by
  obtain ⟨B, rfl⟩ := h.Phi_surj he
  rw [h.Phi_lev, h.cE_Phi, h.cE_Phi]

theorem cE_sqS (h : ECBase τ lev z ν C E Jh cV) (v : 𝔽) :
    cE Jh cV (τ (Multiplicative.ofAdd (sqS v))) = vecMulVec v v := by
  rw [← h.Phi_sq, h.cE_Phi]

theorem cE_bf (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    cE Jh cV (bf Jh cV (w, 0) (0, x)) = vecMulVec w x := by
  rw [← h.Phi_vecMulVec, h.cE_Phi]

theorem sq_eq_of_cV (h : ECBase τ lev z ν C E Jh cV) {b b' : G} (hb : b ∈ Jh) (hb' : b' ∈ Jh)
    (hbb' : cV b = cV b') : b * b = b' * b' := by
  have he := h.mem_E_of_cV_eq hb hb' hbb'
  have hb'' : b' = b * (b⁻¹ * b') := by rw [mul_inv_cancel_left]
  set e := b⁻¹ * b'
  have hc : e * b = b * e := (h.E_cent b hb e he).symm
  rw [hb'']
  calc b * b = b * b * (e * e) := by rw [h.E_sq e he, mul_one]
    _ = b * (b * e) * e := by group
    _ = b * (e * b) * e := by rw [hc]
    _ = b * e * (b * e) := by group

theorem pv_eq (h : ECBase τ lev z ν C E Jh cV) {b : G} {x : 𝔽} (hb : b ∈ Jh)
    (hcv : cV b = (0, x)) : cE Jh cV (b * b) = pv Jh cV x := by
  rw [pv, h.sq_eq_of_cV hb (h.lift_mem _) (by rw [hcv, h.cV_lift])]

theorem pv_lev (h : ECBase τ lev z ν C E Jh cV) (g : GL (Fin 3) (ZMod 2)) (x : 𝔽) :
    pv Jh cV ((g : M₃) *ᵥ x) = (g : M₃) * pv Jh cV x * (g : M₃)ᵀ := by
  have hb := h.lift_mem (0, x)
  set b := lift Jh cV (0, x) with hb_def
  have hm : lev g * b * (lev g)⁻¹ ∈ Jh := (mem_set_normalizer_iff.1 (h.vc.lev_mem g) b).1 hb
  have hcv : cV (lev g * b * (lev g)⁻¹) = (0, (g : M₃) *ᵥ x) := by
    rw [h.vc.lev_act g b hb, h.cV_lift, mulVec_zero]
  have hsq : lev g * b * (lev g)⁻¹ * (lev g * b * (lev g)⁻¹) = lev g * (b * b) * (lev g)⁻¹ := by
    group
  rw [← h.pv_eq hm hcv, hsq, h.cE_lev g (h.sq_mem_E hb)]
  rfl

theorem pv_zero (h : ECBase τ lev z ν C E Jh cV) : pv Jh cV 0 = 0 := by
  have h1 := h.pv_eq (one_mem Jh) h.cV_one
  rw [mul_one, ← h.Phi_zero, h.cE_Phi] at h1
  exact h1.symm

theorem pv_e1 (h : ECBase τ lev z ν C E Jh cV) :
    pv Jh cV (uv 0) = 0 ∨ pv Jh cV (uv 0) = vecMulVec ![1, 0, 0] ![1, 0, 0] := by
  have hfix : ∀ g : GL (Fin 3) (ZMod 2), (g : M₃) *ᵥ uv 0 = uv 0 →
      (g : M₃) * pv Jh cV (uv 0) * (g : M₃)ᵀ = pv Jh cV (uv 0) := fun g hg => by
    rw [← h.pv_lev, hg]
  exact fix_stab_one _ (hfix _ glTransTwoOne_uv) (hfix _ glTransThreeOne_uv)
    (hfix _ glTransThreeTwo_uv) (hfix _ glSwapTwoThree_uv)

theorem exists_u (h : ECBase τ lev z ν C E Jh cV) :
    ∃ u : Bool, ∀ x, pv Jh cV x = if u then vecMulVec x x else 0 := by
  rcases h.pv_e1 with h0 | h0
  · refine ⟨false, fun x => ?_⟩
    rw [ite_eq_right Bool.false_ne_true]
    by_cases hx : x = 0
    · rw [hx, h.pv_zero]
    · obtain ⟨g, hg⟩ := exists_gl_e1 hx
      rw [← hg, h.pv_lev, h0, Matrix.mul_zero, Matrix.zero_mul]
  · refine ⟨true, fun x => ?_⟩
    rw [ite_eq_left rfl]
    by_cases hx : x = 0
    · rw [hx, h.pv_zero, zero_vecMulVec]
    · obtain ⟨g, hg⟩ := exists_gl_e1 hx
      rw [← hg, h.pv_lev, h0, ← uv_zero, congr_vecMulVec]

theorem exists_ecoords (h : ECBase τ lev z ν C E Jh cV) :
    ∃ (u : Bool) (cE' : G → M₃), EpsOneECoords Jh E cV u cE' := by
  obtain ⟨u, hu⟩ := h.exists_u
  refine ⟨u, cE Jh cV, ⟨fun e he e' he' => h.cE_mul he he', fun e he he0 => ?_,
    fun B => ⟨Phi Jh cV B, h.Phi_mem B, h.cE_Phi B⟩, fun x hx => ?_⟩⟩
  · rw [← h.Phi_cE he, he0, h.Phi_zero]
  · obtain ⟨a, ha, haw⟩ := h.δ_surj (cV x).1
    have haJ := h.C_Jh ha
    have hb := h.lift_mem (0, (cV x).2)
    set b := lift Jh cV (0, (cV x).2) with hb_def
    have hab : cV (a * b) = cV x := by
      rw [h.vc.mul a haJ b hb, h.cV_C ha, haw, h.cV_lift]
      ext <;> simp
    have hxx : x * x = a * a * (b * b) * cm b a := by
      rw [← h.sq_mul haJ hb, h.sq_eq_of_cV hx (mul_mem haJ hb) hab.symm]
    have hcm : cm b a = bf Jh cV ((cV x).1, 0) (0, (cV x).2) := by
      rw [h.cm_eq_bf hb haJ, h.cV_lift, h.cV_C ha, haw, h.bf_comm]
    rw [hxx, h.cE_mul (mul_mem (h.sq_mem_E haJ) (h.sq_mem_E hb)) (h.cm_mem_E hb haJ),
      h.cE_mul (h.sq_mem_E haJ) (h.sq_mem_E hb), h.C_sq a ha, haw, h.cE_sqS, hcm, h.cE_bf,
      h.pv_eq hb (h.cV_lift _), hu]
    abel

end ECBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords
