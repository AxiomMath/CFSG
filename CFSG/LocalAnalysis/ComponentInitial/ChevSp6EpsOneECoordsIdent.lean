module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneECoordsPhi

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "𝔽" => Fin 3 → ZMod 2

variable {G : Type} [Group G]

theorem card_M3 : Nat.card M₃ = 512 := by
  simp [Nat.card_eq_fintype_card, Matrix]

theorem sqS_zero : sqS (0 : 𝔽) = 0 :=
  Subtype.ext (zero_vecMulVec _)

namespace ECBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {C E Jh : Subgroup G} {cV : G → 𝔽 × 𝔽}

theorem τ_eq_one (h : ECBase τ lev z ν C E Jh cV) {S : 𝕊}
    (hS : τ (Multiplicative.ofAdd S) = 1) : S = 0 := by
  have h1 : τ (Multiplicative.ofAdd S) = τ (Multiplicative.ofAdd 0) := by
    rw [hS, ofAdd_zero, map_one]
  exact Multiplicative.ofAdd.injective (h.τ_inj h1)

theorem Phi_e1 (h : ECBase τ lev z ν C E Jh cV) :
    Phi Jh cV (vecMulVec (uv 0) (uv 0)) = τ (Multiplicative.ofAdd (sqS (uv 0))) := by
  obtain ⟨c, hc, hcx⟩ := h.δ_surj (uv 0)
  have hcJ := h.C_Jh hc
  have hy : lift Jh cV (0, uv 0) ∈ Jh := h.lift_mem _
  set y := lift Jh cV (0, uv 0) with hy_def
  have hzy : cV (y * c) = cV (z * y * z⁻¹) := by
    rw [h.vc.z_act y hy, h.cV_lift, h.vc.mul y hy c hcJ, h.cV_lift, h.cV_C hc, hcx]
    ext <;> simp
  have he' := h.mem_E_of_cV_eq (mul_mem hy hcJ) (h.z_Jh y hy) hzy
  set e' := (y * c)⁻¹ * (z * y * z⁻¹) with he'_def
  have hzy' : z * y * z⁻¹ = y * c * e' := by rw [he'_def, mul_inv_cancel_left]
  have hce : e' * (y * c) = y * c * e' := (h.E_cent _ (mul_mem hy hcJ) _ he').symm
  have hsq : z * (y * y) * z⁻¹ = y * y * (c * c) * cm c y := by
    calc z * (y * y) * z⁻¹ = (z * y * z⁻¹) * (z * y * z⁻¹) := by group
      _ = y * c * (e' * (y * c)) * e' := by rw [hzy']; group
      _ = y * c * (y * c) * (e' * e') := by rw [hce]; group
      _ = y * y * (c * c) * cm c y := by rw [h.E_sq e' he', mul_one, h.sq_mul hy hcJ]
  have hcc : c * c = τ (Multiplicative.ofAdd (sqS (uv 0))) := by rw [h.C_sq c hc, hcx]
  have hcy : cm c y = Phi Jh cV (vecMulVec (uv 0) (uv 0)) := by
    rw [h.Phi_vecMulVec, h.cm_eq_bf hcJ hy, h.cV_C hc, hcx, h.cV_lift]
  have hyy := h.sq_mem_E hy
  obtain ⟨B, hBd, hB⟩ := h.z_E _ hyy
  set P := Phi Jh cV (vecMulVec (uv 0) (uv 0)) with hP_def
  have hPE : P ∈ E := h.Phi_mem _
  have h1 : τ (Multiplicative.ofAdd B) = c * c * P := by
    rw [← hB, hsq, hcy]
    have hc2 : y * y * (c * c * P) = c * c * P * (y * y) :=
      h.E_comm hyy (mul_mem (h.sq_mem_E hcJ) hPE)
    calc y * y * (c * c) * P * (y * y)⁻¹ = y * y * (c * c * P) * (y * y)⁻¹ := by group
      _ = c * c * P := by rw [hc2]; group
  have hP : P = τ (Multiplicative.ofAdd (-sqS (uv 0) + B)) := by
    rw [ofAdd_add, map_mul, ofAdd_neg, map_inv, h1, ← hcc]
    group
  set S₀ : 𝕊 := -sqS (uv 0) + B with hS₀
  have hδ : (S₀ : M₃) 0 0 = 1 := by
    have hB0 : (B : M₃) 0 0 = 0 := congrFun hBd 0
    change -(uv 0 0 * uv 0 0) + (B : M₃) 0 0 = 1
    rw [hB0]
    decide
  have hfix : ∀ g : GL (Fin 3) (ZMod 2), (g : M₃) *ᵥ uv 0 = uv 0 →
      (g : M₃) * (S₀ : M₃) * (g : M₃)ᵀ = S₀ := by
    intro g hg
    have h2 : lev g * P * (lev g)⁻¹ = P := by
      rw [hP_def, h.Phi_lev, congr_vecMulVec, hg]
    rw [hP, h.lev_τ] at h2
    have h3 : symThreeCongr g S₀ = S₀ := Multiplicative.ofAdd.injective (h.τ_inj h2)
    rw [← coe_symThreeCongr, h3]
  rcases fix_stab_one (S₀ : M₃) (hfix _ glTransTwoOne_uv) (hfix _ glTransThreeOne_uv)
    (hfix _ glTransThreeTwo_uv) (hfix _ glSwapTwoThree_uv) with h0 | h0
  · rw [h0] at hδ
    exact absurd hδ (by decide)
  · have hS : S₀ = sqS (uv 0) := Subtype.ext (by rw [h0, coe_sqS, uv_zero])
    rw [hP, hS]

theorem Phi_sq (h : ECBase τ lev z ν C E Jh cV) (v : 𝔽) :
    Phi Jh cV (vecMulVec v v) = τ (Multiplicative.ofAdd (sqS v)) := by
  by_cases hv : v = 0
  · subst hv
    rw [zero_vecMulVec, h.Phi_zero, sqS_zero, ofAdd_zero, map_one]
  · obtain ⟨g, hg⟩ := exists_gl_e1 hv
    have h1 : vecMulVec v v = (g : M₃) * vecMulVec (uv 0) (uv 0) * (g : M₃)ᵀ := by
      rw [congr_vecMulVec, hg]
    have h2 : sqS v = symThreeCongr g (sqS (uv 0)) :=
      Subtype.ext (by rw [coe_symThreeCongr, coe_sqS, coe_sqS, h1])
    rw [h1, ← h.Phi_lev, h.Phi_e1, h.lev_τ, h2]
    rfl

theorem Phi_polar (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    Phi Jh cV (symThreePolarSym w x : M₃) =
      τ (Multiplicative.ofAdd (symThreePolarSym w x)) := by
  have hS : sqS (w + x) + sqS w + sqS x = symThreePolarSym w x := Subtype.ext (by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add, coe_sqS, coe_sqS, coe_sqS]
    exact (symThreePolar_eq w x).symm)
  change Phi Jh cV (symThreePolar w x) = _
  rw [symThreePolar_eq, h.Phi_add, h.Phi_add, h.Phi_sq, h.Phi_sq, h.Phi_sq, ← map_mul,
    ← map_mul, ← ofAdd_add, ← ofAdd_add, hS]

theorem Phi_sqS (h : ECBase τ lev z ν C E Jh cV) (v : 𝔽) :
    Phi Jh cV (sqS v : M₃) = τ (Multiplicative.ofAdd (sqS v)) :=
  h.Phi_sq v

theorem Phi_sym (h : ECBase τ lev z ν C E Jh cV) (S : 𝕊) :
    Phi Jh cV (S : M₃) = τ (Multiplicative.ofAdd S) := by
  conv_lhs => rw [sym_eq_sum S]
  conv_rhs => rw [sym_eq_sum S]
  simp only [AddSubgroup.coe_add, h.Phi_add, ofAdd_add, map_mul, h.Phi_polar, h.Phi_sqS]

theorem Phi_eq_one (h : ECBase τ lev z ν C E Jh cV) {B : M₃} (hB : Phi Jh cV B = 1) :
    B = 0 := by
  have h1 := h.Phi_z B
  rw [hB, mul_one, mul_inv_cancel, mul_one] at h1
  have h2 : symPart B = 0 := h.τ_eq_one h1.symm
  have h3 : B + Bᵀ = 0 := congrArg Subtype.val h2
  have hsym : Bᵀ = B := by
    calc Bᵀ = Bᵀ + (B + B) := by rw [two_eq_zero_mat, add_zero]
      _ = B + (B + Bᵀ) := by abel
      _ = B := by rw [h3, add_zero]
  have h4 := h.Phi_sym ⟨B, hsym⟩
  change Phi Jh cV B = _ at h4
  rw [hB] at h4
  exact congrArg Subtype.val (h.τ_eq_one h4.symm)

theorem Phi_injective (h : ECBase τ lev z ν C E Jh cV) : Function.Injective (Phi Jh cV) :=
  fun B B' hBB' => by
    have h1 := h.Phi_sub B B'
    rw [hBB', mul_inv_cancel] at h1
    exact sub_eq_zero.1 (h.Phi_eq_one h1)

theorem Phi_surj (h : ECBase τ lev z ν C E Jh cV) {e : G} (he : e ∈ E) :
    ∃ B, Phi Jh cV B = e := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card_E]; norm_num)
  let f : M₃ → E := fun B => ⟨Phi Jh cV B, h.Phi_mem B⟩
  have hf : Function.Injective f := fun B B' hBB' =>
    h.Phi_injective (congrArg Subtype.val hBB')
  have hcard : Nat.card E ≤ Nat.card M₃ := by rw [h.card_E, card_M3]
  obtain ⟨B, hB⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨e, he⟩
  exact ⟨B, congrArg Subtype.val hB⟩

end ECBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords
