module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneECoordsBase

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "𝔽" => Fin 3 → ZMod 2

variable {G : Type} [Group G]

@[expose] def Phi (Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) (B : M₃) : G :=
  bf Jh cV (col B 0, 0) (0, uv 0) * bf Jh cV (col B 1, 0) (0, uv 1) *
    bf Jh cV (col B 2, 0) (0, uv 2)

@[expose] def gAct (g : GL (Fin 3) (ZMod 2)) (p : 𝔽 × 𝔽) : 𝔽 × 𝔽 :=
  ((g : M₃) *ᵥ p.1, (g : M₃) *ᵥ p.2)

theorem gAct_fst (g : GL (Fin 3) (ZMod 2)) (w : 𝔽) : gAct g (w, 0) = ((g : M₃) *ᵥ w, 0) := by
  simp [gAct]

theorem gAct_snd (g : GL (Fin 3) (ZMod 2)) (x : 𝔽) : gAct g (0, x) = (0, (g : M₃) *ᵥ x) := by
  simp [gAct]

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

namespace ECBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {C E Jh : Subgroup G} {cV : G → 𝔽 × 𝔽}

theorem rearr (h : ECBase τ lev z ν C E Jh cV) {a b c a' b' c' : G} (ha' : a' ∈ E)
    (hb : b ∈ E) (hb' : b' ∈ E) (hc : c ∈ E) :
    a * a' * (b * b') * (c * c') = a * b * c * (a' * b' * c') := by
  have h1 : a' * b = b * a' := h.E_comm ha' hb
  have h2 : a' * b' * c = c * (a' * b') := h.E_comm (mul_mem ha' hb') hc
  calc a * a' * (b * b') * (c * c') = a * (a' * b) * b' * (c * c') := by group
    _ = a * b * (a' * b' * c) * c' := by rw [h1]; group
    _ = a * b * c * (a' * b' * c') := by rw [h2]; group

theorem Phi_mem (h : ECBase τ lev z ν C E Jh cV) (B : M₃) : Phi Jh cV B ∈ E :=
  mul_mem (mul_mem (h.bf_mem _ _) (h.bf_mem _ _)) (h.bf_mem _ _)

theorem Phi_add (h : ECBase τ lev z ν C E Jh cV) (B B' : M₃) :
    Phi Jh cV (B + B') = Phi Jh cV B * Phi Jh cV B' := by
  have hcol : ∀ k, ((col (B + B') k, 0) : 𝔽 × 𝔽) = (col B k, 0) + (col B' k, 0) := fun k => by
    ext i <;> simp [col]
  simp only [Phi, hcol, h.bf_add_left]
  exact h.rearr (h.bf_mem _ _) (h.bf_mem _ _) (h.bf_mem _ _) (h.bf_mem _ _)

theorem Phi_zero (h : ECBase τ lev z ν C E Jh cV) : Phi Jh cV 0 = 1 := by
  have h1 := h.Phi_add 0 0
  rw [add_zero] at h1
  calc Phi Jh cV 0 = (Phi Jh cV 0)⁻¹ * (Phi Jh cV 0 * Phi Jh cV 0) := by group
    _ = 1 := by rw [← h1, inv_mul_cancel]

theorem Phi_sub (h : ECBase τ lev z ν C E Jh cV) (B B' : M₃) :
    Phi Jh cV (B - B') = Phi Jh cV B * (Phi Jh cV B')⁻¹ := by
  have h1 := h.Phi_add (B - B') B'
  rw [sub_add_cancel] at h1
  rw [h1, mul_inv_cancel_right]

theorem Phi_vecMulVec (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    Phi Jh cV (vecMulVec w x) = bf Jh cV (w, 0) (0, x) := by
  have hcol : ∀ k, col (vecMulVec w x) k = x k • w := fun k => by
    funext i
    simp [col, vecMulVec_apply, mul_comm]
  have hsc : ∀ (a : ZMod 2) (k : Fin 3),
      bf Jh cV (a • w, 0) (0, uv k) = bf Jh cV (w, 0) (0, a • uv k) := by
    intro a k
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul, zero_smul, show ((0 : 𝔽), (0 : 𝔽)) = 0 from rfl, h.bf_zero_left,
        h.bf_zero_right]
    · rw [one_smul, one_smul]
  have hx : x 0 • uv 0 + x 1 • uv 1 + x 2 • uv 2 = x := by
    funext i
    fin_cases i <;> simp [uv]
  have hsplit : ∀ a b : 𝔽, ((0 : 𝔽), a) + (0, b) = (0, a + b) := fun a b => by
    ext <;> simp
  rw [Phi, hcol, hcol, hcol, hsc, hsc, hsc, ← h.bf_add_right, ← h.bf_add_right, hsplit, hsplit,
    hx]

theorem conj_bf (h : ECBase τ lev z ν C E Jh cV) (g : GL (Fin 3) (ZMod 2)) (p q : 𝔽 × 𝔽) :
    lev g * bf Jh cV p q * (lev g)⁻¹ = bf Jh cV (gAct g p) (gAct g q) := by
  have hm : ∀ x ∈ Jh, lev g * x * (lev g)⁻¹ ∈ Jh := fun x hx =>
    (mem_set_normalizer_iff.1 (h.vc.lev_mem g) x).1 hx
  have hc : ∀ r, cV (lev g * lift Jh cV r * (lev g)⁻¹) = gAct g r := fun r => by
    rw [h.vc.lev_act g _ (h.lift_mem r), h.cV_lift]
    rfl
  rw [bf, conj_cm, h.cm_eq_bf (hm _ (h.lift_mem p)) (hm _ (h.lift_mem q)), hc, hc]

theorem congr_eq_sum (g : M₃) (B : M₃) : g * B * gᵀ =
    vecMulVec (g *ᵥ col B 0) (g *ᵥ uv 0) + vecMulVec (g *ᵥ col B 1) (g *ᵥ uv 1) +
      vecMulVec (g *ᵥ col B 2) (g *ᵥ uv 2) := by
  conv_lhs => rw [eq_sum_col B]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, congr_vecMulVec,
    congr_vecMulVec, congr_vecMulVec]

theorem Phi_lev (h : ECBase τ lev z ν C E Jh cV) (g : GL (Fin 3) (ZMod 2)) (B : M₃) :
    lev g * Phi Jh cV B * (lev g)⁻¹ = Phi Jh cV ((g : M₃) * B * (g : M₃)ᵀ) := by
  have hconj : ∀ a b c : G, lev g * (a * b * c) * (lev g)⁻¹ =
      lev g * a * (lev g)⁻¹ * (lev g * b * (lev g)⁻¹) * (lev g * c * (lev g)⁻¹) := by
    intros
    group
  rw [Phi, hconj, h.conj_bf, h.conj_bf, h.conj_bf, congr_eq_sum, h.Phi_add, h.Phi_add,
    h.Phi_vecMulVec, h.Phi_vecMulVec, h.Phi_vecMulVec, gAct_fst, gAct_fst, gAct_fst, gAct_snd,
    gAct_snd, gAct_snd]

theorem bf_W (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    bf Jh cV (w, 0) (x, 0) = τ (Multiplicative.ofAdd (symThreePolarSym w x)) := by
  obtain ⟨a, ha, haw⟩ := h.δ_surj w
  obtain ⟨c, hc, hcx⟩ := h.δ_surj x
  have e1 := h.cm_eq_bf (h.C_Jh ha) (h.C_Jh hc)
  rw [h.cV_C ha, h.cV_C hc, haw, hcx] at e1
  rw [← e1, cm, h.C_comm a ha c hc, haw, hcx]

theorem τ_polar_mem (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    τ (Multiplicative.ofAdd (symThreePolarSym w x)) ∈ E := by
  rw [← h.bf_W]
  exact h.bf_mem _ _

theorem z_bf (h : ECBase τ lev z ν C E Jh cV) (w x : 𝔽) :
    z * bf Jh cV (w, 0) (0, x) * z⁻¹ =
      τ (Multiplicative.ofAdd (symThreePolarSym w x)) * bf Jh cV (w, 0) (0, x) := by
  obtain ⟨a, ha, haw⟩ := h.δ_surj w
  have haJ := h.C_Jh ha
  have hb := h.lift_mem (0, x)
  have hza : cV (z * a * z⁻¹) = (w, 0) := by
    rw [h.vc.z_act a haJ, h.cV_C ha, haw, add_zero]
  have hzb : cV (z * lift Jh cV (0, x) * z⁻¹) = (x, 0) + (0, x) := by
    rw [h.vc.z_act _ hb, h.cV_lift]
    ext <;> simp
  have e1 : bf Jh cV (w, 0) (0, x) = cm a (lift Jh cV (0, x)) := by
    rw [h.cm_eq_bf haJ hb, h.cV_C ha, haw, h.cV_lift]
  rw [e1, conj_cm, h.cm_eq_bf (h.z_Jh _ haJ) (h.z_Jh _ hb), hza, hzb, h.bf_add_right, h.bf_W,
    ← e1]

theorem symPart_eq (B : M₃) : symPart B = symThreePolarSym (col B 0) (uv 0) +
    symThreePolarSym (col B 1) (uv 1) + symThreePolarSym (col B 2) (uv 2) := by
  apply Subtype.ext
  rw [coe_symPart, AddSubgroup.coe_add, AddSubgroup.coe_add]
  change B + Bᵀ = symThreePolar _ _ + symThreePolar _ _ + symThreePolar _ _
  conv_lhs => rw [eq_sum_col B]
  simp only [symThreePolar, transpose_add, transpose_vecMulVec]
  abel

theorem Phi_z (h : ECBase τ lev z ν C E Jh cV) (B : M₃) :
    z * Phi Jh cV B * z⁻¹ = τ (Multiplicative.ofAdd (symPart B)) * Phi Jh cV B := by
  have hconj : ∀ a b c : G, z * (a * b * c) * z⁻¹ =
      z * a * z⁻¹ * (z * b * z⁻¹) * (z * c * z⁻¹) := by
    intros
    group
  rw [Phi, hconj, h.z_bf, h.z_bf, h.z_bf, symPart_eq, ofAdd_add, ofAdd_add, map_mul, map_mul]
  exact h.rearr (h.bf_mem _ _) (h.τ_polar_mem _ _) (h.bf_mem _ _) (h.τ_polar_mem _ _)

end ECBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords
