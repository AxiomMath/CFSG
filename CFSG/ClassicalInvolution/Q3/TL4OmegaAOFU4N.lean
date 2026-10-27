module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Gram
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U4

open Matrix CFSG.ClassicalInvolution.Q3.Q3MFOU4 CFSG.ClassicalInvolution.Q3.Q3PP

section Herm

@[expose] noncomputable def vstar (x : Fin 4 → F9) : Fin 4 → F9 := fun i => σ9 (x i)

@[expose] noncomputable def hf (x y : Fin 4 → F9) : F9 := vstar x ⬝ᵥ y

theorem hf_add_right (x y y' : Fin 4 → F9) : hf x (y + y') = hf x y + hf x y' :=
  dotProduct_add _ _ _

theorem hf_sub_right (x y y' : Fin 4 → F9) : hf x (y - y') = hf x y - hf x y' :=
  dotProduct_sub _ _ _

theorem hf_smul_right (x y : Fin 4 → F9) (c : F9) : hf x (c • y) = c * hf x y := by
  rw [hf, dotProduct_smul, smul_eq_mul]
  rfl

theorem vstar_add (x y : Fin 4 → F9) : vstar (x + y) = vstar x + vstar y := by
  funext i
  simp [vstar]

theorem vstar_smul (x : Fin 4 → F9) (c : F9) : vstar (c • x) = σ9 c • vstar x := by
  funext i
  simp [vstar]

theorem vstar_neg (x : Fin 4 → F9) : vstar (-x) = -vstar x := by
  funext i
  simp [vstar]

theorem vstar_vstar (x : Fin 4 → F9) : vstar (vstar x) = x := by
  funext i
  exact σ9_σ9 (x i)

theorem hf_add_left (x x' y : Fin 4 → F9) : hf (x + x') y = hf x y + hf x' y := by
  rw [hf, vstar_add, add_dotProduct]
  rfl

theorem hf_smul_left (x y : Fin 4 → F9) (c : F9) : hf (c • x) y = σ9 c * hf x y := by
  rw [hf, vstar_smul, smul_dotProduct, smul_eq_mul]
  rfl

theorem σ9_dotProduct (a b : Fin 4 → F9) : σ9 (a ⬝ᵥ b) = vstar a ⬝ᵥ vstar b := by
  simp [dotProduct, vstar, map_sum]

theorem hf_swap (x y : Fin 4 → F9) : hf y x = σ9 (hf x y) := by
  rw [hf, hf, σ9_dotProduct, vstar_vstar, dotProduct_comm]

theorem σ9_hf_self (x : Fin 4 → F9) : σ9 (hf x x) = hf x x := (hf_swap x x).symm

@[expose] noncomputable def hfL (a : Fin 4 → F9) : (Fin 4 → F9) →ₗ[F9] F9 where
  toFun y := hf a y
  map_add' := hf_add_right a
  map_smul' c y := by rw [hf_smul_right, smul_eq_mul, RingHom.id_apply]

theorem hf_single : hf (Pi.single 0 1) (Pi.single 0 1) = 1 := by
  simp [hf, vstar, dotProduct, Pi.single_apply]

theorem hf_single_right (x : Fin 4 → F9) (k : Fin 4) : hf x (Pi.single k 1) = σ9 (x k) := by
  rw [hf, dotProduct_single, mul_one]
  rfl

end Herm

section Tau

@[expose] noncomputable def tau (G : Matrix (Fin 4) (Fin 4) F9) (x : Fin 4 → F9) :
    Fin 4 → F9 := -((G.map σ9) *ᵥ vstar x)

@[expose] noncomputable def bf (G : Matrix (Fin 4) (Fin 4) F9) (x y : Fin 4 → F9) : F9 :=
  x ⬝ᵥ (G *ᵥ y)

variable {G : Matrix (Fin 4) (Fin 4) F9}

theorem vstar_mulVec (M : Matrix (Fin 4) (Fin 4) F9) (x : Fin 4 → F9) :
    vstar (M *ᵥ x) = M.map σ9 *ᵥ vstar x := by
  funext i
  simp [vstar, mulVec, dotProduct, map_sum]

theorem map_map_σ9 (M : Matrix (Fin 4) (Fin 4) F9) : (M.map σ9).map σ9 = M := by
  ext i j
  exact σ9_σ9 _

theorem vstar_tau (x : Fin 4 → F9) : vstar (tau G x) = -(G *ᵥ x) := by
  rw [tau, vstar_neg, vstar_mulVec, map_map_σ9, vstar_vstar]

theorem hf_tau_right (x y : Fin 4 → F9) : hf x (tau G y) = -σ9 (bf G x y) := by
  rw [hf, tau, dotProduct_neg, bf, σ9_dotProduct, vstar_mulVec]

theorem bf_skew (halt : Gᵀ = -G) (x y : Fin 4 → F9) : bf G x y = -bf G y x := by
  rw [bf, bf, dotProduct_mulVec, ← mulVec_transpose, halt, neg_mulVec, neg_dotProduct,
    dotProduct_comm]

theorem bf_self (halt : Gᵀ = -G) (x : Fin 4 → F9) : bf G x x = 0 := by
  have h := bf_skew halt x x
  have h3 : (2 : F9) * bf G x x = 0 := by linear_combination h
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero_F9

theorem map_transpose_eq (halt : Gᵀ = -G) : (G.map σ9)ᵀ = -(G.map σ9) := by
  rw [← transpose_map, halt, Matrix.map_neg _ (map_neg σ9)]

theorem mul_map_eq (hgu : (G.map σ9)ᵀ * G = 1) (halt : Gᵀ = -G) : G * G.map σ9 = -1 := by
  have h1 : (-(G.map σ9)) * G = 1 := by rw [← map_transpose_eq halt]; exact hgu
  have h2 := mul_eq_one_comm.mp h1
  rw [Matrix.mul_neg] at h2
  rw [← neg_neg (G * G.map σ9), h2]

theorem bf_tau_self (hgu : (G.map σ9)ᵀ * G = 1) (halt : Gᵀ = -G) (x : Fin 4 → F9) :
    bf G x (tau G x) = hf x x := by
  rw [bf, tau, mulVec_neg, mulVec_mulVec, mul_map_eq hgu halt, neg_mulVec, one_mulVec, neg_neg,
    hf, dotProduct_comm]

theorem hf_tau_left (halt : Gᵀ = -G) (e x : Fin 4 → F9) : hf (tau G e) x = bf G e x := by
  rw [hf, vstar_tau, neg_dotProduct, bf, dotProduct_comm (G *ᵥ e) x, dotProduct_mulVec,
    ← mulVec_transpose, halt, neg_mulVec, neg_dotProduct, neg_neg, dotProduct_comm]

theorem bf_tau_left (hgu : (G.map σ9)ᵀ * G = 1) (e x : Fin 4 → F9) :
    bf G (tau G e) x = -hf e x := by
  rw [bf, tau, neg_dotProduct, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
    mulVec_mulVec, hgu, one_mulVec, hf, dotProduct_comm]

theorem hf_tau_tau (hgu : (G.map σ9)ᵀ * G = 1) (halt : Gᵀ = -G) (x : Fin 4 → F9) :
    hf (tau G x) (tau G x) = hf x x := by
  rw [hf_tau_left halt, bf_tau_self hgu halt]

theorem hf_tau_self (halt : Gᵀ = -G) (x : Fin 4 → F9) : hf x (tau G x) = 0 := by
  rw [hf_tau_right, bf_self halt, map_zero, neg_zero]

end Tau

section Unit

theorem exists_unit_of_orth {a b : Fin 4 → F9} (haa : hf a a = 1) (hbb : hf b b = 1)
    (hab : hf a b = 0) : ∃ v, hf a v = 0 ∧ hf b v = 0 ∧ hf v v = 1 := by
  classical
  have hba : hf b a = 0 := by rw [hf_swap, hab, map_zero]
  set p : (Fin 4 → F9) → (Fin 4 → F9) := fun z => z - hf a z • a - hf b z • b with hp
  have hpa : ∀ z, hf a (p z) = 0 := fun z => by
    simp only [hp, hf_sub_right, hf_smul_right, haa, hab]
    ring
  have hpb : ∀ z, hf b (p z) = 0 := fun z => by
    simp only [hp, hf_sub_right, hf_smul_right, hbb, hba]
    ring
  have hxp : ∀ x z, hf a x = 0 → hf b x = 0 → hf x (p z) = hf x z := fun x z hxa hxb => by
    have h1 : hf x a = 0 := by rw [hf_swap, hxa, map_zero]
    have h2 : hf x b = 0 := by rw [hf_swap, hxb, map_zero]
    simp only [hp, hf_sub_right, hf_smul_right, h1, h2]
    ring
  obtain ⟨x, hxa, hxb, hx0⟩ : ∃ x, hf a x = 0 ∧ hf b x = 0 ∧ x ≠ 0 := by
    set W := LinearMap.ker ((hfL a).prod (hfL b)) with hW
    have hWdim : 2 ≤ Module.finrank F9 W := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ((hfL a).prod (hfL b))
      have h3 : Module.finrank F9 (LinearMap.range ((hfL a).prod (hfL b))) ≤ 2 := by
        have := Submodule.finrank_le (LinearMap.range ((hfL a).prod (hfL b)))
        simpa using this
      rw [Module.finrank_fin_fun, ← hW] at h1
      omega
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F9) (by omega)
    obtain ⟨⟨x, hxW⟩, hx0⟩ := exists_ne (0 : W)
    have hxW' := hxW
    rw [hW, LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hxW'
    exact ⟨x, hxW'.1, hxW'.2, fun h => hx0 (Subtype.ext h)⟩
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (funext hc)
  set y := p (Pi.single k 1) with hy
  have hya := hpa (Pi.single k 1)
  have hyb := hpb (Pi.single k 1)
  have hxy : hf x y ≠ 0 := by
    rw [hy, hxp x _ hxa hxb, hf_single_right]
    intro h
    apply hk
    have := congrArg σ9 h
    rwa [σ9_σ9, map_zero] at this
  obtain ⟨w, hwa, hwb, hw⟩ : ∃ w, hf a w = 0 ∧ hf b w = 0 ∧ hf w w ≠ 0 := by
    by_cases hxx : hf x x = 0
    · by_cases hyy : hf y y = 0
      · set d := hf x y with hd
        have hyx : hf y x = σ9 d := by rw [hd, hf_swap]
        have hσd : σ9 d ≠ 0 := (map_ne_zero σ9).mpr hxy
        refine ⟨x + d⁻¹ • y, ?_, ?_, ?_⟩
        · rw [hf_add_right, hf_smul_right, hxa, hya, mul_zero, add_zero]
        · rw [hf_add_right, hf_smul_right, hxb, hyb, mul_zero, add_zero]
        · have e : hf (x + d⁻¹ • y) (x + d⁻¹ • y) = 2 := by
            rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_right,
              hf_smul_right, hf_smul_left, hxx, hyy, hyx, ← hd, map_inv₀]
            field_simp
            ring
          rw [e]
          exact two_ne_zero_F9
      · exact ⟨y, hya, hyb, hyy⟩
    · exact ⟨x, hxa, hxb, hxx⟩
  obtain ⟨ζ, hζ⟩ := exists_zeta
  rcases eq_of_σ9_fixed (σ9_hf_self w) with h0 | h1 | h1
  · exact absurd h0 hw
  · exact ⟨w, hwa, hwb, h1⟩
  · refine ⟨ζ • w, ?_, ?_, ?_⟩
    · rw [hf_smul_right, hwa, mul_zero]
    · rw [hf_smul_right, hwb, mul_zero]
    · rw [hf_smul_left, hf_smul_right, h1, ← mul_assoc, hζ]
      ring

end Unit

end CFSG.ClassicalInvolution.Q3.TL4.U4
