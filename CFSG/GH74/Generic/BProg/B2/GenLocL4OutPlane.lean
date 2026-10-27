module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutNF
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutMix

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG Matrix
open scoped MatrixGroups


section PlaneSL2

variable {F : Type} [Field F]

@[expose] def e12 (a : F) : SL(2, F) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
@[expose] def e21 (a : F) : SL(2, F) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩
@[expose] def dgS (s : Fˣ) : SL(2, F) := ⟨!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)], by
  simp [Matrix.det_fin_two]⟩
@[expose] def hypS (h2 : (2 : F) ≠ 0) (γ σ : Fˣ) : SL(2, F) :=
  ⟨!![((σ : F) + ((σ⁻¹ : Fˣ) : F)) / 2, ((σ : F) - ((σ⁻¹ : Fˣ) : F)) / (2 * γ);
      (γ : F) ^ 2 * (((σ : F) - ((σ⁻¹ : Fˣ) : F)) / (2 * γ)), ((σ : F) + ((σ⁻¹ : Fˣ) : F)) / 2], by
    have hσ : (σ : F) * ((σ⁻¹ : Fˣ) : F) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hγ : (γ : F) ≠ 0 := γ.ne_zero
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    field_simp
    linear_combination 4 * hσ⟩

theorem coe_inv_fin_two (g : SL(2, F)) :
    ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
      -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem dgS_e12 (s : Fˣ) (a : F) : dgS s * e12 a * (dgS s)⁻¹ = e12 ((s : F) ^ 2 * a) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dgS, e12, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem key_identity (γ ρ : F) (hγ : γ ≠ 0) (hρ : ρ ≠ 0) (h4 : ρ ^ 4 ≠ 1) (h1 : ρ ^ 2 + 1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    let m : F → F := fun σ => (σ + σ⁻¹) / 2
    let y : F → F := fun σ => (σ - σ⁻¹) / (2 * γ)
    let H : F → Matrix (Fin 2) (Fin 2) F := fun σ => !![m σ, y σ; γ ^ 2 * y σ, m σ]
    let Hi : F → Matrix (Fin 2) (Fin 2) F := fun σ => !![m σ, -y σ; -(γ ^ 2 * y σ), m σ]
    let s : F := (ρ ^ 2 + 1) / (ρ ^ 2 - 1)
    let D : Matrix (Fin 2) (Fin 2) F := !![s, 0; 0, s⁻¹]
    let Di : Matrix (Fin 2) (Fin 2) F := !![s⁻¹, 0; 0, s]
    H ρ * (Hi (ρ ^ 2) * D * H (ρ ^ 2) * Di) * Hi ρ = !![-1, 4 * (ρ ^ 4 + 1) / (γ * (ρ ^ 4 - 1)); 0, -1] := by
  intro m y H Hi s D Di
  have hs1 : ρ ^ 2 - 1 ≠ 0 := by
    intro h; apply h4; linear_combination (ρ ^ 2 + 1) * h
  have hs2 : ρ ^ 4 - 1 ≠ 0 := sub_ne_zero.2 h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, Hi, D, Di, m, y, s, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring


theorem plane_unipotent (h2 : (2 : F) ≠ 0) (γ ρ : Fˣ) (h4 : (ρ : F) ^ 4 ≠ 1) (h1 : (ρ : F) ^ 2 + 1 ≠ 0)
    (H : Subgroup SL(2, F)) (hD : ∀ s : Fˣ, dgS s ∈ H) (hG : ∀ σ : Fˣ, hypS h2 γ σ ∈ H) :
    e12 (-2 * (4 * ((ρ : F) ^ 4 + 1) / ((γ : F) * ((ρ : F) ^ 4 - 1)))) ∈ H := by
  have hρ0 : (ρ : F) ≠ 0 := ρ.ne_zero
  have hs1 : (ρ : F) ^ 2 - 1 ≠ 0 := by
    intro h; apply h4; linear_combination ((ρ : F) ^ 2 + 1) * h
  set σ : Fˣ := ρ ^ 2 with hσ
  set s : Fˣ := Units.mk0 (((ρ : F) ^ 2 + 1) / ((ρ : F) ^ 2 - 1)) (div_ne_zero h1 hs1) with hs
  set g := hypS h2 γ σ with hg
  set G := hypS h2 γ ρ with hG'
  set v : SL(2, F) := G * (g⁻¹ * dgS s * g * (dgS s)⁻¹) * G⁻¹ with hv
  have hvH : v ∈ H := by
    refine H.mul_mem (H.mul_mem (hG ρ) (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem (hG σ)) (hD s)) (hG σ))
      (H.inv_mem (hD s)))) (H.inv_mem (hG ρ))
  have hvm : (v : Matrix (Fin 2) (Fin 2) F) = !![-1, 4 * ((ρ : F) ^ 4 + 1) / ((γ : F) * ((ρ : F) ^ 4 - 1)); 0, -1] := by
    have hk := key_identity (γ : F) (ρ : F) γ.ne_zero hρ0 h4 h1 h2
    simp only at hk
    rw [← hk]
    simp only [hv, Matrix.SpecialLinearGroup.coe_mul, coe_inv_fin_two]
    simp [hg, hG', hσ, hs, hypS, dgS, Units.val_inv_eq_inv_val]
  have hv2 : v * v = e12 (-2 * (4 * ((ρ : F) ^ 4 + 1) / ((γ : F) * ((ρ : F) ^ 4 - 1)))) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hvm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e12, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [← hv2]
  exact H.mul_mem hvH hvH

theorem e12_mul (a b : F) : e12 a * e12 b = e12 (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e12, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem e12_zero : (e12 (0 : F)) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e12]

theorem e12_all_of_ne [Finite F] (hodd : Nat.card F % 2 = 1) (H : Subgroup SL(2, F)) (hD : ∀ s : Fˣ, dgS s ∈ H)
    {β : F} (hβ : β ≠ 0) (hH : e12 β ∈ H) (a : F) : e12 a ∈ H := by
  obtain ⟨x, y, hxy⟩ := exists_two_sq hodd (one_ne_zero : (1 : F) ≠ 0) (one_ne_zero : (1 : F) ≠ 0) (a / β)
  have hsq : ∀ t : F, e12 (β * t ^ 2) ∈ H := by
    intro t
    by_cases ht : t = 0
    · rw [ht]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]; rw [e12_zero]; exact H.one_mem
    · have := H.mul_mem (H.mul_mem (hD (Units.mk0 t ht)) hH) (H.inv_mem (hD (Units.mk0 t ht)))
      rw [dgS_e12] at this
      simpa [mul_comm] using this
  have h1 : a = β * x ^ 2 + β * y ^ 2 := by
    field_simp at hxy
    linear_combination (-1 : F) * hxy
  have : e12 a = e12 (β * x ^ 2) * e12 (β * y ^ 2) := by rw [e12_mul, ← h1]
  rw [this]
  exact H.mul_mem (hsq x) (hsq y)

@[expose] def wS : SL(2, F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem wS_conj (x : F) : wS * e12 x * wS⁻¹ = e21 (-x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wS, e12, e21, Matrix.mul_apply, Fin.sum_univ_two]

theorem wS_mem [Finite F] (H : Subgroup SL(2, F)) (hD : ∀ s : Fˣ, dgS s ∈ H) (hE : ∀ a : F, e12 a ∈ H)
    (g : SL(2, F)) (hg : g ∈ H) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : wS ∈ H := by
  set c : Fˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) F) 1 0) hc with hcdef
  have : wS = dgS c * e12 (-((g : Matrix (Fin 2) (Fin 2) F) 0 0) / c) * g * e12 (-((g : Matrix (Fin 2) (Fin 2) F) 1 1) / c) := by
    apply Subtype.ext
    have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
      have := g.2
      rwa [Matrix.det_fin_two] at this
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wS, dgS, e12, hcdef, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp
    all_goals first | ring1 | linear_combination (-1 : F) * hdet | linear_combination hdet
  rw [this]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hD c) (hE _)) hg) (hE _)


theorem plane_sl2 [Finite F] (hodd : Nat.card F % 2 = 1) (h2 : (2 : F) ≠ 0) (γ ρ : Fˣ) (h4 : (ρ : F) ^ 4 ≠ 1)
    (h1 : (ρ : F) ^ 2 + 1 ≠ 0) (h5 : (ρ : F) ^ 4 + 1 ≠ 0) (H : Subgroup SL(2, F)) (hD : ∀ s : Fˣ, dgS s ∈ H)
    (hG : ∀ σ : Fˣ, hypS h2 γ σ ∈ H) : (∀ a : F, e12 a ∈ H) ∧ (∀ a : F, e21 a ∈ H) := by
  have hρ0 : (ρ : F) ≠ 0 := ρ.ne_zero
  have hγ0 : (γ : F) ≠ 0 := γ.ne_zero
  have hs2 : (ρ : F) ^ 4 - 1 ≠ 0 := sub_ne_zero.2 h4
  have hβ : -2 * (4 * ((ρ : F) ^ 4 + 1) / ((γ : F) * ((ρ : F) ^ 4 - 1))) ≠ 0 := by
    have h4' : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    exact mul_ne_zero (neg_ne_zero.2 h2) (div_ne_zero (mul_ne_zero h4' h5) (mul_ne_zero hγ0 hs2))
  have hE : ∀ a : F, e12 a ∈ H := e12_all_of_ne hodd H hD hβ (plane_unipotent h2 γ ρ h4 h1 H hD hG)
  refine ⟨hE, fun a => ?_⟩
  set σ : Fˣ := ρ ^ 2 with hσ
  have hlow : (hypS h2 γ σ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    simp only [hypS, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const]
    simp only [hσ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
    exact div_ne_zero (mul_ne_zero hγ0 hs2) (mul_ne_zero (pow_ne_zero 2 hρ0) h2)
  have hw := wS_mem H hD hE (hypS h2 γ σ) (hG σ) hlow
  have := H.mul_mem (H.mul_mem hw (hE (-a))) (H.inv_mem hw)
  rw [wS_conj, neg_neg] at this
  exact this

@[expose] def planar (g : SL(2, F)) : SL(4, F) :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
      (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by
    have := g.2
    rw [Matrix.det_fin_two] at this
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    linear_combination this⟩

theorem coe_planar (g : SL(2, F)) : ((planar g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
      (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := rfl

theorem planar_one : planar (1 : SL(2, F)) = 1 := by
  apply Subtype.ext
  rw [coe_planar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem planar_mul (g h : SL(2, F)) : planar (g * h) = planar g * planar h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_planar, coe_planar, coe_planar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Matrix.SpecialLinearGroup.coe_mul]

@[expose] def planarHom : SL(2, F) →* SL(4, F) where
  toFun := planar
  map_one' := planar_one
  map_mul' := planar_mul

theorem planarHom_apply (g : SL(2, F)) : planarHom g = planar g := rfl

theorem planarHom_e12 (a : F) : planarHom (e12 a) = tv 0 1 (by decide) a := by
  apply Subtype.ext
  rw [planarHom_apply, coe_planar, coe_tv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e12, Matrix.single_apply]

theorem planarHom_e21 (a : F) : planarHom (e21 a) = tv 1 0 (by decide) a := by
  apply Subtype.ext
  rw [planarHom_apply, coe_planar, coe_tv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e21, Matrix.single_apply]

theorem plane_top [Finite F] (hodd : Nat.card F % 2 = 1) (h2 : (2 : F) ≠ 0) (γ ρ : Fˣ) (h4 : (ρ : F) ^ 4 ≠ 1)
    (h1 : (ρ : F) ^ 2 + 1 ≠ 0) (h5 : (ρ : F) ^ 4 + 1 ≠ 0) (Γ : Subgroup SL(4, F))
    (hD : ∀ s : Fˣ, planarHom (dgS s) ∈ Γ) (hG : ∀ σ : Fˣ, planarHom (hypS h2 γ σ) ∈ Γ) :
    (∀ a : F, tv 0 1 (by decide) a ∈ Γ) ∧ (∀ a : F, tv 1 0 (by decide) a ∈ Γ) := by
  have := plane_sl2 hodd h2 γ ρ h4 h1 h5 (Γ.comap planarHom) hD hG
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have := this.1 a
    rwa [Subgroup.mem_comap, planarHom_e12] at this
  · have := this.2 a
    rwa [Subgroup.mem_comap, planarHom_e21] at this

end PlaneSL2






end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
