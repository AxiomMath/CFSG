module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def tU (a : K) : SL(2,K) := transvection (zero_ne_one : (0:Fin 2) ≠ 1) a
@[expose] def tL (a : K) : SL(2,K) := transvection (one_ne_zero : (1:Fin 2) ≠ 0) a

@[expose] def sl2Mk (a b c d : K) (h : a * d - b * c = 1) : SL(2,K) :=
  ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using h⟩

theorem sl2_det (g : SL(2,K)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

theorem sl2_ext {g h : SL(2,K)} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1)
    (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[simp] theorem sl2Mk_00 (a b c d : K) (h) : sl2Mk a b c d h 0 0 = a := by simp [sl2Mk]
@[simp] theorem sl2Mk_01 (a b c d : K) (h) : sl2Mk a b c d h 0 1 = b := by simp [sl2Mk]
@[simp] theorem sl2Mk_10 (a b c d : K) (h) : sl2Mk a b c d h 1 0 = c := by simp [sl2Mk]
@[simp] theorem sl2Mk_11 (a b c d : K) (h) : sl2Mk a b c d h 1 1 = d := by simp [sl2Mk]

@[simp] theorem sl2_mul_00 (g h : SL(2,K)) : (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] theorem sl2_mul_01 (g h : SL(2,K)) : (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] theorem sl2_mul_10 (g h : SL(2,K)) : (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] theorem sl2_mul_11 (g h : SL(2,K)) : (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sl2_one_00 : (1 : SL(2,K)) 0 0 = 1 := by simp
@[simp] theorem sl2_one_01 : (1 : SL(2,K)) 0 1 = 0 := by simp
@[simp] theorem sl2_one_10 : (1 : SL(2,K)) 1 0 = 0 := by simp
@[simp] theorem sl2_one_11 : (1 : SL(2,K)) 1 1 = 1 := by simp

@[simp] theorem sl2_inv_00 (g : SL(2,K)) : (g⁻¹) 0 0 = g 1 1 := by
  simp [coe_inv, Matrix.adjugate_fin_two]
@[simp] theorem sl2_inv_01 (g : SL(2,K)) : (g⁻¹) 0 1 = - g 0 1 := by
  simp [coe_inv, Matrix.adjugate_fin_two]
@[simp] theorem sl2_inv_10 (g : SL(2,K)) : (g⁻¹) 1 0 = - g 1 0 := by
  simp [coe_inv, Matrix.adjugate_fin_two]
@[simp] theorem sl2_inv_11 (g : SL(2,K)) : (g⁻¹) 1 1 = g 0 0 := by
  simp [coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem tU_00 (a : K) : tU a 0 0 = 1 := by simp [tU, transvection_coe]
@[simp] theorem tU_01 (a : K) : tU a 0 1 = a := by simp [tU, transvection_coe]
@[simp] theorem tU_10 (a : K) : tU a 1 0 = 0 := by simp [tU, transvection_coe]
@[simp] theorem tU_11 (a : K) : tU a 1 1 = 1 := by simp [tU, transvection_coe]
@[simp] theorem tL_00 (a : K) : tL a 0 0 = 1 := by simp [tL, transvection_coe]
@[simp] theorem tL_01 (a : K) : tL a 0 1 = 0 := by simp [tL, transvection_coe]
@[simp] theorem tL_10 (a : K) : tL a 1 0 = a := by simp [tL, transvection_coe]
@[simp] theorem tL_11 (a : K) : tL a 1 1 = 1 := by simp [tL, transvection_coe]

theorem tU_add (a b : K) : tU a * tU b = tU (a + b) := by
  apply sl2_ext <;> simp [add_comm]

theorem tU_zero : tU (0:K) = 1 := by apply sl2_ext <;> simp
theorem tU_injective : Function.Injective (tU : K → SL(2,K)) := fun a b h => by
  simpa using congrArg (fun g : SL(2,K) => g 0 1) h

theorem tU_inv (a : K) : (tU a)⁻¹ = tU (-a) := by
  apply sl2_ext <;> simp



section char2
variable [CharP K 2]

theorem two_eq_zero : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  simpa using this

theorem neg_eq_self' (x : K) : -x = x := CharTwo.neg_eq x

theorem sq_eq_one_iff' {x : K} : x ^ 2 = 1 ↔ x = 1 := by
  constructor
  · intro h
    have : (x - 1) ^ 2 = 0 := by linear_combination h - (x - 1) * (two_eq_zero (K := K))
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination this
  · rintro rfl; simp

theorem exists_conj_tU_one [Finite K] (x : SL(2,K)) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ h : SL(2,K), h * x * h⁻¹ = tU 1 := by
  have h2 : (2:K) = 0 := two_eq_zero
  have hF : ringChar K = 2 := ringChar.eq K 2
  have e1 : x 0 0 * x 0 0 + x 0 1 * x 1 0 = 1 := by
    simpa using congrArg (fun g : SL(2,K) => g 0 0) hx2
  have e4 : x 1 0 * x 0 1 + x 1 1 * x 1 1 = 1 := by
    simpa using congrArg (fun g : SL(2,K) => g 1 1) hx2
  have hdet := sl2_det x
  have hda : x 1 1 = x 0 0 := by
    have : (x 0 0 - x 1 1) ^ 2 = 0 := by
      linear_combination (e1 - hdet) + (e4 - hdet) + (-2 * x 0 1 * x 1 0) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination -this
  have hmul : ∀ h : SL(2,K), h * x = tU 1 * h → ∃ h : SL(2,K), h * x * h⁻¹ = tU 1 :=
    fun h hh => ⟨h, by rw [mul_inv_eq_iff_eq_mul]; exact hh⟩
  by_cases hc : x 1 0 = 0
  · have ha1 : x 0 0 = 1 := by
      have : x 0 0 ^ 2 = 1 := by simpa [hc, pow_two] using e1
      exact sq_eq_one_iff'.mp this
    have hb : x 0 1 ≠ 0 := by
      intro hb; apply hx1; apply sl2_ext <;> simp [hb, hc, ha1, hda]
    obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two hF ((x 0 1)⁻¹)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hμ
      exact hb hμ
    refine ⟨sl2Mk μ 0 0 μ⁻¹ (by field_simp; ring), ?_⟩
    have hμ2 : μ * μ * x 0 1 = 1 := by rw [← hμ]; field_simp
    apply sl2_ext <;> simp [hc, ha1, hda]
    · field_simp
    · linear_combination hμ2
    · field_simp
  · obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two hF ((x 1 0)⁻¹)
    have hμ2 : μ * μ * x 1 0 = 1 := by rw [← hμ]; field_simp
    refine hmul (sl2Mk 0 μ (μ * x 1 0) (μ * (x 0 0 + 1)) (by linear_combination (-1:K) * hμ2 + (-1 : K) * h2)) ?_
    apply sl2_ext <;> simp [hda]
    · linear_combination (-μ) * h2
    · linear_combination (μ * x 1 0 * x 0 0) * h2
    · linear_combination μ * e1

theorem sl2_invol_diag (x : SL(2,K)) (hx2 : x * x = 1) : x 1 1 = x 0 0 := by
  have h2 : (2:K) = 0 := two_eq_zero
  have e1 : x 0 0 * x 0 0 + x 0 1 * x 1 0 = 1 := by
    simpa using congrArg (fun g : SL(2,K) => g 0 0) hx2
  have e4 : x 1 0 * x 0 1 + x 1 1 * x 1 1 = 1 := by
    simpa using congrArg (fun g : SL(2,K) => g 1 1) hx2
  have hdet := sl2_det x
  have : (x 0 0 - x 1 1) ^ 2 = 0 := by
    linear_combination (e1 - hdet) + (e4 - hdet) + (-2 * x 0 1 * x 1 0) * h2
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  linear_combination -this

@[expose] def wSL : SL(2,K) :=
  sl2Mk 0 1 1 0 (by linear_combination (-1 : K) * (two_eq_zero (K := K)))

@[simp] theorem wSL_00 : (wSL : SL(2,K)) 0 0 = 0 := by simp [wSL]
@[simp] theorem wSL_01 : (wSL : SL(2,K)) 0 1 = 1 := by simp [wSL]
@[simp] theorem wSL_10 : (wSL : SL(2,K)) 1 0 = 1 := by simp [wSL]
@[simp] theorem wSL_11 : (wSL : SL(2,K)) 1 1 = 0 := by simp [wSL]

theorem wSL_mul_self : (wSL : SL(2,K)) * wSL = 1 := by
  apply sl2_ext <;> simp

theorem wSL_inv : (wSL : SL(2,K))⁻¹ = wSL := by
  apply sl2_ext <;> simp [neg_eq_self']

theorem tL_eq (c : K) : tL c = wSL * tU c * wSL⁻¹ := by
  apply sl2_ext <;> simp [neg_eq_self']

theorem wSL_tU_cube : (wSL * tU (1:K)) * (wSL * tU 1) * (wSL * tU 1) = 1 := by
  have h2 : (2:K) = 0 := two_eq_zero
  apply sl2_ext <;> simp <;> linear_combination h2

theorem sl2_order_three_trace (M : SL(2,K)) (hM : M * M * M = 1) (hM1 : M ≠ 1) :
    M 0 0 + M 1 1 = 1 := by
  have h2 : (2:K) = 0 := two_eq_zero
  have hdet := sl2_det M
  have e00 := congrArg (fun g : SL(2,K) => g 0 0) hM
  have e01 := congrArg (fun g : SL(2,K) => g 0 1) hM
  have e10 := congrArg (fun g : SL(2,K) => g 1 0) hM
  have e11 := congrArg (fun g : SL(2,K) => g 1 1) hM
  simp at e00 e01 e10 e11
  by_cases hT : (M 0 0 + M 1 1) ^ 2 - 1 = 0
  · have : (M 0 0 + M 1 1 - 1) ^ 2 = 0 := by linear_combination hT - (M 0 0 + M 1 1 - 1) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination this
  · exfalso
    have hb : M 0 1 = 0 := by
      have : ((M 0 0 + M 1 1) ^ 2 - 1) * M 0 1 = 0 := by linear_combination e01 + M 0 1 * hdet
      exact (mul_eq_zero.mp this).resolve_left hT
    have hc : M 1 0 = 0 := by
      have : ((M 0 0 + M 1 1) ^ 2 - 1) * M 1 0 = 0 := by linear_combination e10 + M 1 0 * hdet
      exact (mul_eq_zero.mp this).resolve_left hT
    rw [hb, hc] at e00 e11 hdet
    have hd : M 1 1 = M 0 0 ^ 2 := by
      have : M 1 1 = M 1 1 * (M 0 0 ^ 3) := by
        have : M 0 0 ^ 3 = 1 := by linear_combination e00
        rw [this, mul_one]
      rw [this]; linear_combination (M 0 0 ^ 2) * hdet
    by_cases ha : M 0 0 = 1
    · apply hM1
      apply sl2_ext <;> simp [hb, hc, ha, hd]
    · apply hT
      have h3 : (M 0 0 - 1) * (M 0 0 ^ 2 + M 0 0 + 1) = 0 := by linear_combination e00
      have h4 : M 0 0 ^ 2 + M 0 0 + 1 = 0 :=
        (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha)
      rw [hd]
      linear_combination (M 0 0 ^ 2 + M 0 0 - 1) * h4


theorem sl2_comm_tU_one {x : SL(2,K)} (hx : x * tU 1 = tU 1 * x) : ∃ a, x = tU a := by
  have h2 : (2:K) = 0 := two_eq_zero
  have e00 := congrArg (fun g : SL(2,K) => g 0 0) hx
  have e01 := congrArg (fun g : SL(2,K) => g 0 1) hx
  have e11 := congrArg (fun g : SL(2,K) => g 1 1) hx
  simp at e00 e01 e11
  have hr : x 1 0 = 0 := e00
  have hp : x 1 1 = x 0 0 := by linear_combination -e01
  have hdet := sl2_det x
  have hp1 : x 0 0 = 1 := by
    apply sq_eq_one_iff'.mp
    rw [hr, hp] at hdet
    linear_combination hdet
  refine ⟨x 0 1, ?_⟩
  apply sl2_ext <;> simp [hr, hp, hp1]

theorem sl2_normalizes_tU_one {g : SL(2,K)} {b : K} (hg : g * tU 1 = tU b * g) : g 1 0 = 0 := by
  have e11 := congrArg (fun g : SL(2,K) => g 1 1) hg
  simpa using e11

theorem sl2_conj_tU {g : SL(2,K)} (hg : g 1 0 = 0) (a : K) :
    g * tU a = tU (g 0 0 ^ 2 * a) * g := by
  have hdet := sl2_det g
  rw [hg] at hdet
  apply sl2_ext <;> simp [hg]
  linear_combination (-(g 0 0 * a)) * hdet

@[expose] def dSL (t : K) (ht : t ≠ 0) : SL(2,K) := sl2Mk t 0 0 t⁻¹ (by field_simp; ring)
@[simp] theorem dSL_00 (t : K) (ht : t ≠ 0) : dSL t ht 0 0 = t := by simp [dSL]
@[simp] theorem dSL_01 (t : K) (ht : t ≠ 0) : dSL t ht 0 1 = 0 := by simp [dSL]
@[simp] theorem dSL_10 (t : K) (ht : t ≠ 0) : dSL t ht 1 0 = 0 := by simp [dSL]
@[simp] theorem dSL_11 (t : K) (ht : t ≠ 0) : dSL t ht 1 1 = t⁻¹ := by simp [dSL]


@[expose] def slFieldAut (σ : K ≃+* K) : MulAut SL(2,K) where
  toFun := Matrix.SpecialLinearGroup.map (σ : K →+* K)
  invFun := Matrix.SpecialLinearGroup.map (σ.symm : K →+* K)
  left_inv g := by
    apply sl2_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv g := by
    apply sl2_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' g h := map_mul _ g h

theorem slFieldAut_apply (σ : K ≃+* K) (g : SL(2,K)) (i j : Fin 2) :
    (slFieldAut σ g) i j = σ (g i j) := by
  simp [slFieldAut, Matrix.SpecialLinearGroup.map_apply_coe]


theorem tU_conj_tU (p a : K) : (tU p)⁻¹ * tU a * tU p = tU a := by
  rw [tU_inv, tU_add, tU_add]; congr 1; ring

theorem exists_fieldAut_of_fixes [Finite K] (α : MulAut SL(2,K)) (hα : α (tU 1) = tU 1) :
    ∃ (σ : K ≃+* K) (p : K), α = slFieldAut σ * MulAut.conj (tU p) := by
  have h2 : (2:K) = 0 := two_eq_zero
  have hF : ringChar K = 2 := ringChar.eq K 2
  have hU : ∀ a, ∃ b, α (tU a) = tU b := by
    intro a
    apply sl2_comm_tU_one
    have := congrArg α (show tU a * tU 1 = tU 1 * tU a by rw [tU_add, tU_add, add_comm])
    rw [map_mul, map_mul, hα] at this
    exact this
  choose σf hσf using hU
  have hσ0 : σf 0 = 0 := by
    apply tU_injective
    rw [← hσf, tU_zero, map_one]
  have hσ1 : σf 1 = 1 := by
    apply tU_injective
    rw [← hσf, hα]
  have hadd : ∀ a b, σf (a + b) = σf a + σf b := by
    intro a b
    apply tU_injective
    rw [← hσf, ← tU_add, map_mul, hσf, hσf, tU_add]
  have hsq : ∀ t y : K, σf (t * t * y) = σf (t * t) * σf y := by
    intro t y
    by_cases ht : t = 0
    · subst ht; simp [hσ0]
    have hd : ∀ a, dSL t ht * tU a = tU (t * t * a) * dSL t ht := fun a => by
      rw [sl2_conj_tU (dSL_10 t ht) a]; simp [dSL_00, pow_two]
    have hg : ∀ a, α (dSL t ht) * tU (σf a) = tU (σf (t * t * a)) * α (dSL t ht) := fun a => by
      have := congrArg α (hd a)
      rwa [map_mul, map_mul, hσf, hσf] at this
    have hg10 : α (dSL t ht) 1 0 = 0 := by
      apply sl2_normalizes_tU_one (b := σf (t * t))
      have := hg 1
      rwa [hσ1, mul_one] at this
    have key : ∀ a, σf (t * t * a) = α (dSL t ht) 0 0 ^ 2 * σf a := fun a => by
      have hconj := sl2_conj_tU hg10 (σf a)
      have : tU (α (dSL t ht) 0 0 ^ 2 * σf a) = tU (σf (t * t * a)) :=
        mul_right_cancel (b := α (dSL t ht)) (by rw [← hconj]; exact hg a)
      exact (tU_injective this).symm
    have k1 := key 1
    rw [mul_one, hσ1, mul_one] at k1
    rw [key y, k1]
  have hmul : ∀ x y : K, σf (x * y) = σf x * σf y := by
    intro x y
    obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two hF x
    rw [ht, hsq]
  let σr : K →+* K :=
    { toFun := σf, map_one' := hσ1, map_mul' := hmul, map_zero' := hσ0, map_add' := hadd }
  have hbij : Function.Bijective σr := Finite.injective_iff_bijective.mp σr.injective
  let σ : K ≃+* K := RingEquiv.ofBijective σr hbij
  have hσ : ∀ a, σ a = σf a := fun a => rfl
  let φ := slFieldAut σ
  have hφU : ∀ a, φ (tU a) = α (tU a) := by
    intro a
    rw [hσf]
    apply sl2_ext <;> simp [φ, slFieldAut_apply, hσ, hσ0, hσ1]
  let β : MulAut SL(2,K) := φ⁻¹ * α
  have hβ : ∀ A, β A = φ⁻¹ (α A) := fun A => rfl
  have hβU : ∀ a, β (tU a) = tU a := by
    intro a
    rw [hβ, ← hφU]
    exact MulAut.inv_apply_self _ _ _
  set W : SL(2,K) := β wSL with hWdef
  have hWW : W * W = 1 := by rw [hWdef, ← map_mul, wSL_mul_self, map_one]
  have hW3 : (W * tU 1) * (W * tU 1) * (W * tU 1) = 1 := by
    have := congrArg β (wSL_tU_cube (K := K))
    simp only [map_mul, hβU, map_one] at this
    exact this
  have hWne : W * tU 1 ≠ 1 := by
    intro h
    have hW : W = tU 1 := by
      rw [mul_eq_one_iff_eq_inv, tU_inv, neg_eq_self'] at h
      exact h
    have : β wSL = β (tU 1) := by rw [← hWdef, hW, hβU]
    have := congrArg (fun g : SL(2,K) => g 0 0) (β.injective this)
    simp at this
  have htr := sl2_order_three_trace _ hW3 hWne
  have hdiag := sl2_invol_diag W hWW
  have hr : W 1 0 = 1 := by
    simp at htr
    linear_combination htr - hdiag - W 0 0 * h2
  have hq : W 0 1 = 1 + W 0 0 * W 0 0 := by
    have e1 : W 0 0 * W 0 0 + W 0 1 * W 1 0 = 1 := by
      simpa using congrArg (fun g : SL(2,K) => g 0 0) hWW
    rw [hr] at e1
    linear_combination e1 - W 0 0 * W 0 0 * h2
  have hWform : W = tU (W 0 0) * wSL * (tU (W 0 0))⁻¹ := by
    apply sl2_ext <;> simp [hr, hq, hdiag, neg_eq_self']
    ring
  obtain ⟨p, hWform⟩ : ∃ p, W = tU p * wSL * (tU p)⁻¹ := ⟨_, hWform⟩
  let γ : MulAut SL(2,K) := MulAut.conj (tU p)⁻¹ * β
  have hγU : ∀ a, γ (tU a) = tU a := by
    intro a
    show (tU p)⁻¹ * β (tU a) * ((tU p)⁻¹)⁻¹ = tU a
    rw [hβU, inv_inv]
    exact tU_conj_tU _ _
  have hγw : γ wSL = wSL := by
    show (tU p)⁻¹ * β wSL * ((tU p)⁻¹)⁻¹ = wSL
    rw [← hWdef, hWform, inv_inv]
    group
  have hγ : ∀ A, γ A = A := by
    intro A
    refine SL2.transvection_induction (fun A => γ A = A) ?_ ?_ A
    · intro i j h c
      fin_cases i <;> fin_cases j
      · exact absurd rfl h
      · exact hγU c
      · show γ (tL c) = tL c
        rw [tL_eq, map_mul, map_mul, map_inv, hγU, hγw, wSL_inv]
      · exact absurd rfl h
    · intro A B hA hB
      simp only [map_mul, hA, hB]
  have hβA : ∀ A, β A = tU p * A * (tU p)⁻¹ := by
    intro A
    have := hγ A
    change (tU p)⁻¹ * β A * ((tU p)⁻¹)⁻¹ = A at this
    rw [inv_inv] at this
    calc β A = tU p * ((tU p)⁻¹ * β A * tU p) * (tU p)⁻¹ := by group
      _ = _ := by rw [this]
  refine ⟨σ, p, ?_⟩
  ext A : 1
  change α A = φ (tU p * A * (tU p)⁻¹)
  rw [← hβA, hβ]
  exact (MulAut.apply_inv_self _ _ _).symm


theorem slFieldAut_mul (σ τ : K ≃+* K) : slFieldAut (σ * τ) = slFieldAut σ * slFieldAut τ := by
  ext A : 1
  apply sl2_ext <;> simp [slFieldAut_apply]

theorem slFieldAut_one : slFieldAut (1 : K ≃+* K) = 1 := by
  ext A : 1
  apply sl2_ext <;> simp [slFieldAut_apply]

@[expose] def slFieldAutHom : (K ≃+* K) →* MulAut SL(2,K) where
  toFun := slFieldAut
  map_one' := slFieldAut_one
  map_mul' := slFieldAut_mul

theorem slFieldAut_mul_conj (σ : K ≃+* K) (u : SL(2,K)) :
    slFieldAut σ * MulAut.conj u = MulAut.conj (slFieldAut σ u) * slFieldAut σ := by
  ext A : 1
  simp [MulAut.conj_apply]

theorem exists_conj_fieldAut [Finite K] (α : MulAut SL(2,K)) :
    ∃ (g : SL(2,K)) (σ : K ≃+* K), α = MulAut.conj g * slFieldAut σ := by
  have h2 : (2:K) = 0 := two_eq_zero
  have hx2 : α (tU 1) * α (tU 1) = 1 := by
    rw [← map_mul, tU_add, show (1:K) + 1 = 0 by linear_combination h2, tU_zero, map_one]
  have hx1 : α (tU 1) ≠ 1 := by
    intro h
    have := α.injective (h.trans (map_one α).symm)
    have := congrArg (fun g : SL(2,K) => g 0 1) this
    simp at this
  obtain ⟨h, hh⟩ := exists_conj_tU_one _ hx2 hx1
  have hα' : (MulAut.conj h * α) (tU 1) = tU 1 := by
    simpa [MulAut.conj_apply] using hh
  obtain ⟨σ, p, hσ⟩ := exists_fieldAut_of_fixes _ hα'
  refine ⟨h⁻¹ * slFieldAut σ (tU p), σ, ?_⟩
  have : α = MulAut.conj h⁻¹ * (MulAut.conj h * α) := by
    rw [← mul_assoc, ← map_mul]; simp
  rw [this, hσ, slFieldAut_mul_conj, ← mul_assoc, ← map_mul]


theorem sl2_order_three_sq (x : SL(2,K)) (hx : x * x * x = 1) (hx1 : x ≠ 1) :
    ((x * x : SL(2,K)) : Matrix (Fin 2) (Fin 2) K) = (x : Matrix (Fin 2) (Fin 2) K) + 1 := by
  have h2 : (2:K) = 0 := two_eq_zero
  have htr := sl2_order_three_trace x hx hx1
  have hdet := sl2_det x
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (x 0 0) * htr + hdet - h2 + (1 - x 0 0 * x 1 1 + x 0 1 * x 1 0) * h2
  · linear_combination (x 0 1) * htr
  · linear_combination (x 1 0) * htr
  · linear_combination (x 1 1) * htr + hdet - h2 + (1 - x 0 0 * x 1 1 + x 0 1 * x 1 0) * h2

theorem sl2_eq_of_sq {a b : SL(2,K)} (hab : a * b = b * a)
    (ha : ((a * a : SL(2,K)) : Matrix (Fin 2) (Fin 2) K) = (a : Matrix (Fin 2) (Fin 2) K) + 1)
    (hb : ((b * b : SL(2,K)) : Matrix (Fin 2) (Fin 2) K) = (b : Matrix (Fin 2) (Fin 2) K) + 1)
    (hab2 : (((a * b) * (a * b) : SL(2,K)) : Matrix (Fin 2) (Fin 2) K) =
      ((a * b : SL(2,K)) : Matrix (Fin 2) (Fin 2) K) + 1) : a = b := by
  have hc : ((a : Matrix (Fin 2) (Fin 2) K)) * b = b * a := by
    simpa using congrArg (fun g : SL(2,K) => (g : Matrix (Fin 2) (Fin 2) K)) hab
  simp only [coe_mul] at ha hb hab2
  have e : (a : Matrix (Fin 2) (Fin 2) K) + b = 0 := by
    have : (a : Matrix (Fin 2) (Fin 2) K) * b * ((a : Matrix (Fin 2) (Fin 2) K) * b) =
        (a * a) * (b * b) := by
      calc _ = (a : Matrix (Fin 2) (Fin 2) K) * (b * a) * b := by noncomm_ring
        _ = (a : Matrix (Fin 2) (Fin 2) K) * (a * b) * b := by rw [hc]
        _ = _ := by noncomm_ring
    rw [this, ha, hb] at hab2
    have : ((a : Matrix (Fin 2) (Fin 2) K) + 1) * ((b : Matrix (Fin 2) (Fin 2) K) + 1) =
      (a : Matrix (Fin 2) (Fin 2) K) * b + 1 + (a + b) := by noncomm_ring
    rw [this] at hab2
    simpa using hab2
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun e i) j
  simp at this
  linear_combination this - (b i j) * two_eq_zero (K := K)


theorem sl2_card_le_three [Finite K] (A : Subgroup SL(2,K)) (hcomm : IsMulCommutative A)
    (hA : ∀ x ∈ A, x ^ 3 = 1) : Nat.card A ≤ 3 := by
  classical
  by_cases hbot : ∀ x ∈ A, x = 1
  · have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hbot
    rw [this]; simp
  push Not at hbot
  obtain ⟨a, ha, ha1⟩ := hbot
  have hcube : ∀ x ∈ A, x * x * x = 1 := fun x hx => by
    have := hA x hx
    rw [pow_three'] at this
    exact this
  have key : ∀ b ∈ A, b = 1 ∨ b = a ∨ b = a⁻¹ := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    right
    by_cases hab : a * b = 1
    · right; exact eq_inv_of_mul_eq_one_right hab
    · left
      have hcab : a * b = b * a := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> fun h => by
        simpa using congrArg Subtype.val h
      have hmem : a * b ∈ A := A.mul_mem ha hb
      exact (sl2_eq_of_sq hcab (sl2_order_three_sq a (hcube a ha) ha1)
        (sl2_order_three_sq b (hcube b hb) hb1)
        (sl2_order_three_sq (a * b) (hcube _ hmem) hab)).symm
  have hsub : (A : Set SL(2,K)) ⊆ {1, a, a⁻¹} := by
    intro b hb
    rcases key b hb with h | h | h <;> simp [h]
  calc Nat.card A = (A : Set SL(2,K)).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, a, a⁻¹} : Set SL(2,K)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      simp

end char2

theorem center_eq_bot (K : Type*) [Field K] [CharP K 2] :
    Subgroup.center SL(2, K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  obtain ⟨a, rfl⟩ := sl2_comm_tU_one (hx (tU 1)).symm
  have := congrArg (fun g : SL(2, K) => g 0 0) (hx (tL 1))
  simp at this
  have ha : a = 0 := by linear_combination this
  rw [ha, tU_zero]

noncomputable def mulEquivPSL (K : Type*) [Field K] [CharP K 2] :
    SL(2, K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(2, K)))
    ⟨(injective_iff_map_eq_one _).2 (fun x hx => by
        have : x ∈ Subgroup.center SL(2, K) := (QuotientGroup.eq_one_iff x).1 hx
        rwa [center_eq_bot, Subgroup.mem_bot] at this),
     QuotientGroup.mk'_surjective _⟩

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open scoped MatrixGroups
open SL2Char2

theorem IsL2TwoPowOdd.exists_mulEquiv_sl2 {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ Nonempty (L ≃* SL(2, GaloisField 2 n)) := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h
  exact ⟨n, hn, hn1, ⟨e.trans (mulEquivPSL _).symm⟩⟩


theorem IsL2TwoPowOdd.center_eq_bot {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    Subgroup.center L = ⊥ := by
  obtain ⟨n, -, -, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have : e x ∈ Subgroup.center SL(2, GaloisField 2 n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y)]
  rw [SL2Char2.center_eq_bot, Subgroup.mem_bot] at this
  exact e.injective (this.trans (map_one e).symm)

theorem IsL2TwoPowOdd.card_le_three {L : Type*} [Group L] (h : IsL2TwoPowOdd L) (A : Subgroup L)
    (hA : CFSG.Open.IsElemAbelian 3 A) : Nat.card A ≤ 3 := by
  obtain ⟨n, -, -, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  have hB : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm
  rw [← hB]
  refine sl2_card_le_three _ ?_ ?_
  · obtain ⟨hc, -⟩ := hA
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    apply Subtype.ext
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hA.2 x hx]


theorem table113_T0 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L →
    2 ∣ Nat.card L ∧ 3 ∣ Nat.card L ∧ Subgroup.center L = ⊥ := by
  intro L _ _ h
  refine ⟨?_, ?_, h.center_eq_bot⟩ <;>
  · obtain ⟨n, -, hn1, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
    have hcard : Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula,
        GaloisField.card 2 n (by omega)]
    rw [hcard]
    first
    | exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    | refine Dvd.dvd.mul_left ?_ _
      have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n


instance innerAut113_normal (L : Type*) [Group L] : (innerAut113 L).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ φ
    exact ⟨φ x, by ext y; simp [MulAut.conj_apply]⟩

theorem congr_symm_conj {L S : Type*} [Group L] [Group S] (e : L ≃* S) (g : S) :
    (MulAut.congr e).symm (MulAut.conj g) = MulAut.conj (e.symm g) := by
  ext y
  simp [MulAut.congr_symm_apply, MulAut.conj_apply]

theorem exists_conj_mul_fieldAut {L K : Type*} [Group L] [Field K] [CharP K 2] [Finite K]
    (e : L ≃* SL(2, K)) (α : MulAut L) :
    ∃ (g : L) (σ : K ≃+* K), α = MulAut.conj g * (MulAut.congr e).symm (slFieldAut σ) := by
  obtain ⟨g, σ, hgσ⟩ := exists_conj_fieldAut (MulAut.congr e α)
  refine ⟨e.symm g, σ, ?_⟩
  have := congrArg (MulAut.congr e).symm hgσ
  rw [MulEquiv.symm_apply_apply, map_mul, congr_symm_conj] at this
  exact this

theorem outer_surjective {L K : Type*} [Group L] [Field K] [CharP K 2] [Finite K]
    (e : L ≃* SL(2, K)) :
    Function.Surjective ((QuotientGroup.mk' (innerAut113 L)).comp
      (((MulAut.congr e).symm : MulAut SL(2, K) ≃* MulAut L).toMonoidHom.comp slFieldAutHom)) := by
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, σ, hα⟩ := exists_conj_mul_fieldAut e α
  refine ⟨σ, ?_⟩
  change QuotientGroup.mk' (innerAut113 L) ((MulAut.congr e).symm (slFieldAut σ)) =
    QuotientGroup.mk' (innerAut113 L) α
  rw [hα, map_mul]
  have : QuotientGroup.mk' (innerAut113 L) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  rw [this, one_mul]

noncomputable def ringEquivMulEquivAlgEquiv (K : Type*) [Field K] [Algebra (ZMod 2) K] :
    (K ≃+* K) ≃* (K ≃ₐ[ZMod 2] K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have h : (σ.toRingHom.comp (algebraMap (ZMod 2) K) : ZMod 2 →+* K) =
        algebraMap (ZMod 2) K := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  invFun σ := σ.toRingEquiv
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

theorem isCyclic_ringEquiv_galoisField (n : ℕ) :
    IsCyclic (GaloisField 2 n ≃+* GaloisField 2 n) :=
  (ringEquivMulEquivAlgEquiv (GaloisField 2 n)).isCyclic.mpr inferInstance

theorem card_ringEquiv_galoisField (n : ℕ) (hn : n ≠ 0) :
    Nat.card (GaloisField 2 n ≃+* GaloisField 2 n) = n := by
  rw [Nat.card_congr (ringEquivMulEquivAlgEquiv (GaloisField 2 n)).toEquiv,
    IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 hn]

theorem IsL2TwoPowOdd.outer_structure {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    ∃ n : ℕ, Odd n ∧ IsCyclic (MulAut L ⧸ innerAut113 L) ∧
      Nat.card (MulAut L ⧸ innerAut113 L) ∣ n := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  have hsurj := outer_surjective e
  have := isCyclic_ringEquiv_galoisField n
  refine ⟨n, hn, isCyclic_of_surjective _ hsurj, ?_⟩
  rw [← card_ringEquiv_galoisField n (by omega)]
  exact Subgroup.card_dvd_of_surjective hsurj

theorem IsL2TwoPowOdd.outer_isCyclic {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    IsCyclic (MulAut L ⧸ innerAut113 L) := by
  obtain ⟨_, _, hc, _⟩ := h.outer_structure
  exact hc

theorem IsL2TwoPowOdd.outer_card_odd {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    Odd (Nat.card (MulAut L ⧸ innerAut113 L)) := by
  obtain ⟨_, hn, _, hd⟩ := h.outer_structure
  exact Odd.of_dvd_nat hn hd


theorem conj_injective_of_center_eq_bot {L : Type*} [Group L] (h : Subgroup.center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hmem : g ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := DFunLike.congr_fun hg z
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rwa [h, Subgroup.mem_bot] at hmem

theorem IsL2TwoPowOdd.card_innerAut {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    Nat.card (innerAut113 L) = Nat.card L :=
  (Nat.card_congr (MonoidHom.ofInjective
    (conj_injective_of_center_eq_bot h.center_eq_bot)).toEquiv).symm

theorem IsL2TwoPowOdd.card_inf_innerAut_le {L : Type*} [Group L] (h : IsL2TwoPowOdd L)
    (H : Subgroup (MulAut L)) (hH : CFSG.Open.IsElemAbelian 3 H) :
    Nat.card ↥(H ⊓ innerAut113 L) ≤ 3 := by
  have hinj := conj_injective_of_center_eq_bot h.center_eq_bot
  let c : L →* MulAut L := MulAut.conj
  let A : Subgroup L := (H ⊓ innerAut113 L).comap c
  have hmem : ∀ x, x ∈ A ↔ c x ∈ H := fun x => by
    change c x ∈ H ⊓ innerAut113 L ↔ _
    exact ⟨fun h => h.1, fun h => ⟨h, ⟨x, rfl⟩⟩⟩
  have hA : CFSG.Open.IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hH.1.is_comm.comm (⟨c a, (hmem a).1 ha⟩ : H) ⟨c b, (hmem b).1 hb⟩)
      simpa using this
    · apply hinj
      rw [map_pow, map_one]
      exact hH.2 _ ((hmem x).1 hx)
  have hcard : Nat.card ↥(H ⊓ innerAut113 L) = Nat.card A := by
    have hmap : A.map c = H ⊓ innerAut113 L := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr inf_le_right
    rw [← hmap]
    exact (Nat.card_congr (A.equivMapOfInjective c hinj).toEquiv).symm
  rw [hcard]
  exact h.card_le_three A hA

theorem card_le_three_of_cyclic {C : Type*} [Group C] [IsCyclic C] (h : ∀ x : C, x ^ 3 = 1) :
    Nat.card C ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have h1 : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h g)
  rw [← h1]
  exact Nat.le_of_dvd (by norm_num) h2

theorem table113_T2 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ H : Subgroup (MulAut L),
    CFSG.Open.IsElemAbelian 3 H → Nat.card H ≤ 9 ∧ Nat.card ↥(H ⊓ innerAut113 L) ≤ 3 := by
  intro L _ _ h H hH
  have hin := h.card_inf_innerAut_le H hH
  refine ⟨?_, hin⟩
  have hcyc := h.outer_isCyclic
  let f : H →* MulAut L ⧸ innerAut113 L := (QuotientGroup.mk' (innerAut113 L)).comp H.subtype
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ innerAut113 L) := by
    have : f.ker = (H ⊓ innerAut113 L).subgroupOf H := by
      ext x
      simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card f.range ≤ 3 := by
    refine card_le_three_of_cyclic fun x => ?_
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [← hy]
    change f (y ^ 3) = 1
    have : y ^ 3 = 1 := Subtype.ext (hH.2 y y.2)
    rw [this, map_one]
  rw [← Subgroup.card_ker_mul_card_range f, hker]
  calc Nat.card ↥(H ⊓ innerAut113 L) * Nat.card f.range ≤ 3 * 3 := Nat.mul_le_mul hin hrange
    _ = 9 := by norm_num


theorem IsL2TwoPowOdd.mem_innerAut_of_pow_two {L : Type*} [Group L] (h : IsL2TwoPowOdd L)
    (α : MulAut L) (k : ℕ) (hα : α ^ 2 ^ k = 1) : α ∈ innerAut113 L := by
  have hodd := h.outer_card_odd
  let q : MulAut L ⧸ innerAut113 L := QuotientGroup.mk α
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    change QuotientGroup.mk' (innerAut113 L) (α ^ 2 ^ k) = 1
    rw [hα, map_one])
  have h2 : orderOf q ∣ Nat.card (MulAut L ⧸ innerAut113 L) := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (MulAut L ⧸ innerAut113 L)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have : orderOf q = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have hq : q = 1 := orderOf_eq_one_iff.mp this
  exact (QuotientGroup.eq_one_iff _).1 hq

theorem IsL2TwoPowOdd.le_innerAut_of_isPGroup_two {L : Type*} [Group L] (h : IsL2TwoPowOdd L)
    (S : Subgroup (MulAut L)) (hS : IsPGroup 2 S) : S ≤ innerAut113 L := by
  intro α hα
  obtain ⟨k, hk⟩ := hS ⟨α, hα⟩
  exact h.mem_innerAut_of_pow_two α k (by simpa using congrArg Subtype.val hk)

theorem IsL2TwoPowOdd.card_mulAut {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    ∃ n m : ℕ, Odd n ∧ m ∣ n ∧ Nat.card (MulAut L) = Nat.card L * m := by
  obtain ⟨n, hn, -, hd⟩ := h.outer_structure
  refine ⟨n, _, hn, hd, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (innerAut113 L), h.card_innerAut, mul_comm]

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
