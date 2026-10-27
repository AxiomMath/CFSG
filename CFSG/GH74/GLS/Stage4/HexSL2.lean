module

public import CFSG.GH74.GLS.Stage4.HexSL2Defs
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Hex

section SL2Weights

variable {F : Type*} [Field F]

theorem sl2W_conj {c : F} (hc : c ≠ 0) (d : F) :
    (sl2U c * sl2L (-c⁻¹) * sl2U c) * sl2U d =
      sl2L (-(c⁻¹ * c⁻¹ * d)) * (sl2U c * sl2L (-c⁻¹) * sl2U c) := by
  apply sl2_ext
  simp [Matrix.SpecialLinearGroup.coe_mul]
  field_simp
  ring_nf
  simp

theorem sl2_key {a y e z : F}
    (hM : (sl2U a * sl2L y * sl2U a) * sl2U e = sl2L z * (sl2U a * sl2L y * sl2U a))
    (he : e ≠ 0) : 1 + a * y = 0 ∧ z = -(e * y ^ 2) := by
  have h01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hM
  have h11 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 1) hM
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h01 h11
  have hay : 1 + a * y = 0 := h01.resolve_right he
  rw [hay] at h11
  exact ⟨hay, by linear_combination y * h11 + z * hay⟩

theorem sl2_conj_weight {G : Type*} [Group G] (hF2 : (2 : F) ≠ 0) (φ : SL2 F →* G)
    (hφ : Function.Injective φ) (g : G) (A B : F → F)
    (hA : ∀ c, g * φ (sl2U c) * g⁻¹ = φ (sl2U (A c)))
    (hB : ∀ c, g * φ (sl2L c) * g⁻¹ = φ (sl2L (B c))) :
    ∃ (a : F) (σ : F →+* F), a ≠ 0 ∧ (∀ c, A c = a * σ c) ∧ (∀ c, B c = a⁻¹ * σ c) := by
  let κ : SL2 F →* G := (MulAut.conj g).toMonoidHom.comp φ
  have hκ : ∀ x, κ x = g * φ x * g⁻¹ := fun x => by simp [κ, MulAut.conj_apply]
  have hκinj : Function.Injective κ := (MulAut.conj g).injective.comp hφ
  have hκU : ∀ c, κ (sl2U c) = φ (sl2U (A c)) := fun c => by rw [hκ]; exact hA c
  have hκL : ∀ c, κ (sl2L c) = φ (sl2L (B c)) := fun c => by rw [hκ]; exact hB c
  have hAadd : ∀ c d, A (c + d) = A c + A d := by
    intro c d
    apply sl2U_injective
    apply hφ
    rw [← hκU, sl2U_add, map_mul, hκU, hκU, sl2U_add, map_mul]
  have hBadd : ∀ c d, B (c + d) = B c + B d := by
    intro c d
    apply sl2L_injective
    apply hφ
    rw [← hκL, sl2L_add, map_mul, hκL, hκL, sl2L_add, map_mul]
  have hA0 : A 0 = 0 := by simpa using hAadd 0 0
  have hB0 : B 0 = 0 := by simpa using hBadd 0 0
  have hAneg : ∀ c, A (-c) = -A c := fun c => by
    have := hAadd c (-c)
    rw [add_neg_cancel, hA0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hA1 : A 1 ≠ 0 := by
    intro h
    have h1 : κ (sl2U 1) = κ 1 := by rw [hκU, h, sl2U_zero, map_one, map_one]
    have h2 : sl2U (1 : F) = 1 := hκinj h1
    have h3 : sl2U (1 : F) = sl2U 0 := by rw [h2, sl2U_zero]
    exact one_ne_zero (sl2U_injective h3)
  have key : ∀ c : F, c ≠ 0 → ∀ d : F, A d ≠ 0 →
      1 + A c * B (-c⁻¹) = 0 ∧ B (-(c⁻¹ * c⁻¹ * d)) = -(A d * B (-c⁻¹) ^ 2) := by
    intro c hc d hd
    have hw := congrArg κ (sl2W_conj hc d)
    simp only [map_mul, hκU, hκL] at hw
    have h2 : (sl2U (A c) * sl2L (B (-c⁻¹)) * sl2U (A c)) * sl2U (A d) =
        sl2L (B (-(c⁻¹ * c⁻¹ * d))) * (sl2U (A c) * sl2L (B (-c⁻¹)) * sl2U (A c)) := by
      apply hφ
      simpa only [map_mul] using hw
    exact sl2_key h2 hd
  have hBneg : ∀ c : F, c ≠ 0 → A c ≠ 0 ∧ B (-c⁻¹) = -(A c)⁻¹ := by
    intro c hc
    obtain ⟨h1, -⟩ := key c hc 1 hA1
    have hAc : A c ≠ 0 := fun h => by rw [h, zero_mul, add_zero] at h1; exact one_ne_zero h1
    refine ⟨hAc, ?_⟩
    have h1' : A c * (-B (-c⁻¹)) = 1 := by linear_combination -h1
    have h2 : -B (-c⁻¹) = (A c)⁻¹ := eq_inv_of_mul_eq_one_right h1'
    linear_combination -h2
  have hAsq : ∀ c : F, A (c * c) = A c * A c / A 1 := by
    intro c
    by_cases hc : c = 0
    · subst hc; simp [hA0]
    · obtain ⟨hAc, hBc⟩ := hBneg c hc
      obtain ⟨-, h2⟩ := key c hc 1 hA1
      have hcc : c * c ≠ 0 := mul_ne_zero hc hc
      obtain ⟨hAcc, hBcc⟩ := hBneg (c * c) hcc
      have e1 : -(c⁻¹ * c⁻¹ * 1) = -(c * c)⁻¹ := by rw [mul_one, mul_inv]
      rw [e1, hBcc, hBc] at h2
      have h3 : (A (c * c))⁻¹ = A 1 * ((A c)⁻¹) ^ 2 := by linear_combination -h2
      generalize A (c * c) = X at h3 hAcc ⊢
      generalize A c = Y at h3 hAc ⊢
      generalize A 1 = Z at h3 hA1 ⊢
      rw [eq_div_iff hA1]
      field_simp at h3
      linear_combination -h3
  let σ0 : F → F := fun c => A c / A 1
  have hσadd : ∀ c d, σ0 (c + d) = σ0 c + σ0 d := fun c d => by simp only [σ0, hAadd, add_div]
  have hσ1 : σ0 1 = 1 := div_self hA1
  have hσ0 : σ0 0 = 0 := by simp [σ0, hA0]
  have hσsq : ∀ c, σ0 (c * c) = σ0 c * σ0 c := fun c => by
    simp only [σ0, hAsq]
    field_simp
  have hσmul : ∀ c d, σ0 (c * d) = σ0 c * σ0 d := by
    intro c d
    have h1 : σ0 ((c + d) * (c + d)) = σ0 (c + d) * σ0 (c + d) := hσsq (c + d)
    have e : (c + d) * (c + d) = c * c + c * d + (c * d + d * d) := by ring
    rw [e, hσadd, hσadd, hσadd, hσsq, hσsq, hσadd] at h1
    apply mul_left_cancel₀ hF2
    linear_combination h1
  let σ : F →+* F :=
    { toFun := σ0, map_one' := hσ1, map_mul' := hσmul, map_zero' := hσ0, map_add' := hσadd }
  have hAσ : ∀ c, A c = A 1 * σ c := fun c => by
    show A c = A 1 * (A c / A 1)
    field_simp
  refine ⟨A 1, σ, hA1, hAσ, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [hB0]
  · have hc' : -c⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hc)
    obtain ⟨-, h2⟩ := hBneg (-c⁻¹) hc'
    have e1 : -(-c⁻¹)⁻¹ = c := by rw [inv_neg, inv_inv, neg_neg]
    rw [e1, hAneg, hAσ c⁻¹, map_inv₀] at h2
    rw [h2]
    field_simp

end SL2Weights

end CFSG.GH74.GLS.Stage4.Hex
