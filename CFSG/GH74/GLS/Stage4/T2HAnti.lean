module

public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem t2H_inv_of_anticomm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F) (c : F)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F))
    (W M : SL2 F) (hW : W * W = negOne F)
    (hanti : (g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) =
      -((W : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)))
    (hM : (g : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) =
      (M : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) :
    W * M * W⁻¹ = M⁻¹ := by
  obtain ⟨p, q, r, s, hGe⟩ : ∃ p q r s : F, (g : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨a, b, d, e, hWe⟩ : ∃ a b d e : F, (W : Matrix (Fin 2) (Fin 2) F) = !![a, b; d, e] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨m0, m1, m2, m3, hMe⟩ :
      ∃ m0 m1 m2 m3 : F, (M : Matrix (Fin 2) (Fin 2) F) = !![m0, m1; m2, m3] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdW : a * e - b * d = 1 := by
    have := W.2
    rw [hWe, Matrix.det_fin_two_of] at this
    exact this
  have hW' : (W : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 0; 0, -1] := by
    have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) hW
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  rw [hGe] at hg2 hns hanti hM
  rw [hWe] at hW' hanti
  rw [hMe] at hM
  have hns' : ¬ (q = 0 ∧ r = 0 ∧ p = s) := by
    rintro ⟨hq, hr, hps⟩
    apply hns
    refine ⟨p, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hr, hps]
  have hg00 := congrFun (congrFun hg2 0) 0
  have hg01 := congrFun (congrFun hg2 0) 1
  have hg10 := congrFun (congrFun hg2 1) 0
  have hg11 := congrFun (congrFun hg2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hg00 hg01 hg10 hg11
  have hw00 := congrFun (congrFun hW' 0) 0
  have hw01 := congrFun (congrFun hW' 0) 1
  have hw10 := congrFun (congrFun hW' 1) 0
  have hw11 := congrFun (congrFun hW' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hw00 hw01 hw10 hw11
  have ha00 := congrFun (congrFun hanti 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at ha00
  have hc00 := congrFun (congrFun hM 0) 0
  have hc01 := congrFun (congrFun hM 0) 1
  have hc10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hc00 hc01 hc10
  have hs : s = -p := by
    by_contra hne
    have hsum : p + s ≠ 0 := fun h => hne (by linear_combination h)
    have hq : q = 0 := by
      have : q * (p + s) = 0 := by linear_combination hg01
      exact (mul_eq_zero.1 this).resolve_right hsum
    have hr : r = 0 := by
      have : r * (p + s) = 0 := by linear_combination hg10
      exact (mul_eq_zero.1 this).resolve_right hsum
    have hps : p = s := by
      have : (p - s) * (p + s) = 0 := by
        rw [hq, hr] at hg00 hg11
        linear_combination hg00 - hg11
      exact sub_eq_zero.mp ((mul_eq_zero.1 this).resolve_right hsum)
    exact hns' ⟨hq, hr, hps⟩
  have he : e = -a := by
    by_contra hne
    have hsum : a + e ≠ 0 := fun h => hne (by linear_combination h)
    have hb : b = 0 := by
      have : b * (a + e) = 0 := by linear_combination hw01
      exact (mul_eq_zero.1 this).resolve_right hsum
    have hd : d = 0 := by
      have : d * (a + e) = 0 := by linear_combination hw10
      exact (mul_eq_zero.1 this).resolve_right hsum
    have : (a + e) * (a + e) = 0 := by
      rw [hb, hd] at hw00 hw11 hdW
      linear_combination hw00 + hw11 + 2 * hdW
    exact hsum (mul_self_eq_zero.1 this)
  subst hs he
  have hA : 2 * p * a + q * d + r * b = 0 := by linear_combination ha00
  have h1 : q * m2 = r * m1 := by linear_combination hc00
  have h2' : 2 * p * m1 = q * (m0 - m3) := by linear_combination hc01
  have h3 : r * (m0 - m3) = 2 * p * m2 := by linear_combination hc10
  have hXp : (a * (m0 - m3) + b * m2 + d * m1) * (2 * p) = 0 := by
    linear_combination (m0 - m3) * hA - b * h3 + d * h2'
  have hXq : (a * (m0 - m3) + b * m2 + d * m1) * q = 0 := by
    linear_combination m1 * hA + a * (-1 : F) * h2' + b * h1
  have hXr : (a * (m0 - m3) + b * m2 + d * m1) * r = 0 := by
    linear_combination m2 * hA + a * h3 - d * h1
  have hX : a * (m0 - m3) + b * m2 + d * m1 = 0 := by
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · by_cases hr : r = 0
        · exact absurd ⟨hq, hr, by rw [hp]; ring⟩ hns'
        · exact (mul_eq_zero.1 hXr).resolve_right hr
      · exact (mul_eq_zero.1 hXq).resolve_right hq
    · exact (mul_eq_zero.1 hXp).resolve_right (mul_ne_zero h2 hp)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, hWe, hMe,
    Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-a) * hX + (-m3) * hw00
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-b) * hX + m1 * hw00
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-d) * hX + m2 * hw00
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination a * hX + (-m0) * hw00

end CFSG.GH74.GLS.Stage4.Rest
