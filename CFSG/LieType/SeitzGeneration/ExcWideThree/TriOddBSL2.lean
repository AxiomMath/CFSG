module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec19

theorem triOdd_sl2_conj_hsl {K : Type} [Field K] (t : Kˣ) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 2) K, P * M * P⁻¹ = HSL t := by
  have hω3 : (t : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ht3
    simpa using this
  have hω1 : (t : K) ≠ 1 := fun h => ht1 (Units.ext h)
  have hωω' : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t
  have hq : (t : K) ^ 2 + (t : K) + 1 = 0 := by
    have h : ((t : K) - 1) * ((t : K) ^ 2 + (t : K) + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hq' : ((t⁻¹ : Kˣ) : K) ^ 2 + ((t⁻¹ : Kˣ) : K) + 1 = 0 := by
    linear_combination ((t⁻¹ : Kˣ) : K) ^ 2 * hq -
      ((t : K) * ((t⁻¹ : Kˣ) : K) + 1 + ((t⁻¹ : Kˣ) : K)) * hωω'
  have hδ : (t : K) - ((t⁻¹ : Kˣ) : K) ≠ 0 := by
    intro h
    have h' : ((t⁻¹ : Kˣ) : K) = (t : K) := (sub_eq_zero.mp h).symm
    rw [h'] at hωω'
    exact hω1 (by linear_combination ((t : K) - 1) * (hq - hωω') - hωω')
  have hMq := sl2_cube_quad hM3 hM1
  obtain ⟨a, b, c, d, hMe⟩ : ∃ a b c d : K, (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h : (M : Matrix (Fin 2) (Fin 2) K).det = 1 := M.2
    rw [hMe, Matrix.det_fin_two_of] at h
    exact h
  rw [hMe] at hMq
  have e00 := congrFun (congrFun hMq 0) 0
  have e01 := congrFun (congrFun hMq 0) 1
  have e10 := congrFun (congrFun hMq 1) 0
  have e11 := congrFun (congrFun hMq 1) 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have F1 : ∀ x₁ x₂ : K,
      a * (a * x₁ + b * x₂) + b * (c * x₁ + d * x₂) + (a * x₁ + b * x₂) + x₁ = 0 := fun x₁ x₂ => by
    linear_combination x₁ * e00 + x₂ * e01
  have F2 : ∀ x₁ x₂ : K,
      c * (a * x₁ + b * x₂) + d * (c * x₁ + d * x₂) + (c * x₁ + d * x₂) + x₂ = 0 := fun x₁ x₂ => by
    linear_combination x₁ * e10 + x₂ * e11
  have hex : ∃ x₁ x₂ : K, x₁ * (c * x₁ + d * x₂) - x₂ * (a * x₁ + b * x₂) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : c = 0 := by simpa using hall 1 0
    have h2 : b = 0 := by simpa using hall 0 1
    have h3 := hall 1 1
    have h4 : d = a := by linear_combination h3 - h1 + h2
    subst h1 h2
    have hdet' : a * a = 1 := by linear_combination hdet - a * h4
    have ha : a = 1 := by linear_combination (a - 1) * (e00 - hdet') - hdet'
    have hd1 : d = 1 := by rw [h4, ha]
    subst ha hd1
    apply hM1
    apply Subtype.ext
    rw [hMe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  have key : ∀ (ω ω' : K), ω ^ 2 + ω + 1 = 0 → ω' ^ 2 + ω' + 1 = 0 → ω - ω' ≠ 0 →
      ∃ Q : Matrix.SpecialLinearGroup (Fin 2) K,
        (M : Matrix (Fin 2) (Fin 2) K) * (Q : Matrix (Fin 2) (Fin 2) K) =
          (Q : Matrix (Fin 2) (Fin 2) K) * !![ω, 0; 0, ω'] := by
    intro ω ω' hq hq' hδ
    obtain ⟨x₁, x₂, hr⟩ := hex
    obtain ⟨s, hs⟩ : ∃ s : K,
        s * ((ω - ω') * (x₁ * (c * x₁ + d * x₂) - x₂ * (a * x₁ + b * x₂))) = 1 :=
      ⟨_, inv_mul_cancel₀ (mul_ne_zero hδ hr)⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Matrix.SpecialLinearGroup (Fin 2) K,
        (Q : Matrix (Fin 2) (Fin 2) K) =
          !![x₁ - ω * (a * x₁ + b * x₂), s * (x₁ - ω' * (a * x₁ + b * x₂));
             x₂ - ω * (c * x₁ + d * x₂), s * (x₂ - ω' * (c * x₁ + d * x₂))] :=
      ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination hs⟩, rfl⟩
    refine ⟨Q, ?_⟩
    rw [hQ, hMe]
    have g1 := F1 x₁ x₂
    have g2 := F2 x₁ x₂
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-ω) * g1 + (a * x₁ + b * x₂) * hq
    · linear_combination (-s * ω') * g1 + s * (a * x₁ + b * x₂) * hq'
    · linear_combination (-ω) * g2 + (c * x₁ + d * x₂) * hq
    · linear_combination (-s * ω') * g2 + s * (c * x₁ + d * x₂) * hq'
  obtain ⟨Q, hQ⟩ := key (t : K) ((t⁻¹ : Kˣ) : K) hq hq' hδ
  refine ⟨Q⁻¹, ?_⟩
  have hMQ : M * Q = Q * HSL t := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_HSL]
    exact hQ
  rw [inv_inv, mul_assoc, hMQ, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.LieType.SeitzGeneration.ExcWideThree

