module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F]

@[expose] def uFiveZeta (d : F) : unitriangular 5 F :=
  uFiveRoot 0 4 (by decide) d

@[expose] def uFiveBeta (e y : F) : unitriangular 5 F :=
  uFiveElt (single 0 2 y + single 1 4 (-e * y))
    ((isStrictUpperFive_single (by decide) y).add (isStrictUpperFive_single (by decide) _))

@[expose] def uFiveAlpha (e a : F) : unitriangular 5 F :=
  uFiveElt (single 0 1 a + single 2 4 (e * a))
    ((isStrictUpperFive_single (by decide) a).add (isStrictUpperFive_single (by decide) _))

theorem ypsMat_uFiveZeta (d : F) : ypsMat (uFiveZeta d) = 1 + single 0 4 d := rfl

theorem ypsMat_uFiveBeta (e y : F) :
    ypsMat (uFiveBeta e y) = 1 + (single 0 2 y + single 1 4 (-e * y)) := rfl

theorem ypsMat_uFiveAlpha (e a : F) :
    ypsMat (uFiveAlpha e a) = 1 + (single 0 1 a + single 2 4 (e * a)) := rfl

theorem ypsMat_uFiveBeta_eq (e y : F) :
    ypsMat (uFiveBeta e y) = !![1, 0, y, 0, 0; 0, 1, 0, 0, -e * y; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := by
  rw [ypsMat_uFiveBeta]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ypsMat_mul_uFiveZeta (u : unitriangular 5 F) (w : F) :
    ypsMat (u * uFiveZeta w) = ypsMat u + single 0 4 w := by
  rw [ypsMat_mul, ypsMat_uFiveZeta, ypsMat_eq u]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem uFiveZeta_comm (g : unitriangular 5 F) (d : F) : g * uFiveZeta d = uFiveZeta d * g := by
  apply ypsMat_injective
  rw [ypsMat_mul_uFiveZeta, ypsMat_mul, ypsMat_uFiveZeta, ypsMat_eq g]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five]

theorem uFiveZeta_zero : uFiveZeta (0 : F) = 1 :=
  ypsMat_injective (by rw [ypsMat_uFiveZeta, single_zero, add_zero, ypsMat_one])

section Finite

variable [Finite F]

theorem uFiveZeta_mem (e d : F) : uFiveZeta d ∈ uFiveTwisted e := by
  rw [mem_uFiveTwisted, ypsMat_uFiveZeta]
  simp

theorem uFiveBeta_mem (e y : F) : uFiveBeta e y ∈ uFiveTwisted e := by
  rw [mem_uFiveTwisted, ypsMat_uFiveBeta]
  simp

theorem uFiveAlpha_mem (e a : F) : uFiveAlpha e a ∈ uFiveTwisted e := by
  rw [mem_uFiveTwisted, ypsMat_uFiveAlpha]
  simp

theorem uFiveRoot24_conj {e : F} {z : unitriangular 5 F} (hz : z ∈ uFiveTwisted e) (r : F) :
    uFiveRoot 2 4 (by decide) r * z * (uFiveRoot 2 4 (by decide) r)⁻¹ =
      z * uFiveZeta (-r * ypsMat z 0 2) := by
  obtain ⟨h12, h13, h23, h34, h14, h24⟩ := hz
  rw [mul_inv_eq_iff_eq_mul]
  apply ypsMat_injective
  rw [ypsMat_mul, ypsMat_mul, ypsMat_mul_uFiveZeta, ypsMat_uFiveRoot]
  rw [ypsMat_eq z, h12, h13, h23, h34, h14, h24]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five] <;> ring

theorem uFiveRoot12_conj {e : F} {z : unitriangular 5 F} (hz : z ∈ uFiveTwisted e) (s : F) :
    uFiveRoot 1 2 (by decide) s * z * (uFiveRoot 1 2 (by decide) s)⁻¹ =
      z * uFiveBeta e (-s * ypsMat z 0 1) * uFiveZeta (-s * e * ypsMat z 0 1 ^ 2) := by
  obtain ⟨h12, h13, h23, h34, h14, h24⟩ := hz
  rw [mul_inv_eq_iff_eq_mul]
  apply ypsMat_injective
  rw [ypsMat_mul, ypsMat_mul, ypsMat_mul_uFiveZeta, ypsMat_mul, ypsMat_uFiveRoot,
    ypsMat_uFiveBeta_eq]
  rw [ypsMat_eq z, h12, h13, h23, h34, h14, h24]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five] <;> ring

theorem eq_uFiveZeta_of_comm {e : F} {z : unitriangular 5 F} (hz : z ∈ uFiveTwisted e)
    (h1 : z * uFiveRoot 1 2 (by decide) 1 = uFiveRoot 1 2 (by decide) 1 * z)
    (h2 : z * uFiveRoot 2 3 (by decide) 1 = uFiveRoot 2 3 (by decide) 1 * z)
    (h3 : z * uFiveRoot 3 4 (by decide) 1 = uFiveRoot 3 4 (by decide) 1 * z) :
    z = uFiveZeta (ypsMat z 0 4) := by
  obtain ⟨h12, h13, h23, h34, h14, h24⟩ := hz
  have e1 := congrArg (fun u => ypsMat u 0 2) h1
  have e2 := congrArg (fun u => ypsMat u 0 3) h2
  have e3 := congrArg (fun u => ypsMat u 0 4) h3
  simp only [ypsMat_mul, ypsMat_uFiveRoot] at e1 e2 e3
  rw [ypsMat_eq z] at e1 e2 e3
  simp [Matrix.mul_apply, Fin.sum_univ_five] at e1 e2 e3
  apply ypsMat_injective
  rw [ypsMat_uFiveZeta, ypsMat_eq z, h12, h13, h23, h34, h14, h24, e1, e2, e3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem not_exists_fixedPointFree_equivariant_uFiveTwisted {e : F} (he : e ≠ 0) {t : F}
    (ht : t * t ≠ t) (τ : uFiveTwisted e ≃* uFiveTwisted e)
    (hτ : ∀ (g : unitriangular 5 F) (x y : uFiveTwisted e),
      (y : unitriangular 5 F) = g * x * g⁻¹ → (τ y : unitriangular 5 F) = g * τ x * g⁻¹)
    (hfix : ∀ x, τ x = x → x = 1) : False := by
  let ζX : F → uFiveTwisted e := fun d => ⟨uFiveZeta d, uFiveZeta_mem e d⟩
  let βX : F → uFiveTwisted e := fun y => ⟨uFiveBeta e y, uFiveBeta_mem e y⟩
  let αX : F → uFiveTwisted e := fun a => ⟨uFiveAlpha e a, uFiveAlpha_mem e a⟩
  let f : F → F := fun d => ypsMat ((τ (ζX d) : uFiveTwisted e) : unitriangular 5 F) 0 4
  have hA : ∀ d, ((τ (ζX d) : uFiveTwisted e) : unitriangular 5 F) = uFiveZeta (f d) := by
    intro d
    have hc : ∀ g : unitriangular 5 F, ((τ (ζX d) : uFiveTwisted e) : unitriangular 5 F) * g =
        g * (τ (ζX d) : uFiveTwisted e) := by
      intro g
      have h := hτ g (ζX d) (ζX d) (by
        change uFiveZeta d = g * uFiveZeta d * g⁻¹
        rw [uFiveZeta_comm g d, mul_inv_cancel_right])
      nth_rewrite 1 [h]
      group
    exact eq_uFiveZeta_of_comm (τ (ζX d)).2 (hc _) (hc _) (hc _)
  have hB : ∀ r y, f (-r * y) =
      -r * ypsMat ((τ (βX y) : uFiveTwisted e) : unitriangular 5 F) 0 2 := by
    intro r y
    have hw : ((βX y * ζX (-r * y) : uFiveTwisted e) : unitriangular 5 F) =
        uFiveRoot 2 4 (by decide) r * (βX y : unitriangular 5 F) *
          (uFiveRoot 2 4 (by decide) r)⁻¹ := by
      change uFiveBeta e y * uFiveZeta (-r * y) = _
      rw [uFiveRoot24_conj (uFiveBeta_mem e y) r,
        show ypsMat (uFiveBeta e y) 0 2 = y by rw [ypsMat_uFiveBeta_eq]; simp]
    have h := hτ _ (βX y) _ hw
    rw [map_mul, Subgroup.coe_mul, hA, uFiveRoot24_conj (τ (βX y)).2 r] at h
    have h2 := congrArg (fun u => ypsMat u 0 4) (mul_left_cancel h)
    simpa [ypsMat_uFiveZeta] using h2
  have hB1 : ∀ y, ypsMat ((τ (βX y) : uFiveTwisted e) : unitriangular 5 F) 0 2 = f y := by
    intro y
    have h := hB (-1) y
    simp only [neg_neg, one_mul] at h
    exact h.symm
  have hlin : ∀ c, f c = c * f 1 := by
    intro c
    have h := hB (-c) 1
    rw [hB1 1] at h
    simpa using h
  have hC : ∀ s a, ypsMat ((τ (βX (-s * a)) : uFiveTwisted e) : unitriangular 5 F) 0 2 =
      -s * ypsMat ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F) 0 1 ∧
      ypsMat ((τ (βX (-s * a)) : uFiveTwisted e) : unitriangular 5 F) 0 4 + f (-s * e * a ^ 2) =
        -s * e * ypsMat ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F) 0 1 ^ 2 := by
    intro s a
    have hw : ((αX a * βX (-s * a) * ζX (-s * e * a ^ 2) : uFiveTwisted e) :
        unitriangular 5 F) = uFiveRoot 1 2 (by decide) s * (αX a : unitriangular 5 F) *
          (uFiveRoot 1 2 (by decide) s)⁻¹ := by
      change uFiveAlpha e a * uFiveBeta e (-s * a) * uFiveZeta (-s * e * a ^ 2) = _
      rw [uFiveRoot12_conj (uFiveAlpha_mem e a) s,
        show ypsMat (uFiveAlpha e a) 0 1 = a by rw [ypsMat_uFiveAlpha]; simp]
    have h := hτ _ (αX a) _ hw
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hA,
      uFiveRoot12_conj (τ (αX a)).2 s] at h
    have h' : ((τ (βX (-s * a)) : uFiveTwisted e) : unitriangular 5 F) *
        uFiveZeta (f (-s * e * a ^ 2)) =
          uFiveBeta e (-s * ypsMat ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F) 0 1) *
            uFiveZeta (-s * e *
              ypsMat ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F) 0 1 ^ 2) := by
      apply mul_left_cancel (a := ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F))
      rw [← mul_assoc, ← mul_assoc]
      exact h
    have e2 := congrArg (fun u => ypsMat u 0 2) h'
    have e4 := congrArg (fun u => ypsMat u 0 4) h'
    simp only [ypsMat_mul_uFiveZeta, ypsMat_uFiveBeta_eq] at e2 e4
    exact ⟨by simpa using e2, by simpa using e4⟩
  have hα : ∀ a, ypsMat ((τ (αX a) : uFiveTwisted e) : unitriangular 5 F) 0 1 = f 1 * a := by
    intro a
    have h := (hC 1 a).1
    rw [hB1, hlin] at h
    linear_combination h
  have hμ : ∀ s a, ypsMat ((τ (βX (-s * a)) : uFiveTwisted e) : unitriangular 5 F) 0 4 =
      s * e * a ^ 2 * (f 1 - f 1 ^ 2) := by
    intro s a
    have h := (hC s a).2
    rw [hα, hlin] at h
    linear_combination h
  have h1 := hμ t 1
  have h2 := hμ 1 t
  simp only [mul_one, neg_mul, one_mul, one_pow] at h1 h2
  have hκ : f 1 - f 1 ^ 2 = 0 := by
    have h3 : e * (f 1 - f 1 ^ 2) * (t - t * t) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact (mul_eq_zero.1 h).resolve_left he
    · exact absurd (sub_eq_zero.1 h).symm ht
  have hζ1 : ζX 1 ≠ 1 := by
    intro h
    have h' := congrArg (fun u : uFiveTwisted e => ypsMat (u : unitriangular 5 F) 0 4) h
    simp [ζX, ypsMat_uFiveZeta, ypsMat_one] at h'
  have hκ' : f 1 * (1 - f 1) = 0 := by linear_combination hκ
  rcases mul_eq_zero.1 hκ' with h0 | h0
  · apply hζ1
    apply τ.injective
    rw [map_one]
    apply Subtype.ext
    rw [hA 1, h0, uFiveZeta_zero]
    rfl
  · apply hζ1
    apply hfix
    apply Subtype.ext
    rw [hA 1, show f 1 = 1 from (sub_eq_zero.1 h0).symm]

end Finite

end CFSG.SeitzReduction.LinearPilot
