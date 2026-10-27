module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Transfer
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

section Field

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra hc
  push Not at hc
  have h3 : ({0, 1, c} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hc.1.symm]), Finset.card_pair hc.2.symm]
  have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem one_add_one_eq_zero_of_card_two (hK : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  rcases eq_zero_or_eq_one_of_card_two hK ((1 : K) + 1) with h | h
  · exact h
  · exfalso
    have : (1 : K) = 0 := by
      calc (1 : K) = (1 + 1) - 1 := by ring
        _ = 0 := by rw [h, sub_self]
    exact one_ne_zero this

theorem coe_uSL (c : K) : ((uSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem coe_vSL (c : K) : ((vSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem coe_uv : ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 1; 0, 1] * !![1, 0; 1, 1] := rfl

theorem coe_vu : ((vSL (1 : K) * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; 1, 1] * !![1, 1; 0, 1] := rfl

theorem sl2_eq_uv_or_vu (hK : Nat.card K = 2) (B : SL2 K) (h3 : B ^ 3 = 1) (h1 : B ≠ 1) :
    B = uSL 1 * vSL 1 ∨ B = vSL 1 * uSL 1 := by
  have h2 := one_add_one_eq_zero_of_card_two hK
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hdet : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
  rw [Matrix.det_fin_two] at hdet
  have e00 : ((B ^ 3 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by rw [h3]; rfl
  have e01 : ((B ^ 3 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by rw [h3]; rfl
  have e10 : ((B ^ 3 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by rw [h3]; rfl
  simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at e00 e01 e10
  have hB : ∀ M : SL2 K, (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 →
      (M : Matrix (Fin 2) (Fin 2) K) 0 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 1 →
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 = (B : Matrix (Fin 2) (Fin 2) K) 1 0 →
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 1 1 → B = M := by
    intro M h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00.symm
    · exact h01.symm
    · exact h10.symm
    · exact h11.symm
  have huv : ∀ i j, ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      !![0, 1; 1, 1] i j := by
    intro i j
    rw [coe_uv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  have hvu : ∀ i j, ((vSL (1 : K) * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      !![1, 1; 1, 0] i j := by
    intro i j
    rw [coe_vu]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 0 0) with ha | ha <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 0 1) with hb | hb <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 1 0) with hc | hc <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 1 1) with hd | hd <;>
  simp only [ha, hb, hc, hd, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
    zero_sub, sub_self, h2] at hdet e00 e01 e10
  all_goals first
    | exact absurd hdet.symm h10
    | exact absurd e01 h10
    | exact absurd e10 h10
    | exact absurd e00.symm h10
    | skip
  all_goals first
    | exact Or.inl (hB _ (by rw [huv, ha]; rfl) (by rw [huv, hb]; rfl) (by rw [huv, hc]; rfl)
        (by rw [huv, hd]; rfl))
    | exact Or.inr (hB _ (by rw [hvu, ha]; rfl) (by rw [hvu, hb]; rfl) (by rw [hvu, hc]; rfl)
        (by rw [hvu, hd]; rfl))
    | exact absurd (hB 1 (by rw [ha]; rfl) (by rw [hb]; rfl) (by rw [hc]; rfl) (by rw [hd]; rfl))
        h1

theorem sl2_sq_eq_one_or (hK : Nat.card K = 2) (B : SL2 K) :
    B * B = 1 ∨ B = uSL 1 * vSL 1 ∨ B = vSL 1 * uSL 1 := by
  by_cases h1 : B = 1
  · exact Or.inl (by rw [h1, one_mul])
  by_cases hsq : B * B = 1
  · exact Or.inl hsq
  have h2 := one_add_one_eq_zero_of_card_two hK
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hdet : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
  rw [Matrix.det_fin_two] at hdet
  have hB : ∀ M : SL2 K, (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 →
      (M : Matrix (Fin 2) (Fin 2) K) 0 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 1 →
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 = (B : Matrix (Fin 2) (Fin 2) K) 1 0 →
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 1 1 → B = M := by
    intro M h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00.symm
    · exact h01.symm
    · exact h10.symm
    · exact h11.symm
  have hsqB : ∀ i j, ((B * B : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      ∑ k, (B : Matrix (Fin 2) (Fin 2) K) i k * (B : Matrix (Fin 2) (Fin 2) K) k j := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have hsq1 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 →
      (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 →
      (B : Matrix (Fin 2) (Fin 2) K) 1 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
      (B : Matrix (Fin 2) (Fin 2) K) 1 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (B : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → False := by
    intro e00 e01 e10 e11
    apply hsq
    ext i j
    rw [hsqB, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · simpa using e00
    · simpa using e01
    · simpa using e10
    · simpa using e11
  have huv : ∀ i j, ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      !![0, 1; 1, 1] i j := by
    intro i j
    rw [coe_uv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  have hvu : ∀ i j, ((vSL (1 : K) * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      !![1, 1; 1, 0] i j := by
    intro i j
    rw [coe_vu]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 0 0) with ha | ha <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 0 1) with hb | hb <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 1 0) with hc | hc <;>
  rcases eq_zero_or_eq_one_of_card_two hK ((B : Matrix (Fin 2) (Fin 2) K) 1 1) with hd | hd <;>
  simp only [ha, hb, hc, hd, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
    zero_sub, sub_self, h2] at hdet hsq1
  all_goals first
    | exact absurd hdet.symm h10
    | exact (hsq1 trivial trivial trivial trivial).elim
    | exact Or.inr (Or.inl (hB _ (by rw [huv, ha]; rfl) (by rw [huv, hb]; rfl)
        (by rw [huv, hc]; rfl) (by rw [huv, hd]; rfl)))
    | exact Or.inr (Or.inr (hB _ (by rw [hvu, ha]; rfl) (by rw [hvu, hb]; rfl)
        (by rw [hvu, hc]; rfl) (by rw [hvu, hd]; rfl)))
    | exact absurd (hB 1 (by rw [ha]; rfl) (by rw [hb]; rfl) (by rw [hc]; rfl) (by rw [hd]; rfl))
        h1

theorem vu_inv (hK : Nat.card K = 2) : (vSL (1 : K) * uSL 1)⁻¹ = uSL 1 * vSL 1 := by
  have h2 := one_add_one_eq_zero_of_card_two hK
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem conj_w_uv (hK : Nat.card K = 2) :
    (uSL (1 : K) * vSL 1 * uSL 1) * (uSL 1 * vSL 1) * (uSL 1 * vSL 1 * uSL 1)⁻¹ =
      vSL 1 * uSL 1 := by
  have h2 := one_add_one_eq_zero_of_card_two hK
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h2, ← add_assoc]

end Field

section Conj


variable {K : Type} [Field K]

theorem conj_gammaP (B C : SL2 K) :
    MulAut.conj (sl2At K ⟨2, by decide⟩ C) * gammaP K B *
        (MulAut.conj (sl2At K ⟨2, by decide⟩ C))⁻¹ = gammaP K (C * B * C⁻¹) := by
  rw [gammaP, gammaP, ← map_inv, mul_assoc, mul_assoc, mul_conj_eq, map_inv, d4Graph_one_sl2Two,
    ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← map_inv (sl2At K _) C, ← map_mul,
    ← map_mul]

end Conj

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
