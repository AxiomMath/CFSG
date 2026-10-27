module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.Generic.S1.Uni Matrix
  CFSG.GH74.Generic.BProg.B2.GenLocU4Basic CFSG.GH74.Generic.BProg.B2.GenLocU4Out

namespace GenLocU4OutFrDa

section Aux

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_neg_one_sq [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    ∃ i₀ : K, i₀ * i₀ = -1 := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card, hK, pow_two, Nat.mul_mod, hq]
    omega
  obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 hc
  exact ⟨r, hr.symm⟩

theorem core_xy (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0) {i₀ a b c : K}
    (hi₀ : i₀ * i₀ = -1) (hbi₀ : h.bar i₀ = i₀) (ha : h.bar a = -a)
    (hc : h.bar c = -b) (habc : a * a + b * c = -1) :
    ∃ x y : K, h.bar x * x + h.bar y * y = 1 ∧
      h.bar x * (a * x + b * y) + h.bar y * (c * x - a * y) = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have he : 1 + i₀ * a ≠ 0 := by
    intro h0
    have h1 : h.bar (1 + i₀ * a) = 0 := by rw [h0, map_zero]
    rw [map_add, map_mul, map_one, hbi₀, ha] at h1
    apply h2
    linear_combination h0 + h1
  have H3 : (4 * (1 + i₀ * a))⁻¹ * (4 * (1 + i₀ * a)) = 1 := inv_mul_cancel₀ (mul_ne_zero h4 he)
  obtain ⟨s, hs⟩ : ∃ s : K, s * (4 * (1 + i₀ * a)) = 1 := ⟨_, H3⟩
  have H4 : h.bar s * (4 * (1 - i₀ * a)) = 1 := by
    have := congrArg h.bar hs
    simp only [map_mul, map_add, map_one, hbi₀, ha, map_ofNat] at this
    linear_combination this
  have hx : h.bar ((a + i₀) + s * (a - i₀)) = (-a + i₀) + h.bar s * (-a - i₀) := by
    simp only [map_add, map_mul, map_sub, hbi₀, ha]
  have hy : h.bar (c * (1 + s)) = -b * (1 + h.bar s) := by
    simp only [map_add, map_mul, map_one, hc]
  refine ⟨(a + i₀) + s * (a - i₀), c * (1 + s), ?_, ?_⟩
  · rw [hx, hy]
    generalize h.bar s = s' at H4 ⊢
    grind
  · rw [hx, hy]
    generalize h.bar s = s' at H4 ⊢
    grind

theorem exists_two_frame [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {C : Matrix (Fin 2) (Fin 2) K} (hCU : (C.map (· ^ (p ^ f)))ᵀ * C = 1)
    (hC2 : C * C = -1) :
    ∃ V : Matrix (Fin 2) (Fin 2) K, (V.map (· ^ (p ^ f)))ᵀ * V = 1 ∧
      C * V = V * !![0, 1; -1, 0] := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hCs : (C.map (· ^ (p ^ f)))ᵀ = -C := by
    calc (C.map (· ^ (p ^ f)))ᵀ = (C.map (· ^ (p ^ f)))ᵀ * (C * (-C)) := by
          rw [Matrix.mul_neg, hC2, neg_neg, Matrix.mul_one]
      _ = ((C.map (· ^ (p ^ f)))ᵀ * C) * (-C) := by rw [Matrix.mul_assoc]
      _ = -C := by rw [hCU, Matrix.one_mul]
  have e : ∀ i j, C j i ^ (p ^ f) = -C i j := fun i j => by
    have := congrFun (congrFun hCs i) j
    simpa using this
  have htr := GenLocU4ExtBd.tr_zero hq h2 C hC2 hCU
  obtain ⟨i₀, hi₀⟩ := exists_neg_one_sq hK hq
  have hbi₀ : h.bar i₀ = i₀ := GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hi₀
  have hCe : C = !![C 0 0, C 0 1; C 1 0, -C 0 0] := by
    rw [← htr]; exact Matrix.eta_fin_two C
  have ha : h.bar (C 0 0) = -C 0 0 := (UnitaryFieldData.bar_apply h _).trans (e 0 0)
  have hc : h.bar (C 1 0) = -C 0 1 := (UnitaryFieldData.bar_apply h _).trans (e 0 1)
  have hb : h.bar (C 0 1) = -C 1 0 := (UnitaryFieldData.bar_apply h _).trans (e 1 0)
  have habc : C 0 0 * C 0 0 + C 0 1 * C 1 0 = -1 := by
    have := congrFun (congrFun hC2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, htr] using this
  generalize C 0 0 = a at *
  generalize C 0 1 = b at *
  generalize C 1 0 = c at *
  obtain ⟨x, y, hxy1, hxy2⟩ := core_xy h h2 hi₀ hbi₀ ha hc habc
  have hmap : ∀ z : K, z ^ (p ^ f) = h.bar z := fun z => (UnitaryFieldData.bar_apply h z).symm
  refine ⟨!![x, -(a * x + b * y); y, -(c * x - a * y)], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hmap, map_neg, map_add, map_mul, map_sub, ha, hb,
        hc] <;>
      first
        | exact hxy1
        | linear_combination (-1 : K) * hxy2
        | linear_combination hxy2
        | linear_combination hxy1 - (h.bar x * x + h.bar y * y) * habc
  · subst hCe
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | ring1
        | linear_combination (-x) * habc
        | linear_combination (-y) * habc

theorem bd_xi : GenLocU4ExtBd.bd (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) !![0, 1; -1, 0] =
    (xi : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GenLocU4ExtBd.bd, xi]

theorem neg_tT_eq : -(tT : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tT, Matrix.diagonal]

end Aux

theorem exists_da_frame {p f : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {x i : Matrix (Fin 4) (Fin 4) K} (hx : IsUnitaryU (p ^ f) x) (hx2 : x * x = 1)
    (htr : x.trace = 0) (hi : IsUnitaryU (p ^ f) i) (hi2 : i * i = -1) (hxi : x * i = i * x) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧
      (x * U = U * (tT : Matrix (Fin 4) (Fin 4) K) ∨
        x * U = U * (-(tT : Matrix (Fin 4) (Fin 4) K))) ∧
      i * U = U * (xi : Matrix (Fin 4) (Fin 4) K) := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  let xg : GL (Fin 4) K := ⟨x, x, hx2, hx2⟩
  obtain ⟨P, hPU, hxP⟩ := GenLocU4ExtFrame.exists_frame hp hp2 hK xg hx (Units.ext hx2) htr
  set U1 : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K) with hU1
  have hS : cT h U1 * U1 = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h U1).1 hPU
  have hU1S : U1 * cT h U1 = 1 := mul_eq_one_comm.mp hS
  have hxP' : x * U1 = U1 * Matrix.diagonal ![-1, -1, 1, 1] := hxP
  have hiC : cT h i * i = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h i).1 hi
  set i' : Matrix (Fin 4) (Fin 4) K := cT h U1 * i * U1 with hi'
  have hi'U : cT h i' * i' = 1 := by
    rw [hi', cT_mul, cT_mul, cT_cT]
    calc cT h U1 * (cT h i * U1) * (cT h U1 * i * U1)
        = cT h U1 * cT h i * (U1 * cT h U1) * i * U1 := by simp only [Matrix.mul_assoc]
      _ = cT h U1 * (cT h i * i) * U1 := by
        rw [hU1S, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hiC, Matrix.mul_one, hS]
  have hi'2 : i' * i' = -1 := by
    calc i' * i' = cT h U1 * (i * (U1 * cT h U1) * i) * U1 := by
          rw [hi']; simp only [Matrix.mul_assoc]
      _ = -1 := by
        rw [hU1S, Matrix.mul_one, hi2, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hS]
  have hSx : cT h U1 * x = Matrix.diagonal ![-1, -1, 1, 1] * cT h U1 := by
    calc cT h U1 * x = cT h U1 * x * (U1 * cT h U1) := by rw [hU1S, Matrix.mul_one]
      _ = cT h U1 * (x * U1) * cT h U1 := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal ![-1, -1, 1, 1] * cT h U1 := by
        rw [hxP', ← Matrix.mul_assoc (cT h U1), hS, Matrix.one_mul]
  have hi'D : i' * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * i' := by
    calc i' * Matrix.diagonal ![-1, -1, 1, 1]
        = cT h U1 * i * (U1 * Matrix.diagonal ![-1, -1, 1, 1]) := by
          rw [hi']; simp only [Matrix.mul_assoc]
      _ = cT h U1 * i * (x * U1) := by rw [hxP']
      _ = (cT h U1 * x) * i * U1 := by
          rw [← Matrix.mul_assoc, Matrix.mul_assoc (cT h U1) i x, ← hxi]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal ![-1, -1, 1, 1] * i' := by
          rw [hSx, hi']; simp only [Matrix.mul_assoc]
  obtain ⟨B, B', hBB'⟩ := GenLocU4ExtBd.exists_bd_of_comm h2 i' hi'D
  have hbd_neg_one : (-1 : Matrix (Fin 4) (Fin 4) K) = GenLocU4ExtBd.bd (-1) (-1) := by
    rw [← GenLocU4ExtBd.bd_one, GenLocU4ExtBd.bd_neg]
  have hsq : GenLocU4ExtBd.bd (B * B) (B' * B') = GenLocU4ExtBd.bd (-1) (-1) := by
    rw [← GenLocU4ExtBd.bd_mul, ← hBB', hi'2, hbd_neg_one]
  obtain ⟨hBsq, hB'sq⟩ := GenLocU4ExtBd.bd_inj hsq
  have hiU' : IsUnitaryU (p ^ f) i' := (GenLocU4OutFrame.isUnitaryU_iff_cT h i').2 hi'U
  have hunit : GenLocU4ExtBd.bd ((B.map (· ^ (p ^ f)))ᵀ * B) ((B'.map (· ^ (p ^ f)))ᵀ * B') =
      GenLocU4ExtBd.bd 1 1 := by
    rw [← GenLocU4ExtBd.bd_unitary hq0, ← hBB', GenLocU4ExtBd.bd_one]
    exact hiU'
  obtain ⟨hBU, hB'U⟩ := GenLocU4ExtBd.bd_inj hunit
  obtain ⟨V, hVU, hBV⟩ := exists_two_frame hp hp2 hK hq hBU hBsq
  obtain ⟨V', hV'U, hBV'⟩ := exists_two_frame hp hp2 hK hq hB'U hB'sq
  set U2 : Matrix (Fin 4) (Fin 4) K := GenLocU4ExtBd.bd V V' with hU2
  have hU2U : IsUnitaryU (p ^ f) U2 := by
    show (U2.map (· ^ (p ^ f)))ᵀ * U2 = 1
    rw [hU2, GenLocU4ExtBd.bd_unitary hq0, hVU, hV'U, GenLocU4ExtBd.bd_one]
  have hU2c : cT h U2 * U2 = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h U2).1 hU2U
  have hU2D : U2 * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * U2 := by
    rw [GenLocU4ExtBd.diag_eq_bd, hU2, GenLocU4ExtBd.bd_mul, GenLocU4ExtBd.bd_mul]
    simp
  refine ⟨U1 * U2, ?_, Or.inr ?_, ?_⟩
  · apply (GenLocU4OutFrame.isUnitaryU_iff_cT h _).2
    rw [cT_mul]
    calc cT h U2 * cT h U1 * (U1 * U2) = cT h U2 * (cT h U1 * U1) * U2 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, Matrix.mul_one, hU2c]
  · rw [neg_tT_eq]
    calc x * (U1 * U2) = (x * U1) * U2 := by rw [Matrix.mul_assoc]
      _ = U1 * (Matrix.diagonal ![-1, -1, 1, 1] * U2) := by rw [hxP', Matrix.mul_assoc]
      _ = U1 * (U2 * Matrix.diagonal ![-1, -1, 1, 1]) := by rw [hU2D]
      _ = U1 * U2 * Matrix.diagonal ![-1, -1, 1, 1] := by rw [Matrix.mul_assoc]
  · have hiU1 : i * U1 = U1 * i' := by
      calc i * U1 = (U1 * cT h U1) * i * U1 := by rw [hU1S, Matrix.one_mul]
        _ = U1 * i' := by rw [hi']; simp only [Matrix.mul_assoc]
    calc i * (U1 * U2) = (i * U1) * U2 := by rw [Matrix.mul_assoc]
      _ = U1 * (i' * U2) := by rw [hiU1, Matrix.mul_assoc]
      _ = U1 * (U2 * xi) := by
          rw [hBB', hU2, GenLocU4ExtBd.bd_mul, hBV, hBV', ← bd_xi, GenLocU4ExtBd.bd_mul]
      _ = U1 * U2 * xi := by rw [Matrix.mul_assoc]

end GenLocU4OutFrDa

end CFSG.GH74.Generic.BProg.B2
