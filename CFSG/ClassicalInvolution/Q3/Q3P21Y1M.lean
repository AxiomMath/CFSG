module

public import CFSG.ClassicalInvolution.Q3.Q3P21S5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.RouteD.SU4Pattern
open scoped MatrixGroups

section Two

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su2_commutant_scalar (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 4 = 3) {C : Matrix (Fin 2) (Fin 2) K}
    (hC : ∀ b : Su K p f 2, C * suMat b = suMat b * C) : ∃ c : K, C = c • 1 := by
  obtain ⟨ι, hι, hσι⟩ := exists_sqrt_neg_one_three hK hq3
  set σ := unitaryInvolution K p f with hσ
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have hσ1 : σ (-1) = -1 := by rw [map_neg, map_one]
  have hdU : (!![ι, 0; 0, -ι] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [det_fin_two_of]
    linear_combination (-1 : K) * hι
  have hiU : conjTr σ (!![ι, 0; 0, -ι] : Matrix (Fin 2) (Fin 2) K) *
      (!![ι, 0; 0, -ι] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσι, map_neg] <;>
      linear_combination (-1 : K) * hι
  have hdV : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [det_fin_two_of]
    ring
  have hiV : conjTr σ (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσ1]
  have hU := hC (Models.mkSU K p f _ hdU hiU)
  have hV := hC (Models.mkSU K p f _ hdV hiV)
  rw [suMat_mkSU] at hU hV
  have u01 := congrFun (congrFun hU 0) 1
  have u10 := congrFun (congrFun hU 1) 0
  have v00 := congrFun (congrFun hV 0) 0
  have v01 := congrFun (congrFun hV 0) 1
  have v10 := congrFun (congrFun hV 1) 0
  have v11 := congrFun (congrFun hV 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at u01 u10 v00 v01 v10 v11
  have hc01 : C 0 1 = 0 := by
    have : C 0 1 * (2 * ι) = 0 := by linear_combination -u01
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h2 hι0)
  have hc10 : C 1 0 = 0 := by
    have : C 1 0 * (2 * ι) = 0 := by linear_combination u10
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h2 hι0)
  refine ⟨C 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc01, hc10]
  linear_combination -v01

theorem blockMat_two_eq_BD (Y : Matrix (Fin 2) (Fin 2) K) : blockMat 4 2 Y = BD 1 Y := by
  rw [BD, blockMat_one, Matrix.one_mul]

theorem eq_BD_of_comm_negBlock (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 4) (Fin 4) K}
    (hn : M * BD (-1) 1 = BD (-1) 1 * M) : ∃ P Q : Matrix (Fin 2) (Fin 2) K, M = BD P Q := by
  have e02 := congrFun (congrFun hn 0) 2
  have e03 := congrFun (congrFun hn 0) 3
  have e12 := congrFun (congrFun hn 1) 2
  have e13 := congrFun (congrFun hn 1) 3
  have e20 := congrFun (congrFun hn 2) 0
  have e21 := congrFun (congrFun hn 2) 1
  have e30 := congrFun (congrFun hn 3) 0
  have e31 := congrFun (congrFun hn 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, BD_eq] at e02 e03 e12 e13 e20 e21 e30 e31
  have half : ∀ x : K, x = -x → x = 0 := fun x hx => by
    have : x * 2 = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_right h2
  have z02 : M 0 2 = 0 := half _ e02
  have z03 : M 0 3 = 0 := half _ e03
  have z12 : M 1 2 = 0 := half _ e12
  have z13 : M 1 3 = 0 := half _ e13
  have z20 : M 2 0 = 0 := half _ e20.symm
  have z21 : M 2 1 = 0 := half _ e21.symm
  have z30 : M 3 0 = 0 := half _ e30.symm
  have z31 : M 3 1 = 0 := half _ e31.symm
  refine ⟨!![M 0 0, M 0 1; M 1 0, M 1 1], !![M 2 2, M 2 3; M 3 2, M 3 3], ?_⟩
  rw [BD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z02, z03, z12, z13, z20, z21, z30, z31]

theorem commutant_blockZero (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3)
    {M : Matrix (Fin 4) (Fin 4) K}
    (hM : ∀ b : Su K p f 2, M * blockMat 4 0 (suMat b) = blockMat 4 0 (suMat b) * M) :
    ∃ (c : K) (D : Matrix (Fin 2) (Fin 2) K), M = BD (c • 1) D := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  have hn := hM (negOneSU K p f)
  rw [suMat_negOneSU, blockMat_zero_eq_BD] at hn
  obtain ⟨P, Q, rfl⟩ := eq_BD_of_comm_negBlock h2 hn
  have hPc : ∀ b : Su K p f 2, P * suMat b = suMat b * P := by
    intro b
    have := hM b
    rw [blockMat_zero_eq_BD, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact (BD_inj this).1
  obtain ⟨c, hc⟩ := su2_commutant_scalar hK hp2 hq3 hPc
  exact ⟨c, Q, by rw [hc]⟩

theorem det_smul_map_of_unitary {σ : K ≃+* K} {H : Matrix (Fin 2) (Fin 2) K}
    (hH : conjTr σ H * H = 1) :
    H.det • H.map σ = !![0, 1; -1, 0] * H * !![0, -1; 1, 0] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, H = !![a, b; c, d] :=
    ⟨H 0 0, H 0 1, H 1 0, H 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have e00 := congrFun (congrFun hH 0) 0
  have e01 := congrFun (congrFun hH 0) 1
  have e10 := congrFun (congrFun hH 1) 0
  have e11 := congrFun (congrFun hH 1) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [det_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination d * e00 - c * e01
  · linear_combination d * e10 - c * e11
  · linear_combination -b * e00 + a * e01
  · linear_combination -b * e10 + a * e11

theorem map_BD (σ : K ≃+* K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    (BD X Y).map σ = BD (X.map σ) (Y.map σ) := by
  rw [BD_eq, BD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem jInv_mul_j : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem j_mul_jInv : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_suMat_eq (b : Su K p f 2) :
    (suMat b).map (unitaryInvolution K p f) = !![0, 1; -1, 0] * suMat b * !![0, -1; 1, 0] := by
  have h1 := det_smul_map_of_unitary (σ := unitaryInvolution K p f) (H := suMat b) b.2.2
  have hd : (suMat b).det = 1 := b.2.1
  rw [hd, one_smul] at h1
  exact h1

theorem twisted_scalar (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3)
    {P : Matrix (Fin 2) (Fin 2) K}
    (hP : ∀ b : Su K p f 2, P * (suMat b).map (unitaryInvolution K p f) = suMat b * P) :
    ∃ l : K, P = l • !![0, -1; 1, 0] := by
  have hc : ∀ b : Su K p f 2,
      (P * !![0, 1; -1, 0]) * suMat b = suMat b * (P * !![0, 1; -1, 0]) := by
    intro b
    have := hP b
    rw [map_suMat_eq] at this
    calc P * !![0, 1; -1, 0] * suMat b
        = P * (!![0, 1; -1, 0] * suMat b * !![0, -1; 1, 0]) * !![0, 1; -1, 0] := by
          simp only [Matrix.mul_assoc, jInv_mul_j, Matrix.mul_one]
      _ = suMat b * P * !![0, 1; -1, 0] := by rw [this]
      _ = suMat b * (P * !![0, 1; -1, 0]) := by rw [Matrix.mul_assoc]
  obtain ⟨l, hl⟩ := su2_commutant_scalar hK hp2 hq3 hc
  refine ⟨l, ?_⟩
  calc P = P * !![0, 1; -1, 0] * !![0, -1; 1, 0] := by
        rw [Matrix.mul_assoc, j_mul_jInv, Matrix.mul_one]
    _ = l • !![0, -1; 1, 0] := by rw [hl, Matrix.smul_mul, Matrix.one_mul]

theorem twisted_commutant (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3)
    {B : Matrix (Fin 4) (Fin 4) K}
    (h0 : ∀ b : Su K p f 2,
      B * (BD (suMat b) 1).map (unitaryInvolution K p f) = BD (suMat b) 1 * B)
    (h2 : ∀ b : Su K p f 2,
      B * (BD 1 (suMat b)).map (unitaryInvolution K p f) = BD 1 (suMat b) * B) :
    ∃ l m : K, B = BD (l • !![0, -1; 1, 0]) (m • !![0, -1; 1, 0]) := by
  have hh2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  have hm1 : (-1 : Matrix (Fin 2) (Fin 2) K).map (unitaryInvolution K p f) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hm2 : (1 : Matrix (Fin 2) (Fin 2) K).map (unitaryInvolution K p f) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hn := h0 (negOneSU K p f)
  rw [suMat_negOneSU, map_BD, hm1, hm2] at hn
  obtain ⟨P, Q, rfl⟩ := eq_BD_of_comm_negBlock hh2 hn
  have hP : ∀ b : Su K p f 2, P * (suMat b).map (unitaryInvolution K p f) = suMat b * P := by
    intro b
    have := h0 b
    rw [map_BD, hm2, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact (BD_inj this).1
  have hQ : ∀ b : Su K p f 2, Q * (suMat b).map (unitaryInvolution K p f) = suMat b * Q := by
    intro b
    have := h2 b
    rw [map_BD, hm2, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact (BD_inj this).2
  obtain ⟨l, hl⟩ := twisted_scalar hK hp2 hq3 hP
  obtain ⟨m, hm⟩ := twisted_scalar hK hp2 hq3 hQ
  exact ⟨l, m, by rw [hl, hm]⟩

@[expose] noncomputable def rotSU2 (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] : Su K p f 2 :=
  Models.mkSU K p f !![0, -1; 1, 0]
    (by rw [det_fin_two_of]; ring)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two])

theorem suMat_rotSU2 : suMat (rotSU2 K p f) = !![0, -1; 1, 0] := rfl

theorem eq_of_central_BD {s : Su K p f 4} (hs : s ∈ Subgroup.center (Su K p f 4)) {c₁ c₂ : K}
    (h : suMat s = BD (c₁ • 1) (c₂ • 1)) : c₁ = c₂ := by
  have hc := Subgroup.mem_center_iff.mp hs (blockEmb K p f 4 2 1 (by norm_num) (rotSU2 K p f))
  have e := congrArg suMat hc
  rw [suMat_mul, suMat_mul, h, suMat_blockEmb, suMat_rotSU2] at e
  have e12 := congrFun (congrFun e 1) 2
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four, BD_eq] at e12
  exact e12.symm

end Two

section Group

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_su2_equiv_sl2 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3) :
    Nonempty (Su K p f 2 ≃* SL(2, ZMod 3)) := by
  classical
  have hcard : Nat.card (ZMod 3) = Nat.card (fixedSubfield K p f) := by
    rw [card_fixedSubfield hK, hqq]
    simp
  obtain ⟨ε⟩ : Nonempty (ZMod 3 ≃+* fixedSubfield K p f) := by
    have := Fintype.ofFinite (ZMod 3)
    have := Fintype.ofFinite (fixedSubfield K p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard])⟩
  obtain ⟨ν, hνinj, hνrange, -⟩ := exists_natChart hK hp2 ε
  have e1 : Su K p f 2 ≃* ↥(blockEmb K p f 4 2 0 (by norm_num)).range :=
    MonoidHom.ofInjective (blockEmb_injective (by norm_num))
  have e3 : SL(2, ZMod 3) ≃* ↥ν.range := MonoidHom.ofInjective hνinj
  have e2 : ↥(blockEmb K p f 4 2 0 (by norm_num)).range ≃* ↥ν.range :=
    MulEquiv.subgroupCongr hνrange.symm
  exact ⟨(e1.trans e2).trans e3.symm⟩

theorem su2_pow_three_mem_commutator (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hqq : p ^ f = 3) :
    ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆ := by
  obtain ⟨e⟩ := exists_su2_equiv_sl2 hK hp2 hqq
  intro l
  exact Q3W.pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp)
    (L := (⊤ : Subgroup (Su K p f 2))) (Subgroup.topEquiv.trans e) l trivial

end Group

end CFSG.ClassicalInvolution.Q3.Q3P21
