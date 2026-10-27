module

public import CFSG.ClassicalInvolution.RouteD.SCRSu4Base

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSu4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_four)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem trace_zero_of_sq {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) (M : Matrix (Fin 2) (Fin 2) R)
    (hM : M * M = -1) (hdet : M.det = 1) : M 0 0 + M 1 1 = 0 := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_contra ht
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right ht
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right ht
  have hsq : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by
    rw [hb, hc] at e00 e11
    linear_combination e00 - e11
  have had : M 0 0 = M 1 1 := by
    have := (mul_eq_zero.mp hsq).resolve_right ht
    linear_combination this
  apply h2
  rw [hb, hc] at e00 hdet
  rw [had] at e00 hdet
  linear_combination e00 - hdet


theorem exists_unit_eigvec (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0)
    {ι : K} (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι) (B : Su K p f 2)
    (hB : suMat B * suMat B = -1) :
    ∃ v : Fin 2 → K, suMat B *ᵥ v = ι • v ∧
      unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 = 1 := by
  set σ := unitaryInvolution K p f with hσdef
  set Bm := suMat B with hBm
  have hB' : conjTr σ Bm = -Bm := conjTr_eq_neg_of_sq B hB
  have hdet : Bm.det = 1 := B.2.1
  have htr : Bm 0 0 + Bm 1 1 = 0 := trace_zero_of_sq h2 Bm hB hdet
  have hBe : ∀ i j, σ (Bm j i) = -Bm i j := by
    intro i j
    have := congrFun (congrFun hB' i) j
    simpa [conjTr] using this
  set P : Matrix (Fin 2) (Fin 2) K := (2 : K)⁻¹ • (1 - ι • Bm) with hP
  have hσ2 : σ (2 : K)⁻¹ = (2 : K)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  have hPe : ∀ i j, P i j = (2 : K)⁻¹ * ((1 : Matrix (Fin 2) (Fin 2) K) i j - ι * Bm i j) := by
    intro i j
    simp [hP]
  have hselfadj : ∀ i j, σ (P j i) = P i j := by
    intro i j
    rw [hPe, hPe, map_mul, hσ2, map_sub, map_mul, hσι, hBe]
    have : σ ((1 : Matrix (Fin 2) (Fin 2) K) j i) = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [this]
    ring
  have hNN : (ι • Bm) * (ι • Bm) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB, hι]
    simp
  have hBP : Bm * P = ι • P := by
    have h1 : Bm * (1 - ι • Bm) = ι • (1 - ι • Bm) := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hB, smul_sub, smul_smul, hι]
      module
    simp only [hP, Matrix.mul_smul, h1, smul_comm ι (2 : K)⁻¹]
  have hPP : P * P = P := by
    have h1 : (1 - ι • Bm) * (1 - ι • Bm) = (2 : K) • (1 - ι • Bm) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hNN]
      module
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1]
    have : (2 : K)⁻¹ * ((2 : K)⁻¹ * 2) = (2 : K)⁻¹ := by field_simp
    rw [this]
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have hPtr : P 0 0 + P 1 1 = 1 := by
    rw [hPe, hPe]
    simp only [Matrix.one_apply_eq]
    linear_combination h22 + (-(2 : K)⁻¹ * ι) * htr
  have hex : ∃ j, P j j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hPtr
    rw [hcon 0, hcon 1] at this
    simp at this
  obtain ⟨j, hj⟩ := hex
  set w : Fin 2 → K := fun i => P i j with hwdef
  have hBw : Bm *ᵥ w = ι • w := by
    ext i
    have := congrFun (congrFun hBP i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, w] using this
  have hww : σ (w 0) * w 0 + σ (w 1) * w 1 = P j j := by
    have := congrFun (congrFun hPP j) j
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
    simp only [hwdef]
    rw [hselfadj j 0, hselfadj j 1]
    exact this
  obtain ⟨μ, hμ⟩ := hσ.norm_surj (P j j)⁻¹ (by rw [map_inv₀, hselfadj j j]) (inv_ne_zero hj)
  refine ⟨μ • w, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hBw, smul_comm]
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    calc σ μ * σ (w 0) * (μ * w 0) + σ μ * σ (w 1) * (μ * w 1) =
        σ μ * μ * (σ (w 0) * w 0 + σ (w 1) * w 1) := by ring
      _ = 1 := by rw [hμ, hww]; field_simp



@[expose] noncomputable def Mv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (v : Fin 2 → K)
    (hv : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 = 1) :
    Su K p f 2 :=
  aSU K p f (a := unitaryInvolution K p f (v 1)) (b := v 0)
    (by rw [hσ.invol]; linear_combination hv) hσ.invol

theorem suMat_Mv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (v : Fin 2 → K)
    (hv : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 = 1) :
    suMat (Mv hσ v hv) = !![unitaryInvolution K p f (v 1), v 0;
      -unitaryInvolution K p f (v 0), v 1] := by
  rw [Mv, suMat_aSU, hσ.invol]

theorem suMat_Mv_mulVec (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (v : Fin 2 → K)
    (hv : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 = 1) :
    suMat (Mv hσ v hv) *ᵥ (Pi.single 1 1) = v := by
  rw [suMat_Mv]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem suMat_conj_Mv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) {ι : K}
    (hι : ι * ι = -1) (B : Su K p f 2) (v : Fin 2 → K)
    (hv : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 = 1)
    (hBv : suMat B *ᵥ v = ι • v) :
    suMat ((Mv hσ v hv)⁻¹ * B * Mv hσ v hv) = !![-ι, 0; 0, ι] := by
  set m := Mv hσ v hv with hm
  set M := suMat (m⁻¹ * B * m) with hM
  have hMe : M *ᵥ (Pi.single 1 1) = ι • Pi.single 1 1 := by
    have h1 : suMat m *ᵥ (Pi.single 1 1) = v := suMat_Mv_mulVec hσ v hv
    calc M *ᵥ (Pi.single 1 1) = suMat m⁻¹ *ᵥ (suMat B *ᵥ (suMat m *ᵥ (Pi.single 1 1))) := by
          rw [hM, suMat_mul, suMat_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = ι • (suMat m⁻¹ *ᵥ (suMat m *ᵥ (Pi.single 1 1))) := by
          rw [h1, hBv, Matrix.mulVec_smul]
      _ = ι • Pi.single 1 1 := by
          rw [Matrix.mulVec_mulVec, suMat_inv_mul_suMat, Matrix.one_mulVec]
  have h01 : M 0 1 = 0 := by
    have := congrFun hMe 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h11 : M 1 1 = ι := by
    have := congrFun hMe 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : M.det = 1 := (m⁻¹ * B * m).2.1
  rw [Matrix.det_fin_two, h01, h11] at hdet
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have h00 : M 0 0 = -ι := by
    have : M 0 0 * ι = 1 := by linear_combination hdet
    have h3 : ι * (-ι) = 1 := by linear_combination -hι
    linear_combination (-ι) * this + (-(M 0 0)) * h3
  have hU : conjTr (unitaryInvolution K p f) M * M = 1 := (m⁻¹ * B * m).2.2
  have h10 : M 1 0 = 0 := by
    have := congrFun (congrFun hU 0) 1
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, h01, h11] at this
    exact this.resolve_right hι0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]



omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem blockMat_four_one (A : Matrix (Fin 2) (Fin 2) K) :
    blockMat 4 1 A = !![1, 0, 0, 0; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_blockEmb_one (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 1 (by norm_num) A) =
      !![1, 0, 0, 0; 0, suMat A 0 0, suMat A 0 1, 0; 0, suMat A 1 0, suMat A 1 1, 0;
        0, 0, 0, 1] := by
  rw [suMat_blockEmb, blockMat_four_one]

theorem blockEmb_one_mem_centralizer (y : Su K p f 4) (d : Fin 4 → K)
    (hd : suMat y = Matrix.diagonal d) (h12 : d 1 = d 2) (A : Su K p f 2) :
    blockEmb K p f 4 2 1 (by norm_num) A ∈ Subgroup.centralizer ({y} : Set (Su K p f 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply suMat_injective
  rw [suMat_mul, suMat_mul, hd, suMat_blockEmb_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h12, mul_comm]

theorem su4_caseA_core (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {ι : K}
    (B B' : Su K p f 2) (hB : suMat B = !![-ι, 0; 0, ι]) (hB' : suMat B' = !![-ι, 0; 0, ι]) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (B, B')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (B, B')} : Set (Su K p f 4)) = ⊤ := by
  set H := Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (B, B')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (B, B')} : Set (Su K p f 4)) with hH
  have hM : ∀ m : Su K p f 2 × Su K p f 2, phiU K p f m ∈ H := fun m =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (phiU_mem_centralizer_xU m))
  have hdiag : suMat (xU K p f * phiU K p f (B, B')) =
      Matrix.diagonal ![ι, -ι, -ι, ι] := by
    rw [suMat_mul, phiU_apply, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two, hB, hB']
    simp only [xU, suMat_rootInvSU_four]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have h1 : ∀ A : Su K p f 2, blockEmb K p f 4 2 1 (by norm_num) A ∈ H := fun A =>
    Subgroup.mem_sup_right (blockEmb_one_mem_centralizer _ _ hdiag rfl A)
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq 3]
  refine iSup_le fun i => ?_
  rintro _ ⟨A, rfl⟩
  fin_cases i
  · have := hM (A, 1)
    rwa [phiU_apply, map_one, mul_one] at this
  · exact h1 A
  · have := hM (1, A)
    rwa [phiU_apply, map_one, one_mul] at this

theorem su4_caseA (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (h2 : (2 : K) ≠ 0) {ι : K}
    (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = -ι) (B B' : Su K p f 2)
    (hB : suMat B * suMat B = -1) (hB' : suMat B' * suMat B' = -1) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (B, B')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (B, B')} : Set (Su K p f 4)) = ⊤ := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨v, hv, hvn⟩ := exists_unit_eigvec hσ h2 hι hσι B hB
  obtain ⟨v', hv', hvn'⟩ := exists_unit_eigvec hσ h2 hι hσι B' hB'
  refine sup_eq_top_of_conj (Mv hσ v hvn)⁻¹ (Mv hσ v' hvn')⁻¹ B B' ?_
  rw [inv_inv, inv_inv]
  exact su4_caseA_core hK hq _ _ (suMat_conj_Mv hσ hι B v hvn hv)
    (suMat_conj_Mv hσ hι B' v' hvn' hv')

end CFSG.ClassicalInvolution.RouteD.SCRSu4
