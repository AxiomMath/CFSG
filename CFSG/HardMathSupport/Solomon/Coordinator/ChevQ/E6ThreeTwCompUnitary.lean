module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompRegular
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwTorusDet
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredMatrix
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.DiagCube
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (hpair hpair_mulVec hpair_comm
  hpair_smul_right hpair_pow_pow hpair_pow_shift pow_three_mulVec irred_frame)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd (adjU_mul adjU_smul
  det_mem_rootsOfUnityU three_ne_zero_of_cube_rootU)

section Linear

variable {K : Type} [Field K]

theorem twNot_hasCyclicVec3_of_mul_eq_zero {A : Matrix (Fin 3) (Fin 3) K} {a b : K}
    (h : (A - a • 1) * (A - b • 1) = 0) : ¬ HasCyclicVec3 A := by
  rintro ⟨v, hv⟩
  have h1 : (A - a • 1) *ᵥ ((A - b • 1) *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec, Matrix.mulVec_smul,
    Matrix.one_mulVec] at h1
  have h2 := Fintype.linearIndependent_iff.1 hv ![a * b, -(a + b), 1] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (norm := module) h1) 2
  simp at h2

theorem twMul_eq_zero_of_mul_eq_diagonal {A P P' : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (hP : P * P' = 1) (hAP : A * P = P * diagonal d) {a b : K}
    (hd : ∀ i, (d i - a) * (d i - b) = 0) : (A - a • 1) * (A - b • 1) = 0 := by
  have hc : ∀ c : K, (A - c • 1) * P = P * diagonal (fun i => d i - c) := by
    intro c
    have hdc : diagonal (fun i => d i - c) = diagonal d - c • 1 := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
    rw [hdc, Matrix.sub_mul, Matrix.mul_sub, hAP, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have h0 : (A - a • 1) * (A - b • 1) * P = 0 := by
    rw [Matrix.mul_assoc, hc b, ← Matrix.mul_assoc, hc a, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp [hd]
  calc (A - a • 1) * (A - b • 1) = (A - a • 1) * (A - b • 1) * (P * P') := by
        rw [hP, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem twAdd_add_eq_zero_of_pow_three_eq {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hy : y ^ 3 = x ^ 3) (hz : z ^ 3 = x ^ 3) : x + y + z = 0 := by
  have h1 : x ^ 2 + x * y + y ^ 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination -hy : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0)).resolve_left
      (sub_ne_zero.2 hxy)
  have h2 : x ^ 2 + x * z + z ^ 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination -hz : (x - z) * (x ^ 2 + x * z + z ^ 2) = 0)).resolve_left
      (sub_ne_zero.2 hxz)
  exact (mul_eq_zero.1 (by linear_combination h1 - h2 : (y - z) * (x + y + z) = 0)).resolve_left
    (sub_ne_zero.2 hyz)

end Linear

section Frame

variable {p n : ℕ} {F : Type} [Field F]

theorem twBar_eq_of_adj_mul_eq_smul_one (hF : UnitaryFieldData p n F)
    {Q : Matrix (Fin 3) (Fin 3) F} {ν : F} (hQ : (Q.map hF.bar)ᵀ * Q = ν • 1) :
    hF.bar ν = ν := by
  have h := congrFun (congrFun hQ 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hF.bar_bar, mul_comm]

theorem twExists_frame_of_hpair (hF : UnitaryFieldData p n F) {A : Matrix (Fin 3) (Fin 3) F}
    (hAu : (A.map hF.bar)ᵀ * A = 1) {α : F} (hA3 : A ^ 3 = α • 1) {w : Fin 3 → F}
    (hw : hpair hF w (A *ᵥ w) = 0) :
    ∃ Q : Matrix (Fin 3) (Fin 3) F, (Q.map hF.bar)ᵀ * Q = hpair hF w w • 1 ∧
      A * Q = Q * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  classical
  have e02 : hpair hF w ((A ^ 2) *ᵥ w) = 0 := by
    have := hpair_pow_pow (h := hF) hAu w w 1 3
    simp only [show (1 : ℕ) ≤ 3 by norm_num, ↓reduceIte, pow_one] at this
    rw [pow_three_mulVec hA3, hpair_smul_right, hpair_comm w (A *ᵥ w), hw, map_zero,
      mul_zero] at this
    simpa using this.symm
  set ν : F := hpair hF w w with hνdef
  have e12 : hpair hF (A *ᵥ w) ((A ^ 2) *ᵥ w) = 0 := by
    have := hpair_pow_pow (h := hF) hAu w w 1 2
    simp only [show (1 : ℕ) ≤ 2 by norm_num, ↓reduceIte, pow_one] at this
    simpa [hw] using this
  have e11 : hpair hF (A *ᵥ w) (A *ᵥ w) = ν := hpair_mulVec hAu w w
  have e22 : hpair hF ((A ^ 2) *ᵥ w) ((A ^ 2) *ᵥ w) = ν := hpair_pow_shift hAu 2 w w
  have e10 : hpair hF (A *ᵥ w) w = 0 := by rw [hpair_comm, hw, map_zero]
  have e20 : hpair hF ((A ^ 2) *ᵥ w) w = 0 := by rw [hpair_comm, e02, map_zero]
  have e21 : hpair hF ((A ^ 2) *ᵥ w) (A *ᵥ w) = 0 := by rw [hpair_comm, e12, map_zero]
  set Q : Matrix (Fin 3) (Fin 3) F := (Matrix.of ![w, A *ᵥ w, (A ^ 2) *ᵥ w])ᵀ with hQ
  refine ⟨Q, ?_, ?_⟩
  · ext j k
    have key : ((Q.map hF.bar)ᵀ * Q) j k = hpair hF (![w, A *ᵥ w, (A ^ 2) *ᵥ w] j)
        (![w, A *ᵥ w, (A ^ 2) *ᵥ w] k) := by
      simp [Matrix.mul_apply, hpair, hQ]
    rw [key]
    fin_cases j <;> fin_cases k <;> simp [hw, e02, e12, e10, e20, e21, e11, e22, hνdef]
  · have hc1 : A *ᵥ (A *ᵥ w) = (A ^ 2) *ᵥ w := by
      rw [Matrix.mulVec_mulVec, pow_two]
    have hc2 : A *ᵥ ((A ^ 2) *ᵥ w) = α • w := by
      rw [Matrix.mulVec_mulVec, ← pow_succ', pow_three_mulVec hA3]
    ext i k
    fin_cases k
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ]
    · have := congrFun hc1 i
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ] at this ⊢
      exact this
    · have := congrFun hc2 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ] at this ⊢
      linear_combination this

theorem twExists_frame_of_mul_eq_diagonal (hF : UnitaryFieldData p n F)
    {A P : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1) {α : F}
    (hA3 : A ^ 3 = α • 1) (hA : HasCyclicVec3 A) (hPu : (P.map hF.bar)ᵀ * P = 1)
    {e : Fin 3 → F} (hAP : A * P = P * diagonal e) :
    ∃ Q : Matrix (Fin 3) (Fin 3) F, (Q.map hF.bar)ᵀ * Q = (3 : F) • 1 ∧
      A * Q = Q * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  have hPP : P * (P.map hF.bar)ᵀ = 1 := mul_eq_one_comm.mp hPu
  have he3 : ∀ i, e i ^ 3 = α := by
    have h1 : P * diagonal e ^ 3 = A ^ 3 * P := SemiconjBy.pow_right hAP.symm 3
    rw [hA3, Matrix.smul_mul, Matrix.one_mul, Matrix.diagonal_pow] at h1
    have h2 : diagonal (e ^ 3) = α • (1 : Matrix (Fin 3) (Fin 3) F) := by
      calc diagonal (e ^ 3) = (P.map hF.bar)ᵀ * (P * diagonal (e ^ 3)) := by
            rw [← Matrix.mul_assoc, hPu, Matrix.one_mul]
        _ = α • 1 := by rw [h1, Matrix.mul_smul, hPu]
    intro i
    simpa using congrFun (congrFun h2 i) i
  have hne : ∀ a b : F, (∀ i, (e i - a) * (e i - b) = 0) → False := fun a b hab =>
    twNot_hasCyclicVec3_of_mul_eq_zero (twMul_eq_zero_of_mul_eq_diagonal hPP hAP hab) hA
  have h01 : e 0 ≠ e 1 := fun h => hne (e 0) (e 2) (by intro i; fin_cases i <;> simp [h])
  have h02 : e 0 ≠ e 2 := fun h => hne (e 0) (e 1) (by intro i; fin_cases i <;> simp [h])
  have h12 : e 1 ≠ e 2 := fun h => hne (e 0) (e 1) (by intro i; fin_cases i <;> simp [h])
  have hsum : e 0 + e 1 + e 2 = 0 := twAdd_add_eq_zero_of_pow_three_eq h01 h02 h12
    (by rw [he3, he3]) (by rw [he3, he3])
  have hw : hpair hF (P *ᵥ fun _ => 1) (A *ᵥ (P *ᵥ fun _ => 1)) = 0 := by
    rw [Matrix.mulVec_mulVec, hAP, ← Matrix.mulVec_mulVec, hpair_mulVec hPu]
    simpa [hpair, Fin.sum_univ_three, Matrix.mulVec_diagonal] using hsum
  obtain ⟨Q, hQ, hAQ⟩ := twExists_frame_of_hpair hF hAu hA3 hw
  refine ⟨Q, ?_, hAQ⟩
  rw [hQ, hpair_mulVec hPu]
  congr 1
  norm_num [hpair, Fin.sum_univ_three]

theorem twExists_unitaryFrame_of_cube (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1) {α μ : F}
    (hA3 : A ^ 3 = α • 1) (hμ : μ ^ 3 = α) (hA : HasCyclicVec3 A) :
    ∃ Q : Matrix (Fin 3) (Fin 3) F, (Q.map hF.bar)ᵀ * Q = (3 : F) • 1 ∧
      A * Q = Q * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  classical
  have hdn : hF.bar A.det * A.det = 1 := by
    have h := congrArg Matrix.det hAu
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have hν : hF.bar μ * μ = 1 := by
    apply eq_one_of_bar_eq_of_pow_three_eq_one hF h3
    · calc (hF.bar μ * μ) ^ 3 = hF.bar (μ ^ 3) * μ ^ 3 := by rw [map_pow, mul_pow]
        _ = 1 := by rw [hμ, ← hA.det_eq hA3, hdn]
    · rw [map_mul, hF.bar_bar, mul_comm]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hν
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 3) (Fin 3) F, S = μ⁻¹ • A := ⟨_, rfl⟩
  have hS3 : S ^ 3 = 1 := by
    rw [hS, smul_pow, hA3, smul_smul, ← hμ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hμ0),
      one_smul]
  have hSu : (S.map hF.bar)ᵀ * S = 1 := by
    rw [hS, adjU_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, map_inv₀, ← mul_inv,
      hν, inv_one, one_smul]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : GL (Fin 3) F, (Sg : Matrix (Fin 3) (Fin 3) F) = S :=
    ⟨⟨S, (S.map hF.bar)ᵀ, mul_eq_one_comm.mp hSu, hSu⟩, rfl⟩
  have hSgU : Sg ∈ primeFormUnitary hF (idGram F 3) := by
    rw [mem_primeFormUnitary, hSg]
    simpa [idGram] using hSu
  obtain ⟨s, hs⟩ : ∃ s : primeFormUnitary hF (idGram F 3), (s : GL (Fin 3) F) = Sg :=
    ⟨⟨Sg, hSgU⟩, rfl⟩
  have hsm : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = S := by rw [hs, hSg]
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsm, hS3]
    rfl
  have hcomm : ∀ x ∈ Subgroup.zpowers s, ∀ y ∈ Subgroup.zpowers s, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self s i j).eq
  have hpow : ∀ x ∈ Subgroup.zpowers s, x ^ 3 = 1 := by
    rintro x ⟨i, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hs3, _root_.one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hF Nat.prime_three h3
    (Subgroup.zpowers s) hcomm hpow
  obtain ⟨Pm, hPm⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = (((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPu : (Pm.map hF.bar)ᵀ * Pm = 1 := by
    rw [hPm]
    simpa [idGram] using mem_primeFormUnitary.1 P.2
  have hD : (Pi * S * Pm).IsDiag := by
    have h1 := hP s (Subgroup.mem_zpowers s)
    have h2 : ((P⁻¹ * s * P : primeFormUnitary hF (idGram F 3)) : GL (Fin 3) F) =
        (P : GL (Fin 3) F)⁻¹ * (s : GL (Fin 3) F) * (P : GL (Fin 3) F) := rfl
    rw [h2, Units.val_mul, Units.val_mul, hsm, ← hPm, ← hPi] at h1
    exact h1
  have hSP : S * Pm = Pm * (Pi * S * Pm) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have hDe : diagonal (fun i => μ * (Pi * S * Pm) i i) = μ • (Pi * S * Pm) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, hD hij, smul_zero]
  have hAP : A * Pm = Pm * diagonal (fun i => μ * (Pi * S * Pm) i i) := by
    have hAS : A = μ • S := by rw [hS, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [hDe, Matrix.mul_smul, ← hSP, hAS, Matrix.smul_mul]
  exact twExists_frame_of_mul_eq_diagonal hF hAu hA3 hA hPu hAP

theorem twExists_unitaryFrame (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1) {α : F}
    (hA3 : A ^ 3 = α • 1) (hA : HasCyclicVec3 A) :
    ∃ (Q : Matrix (Fin 3) (Fin 3) F) (ν : F), ν ≠ 0 ∧ (Q.map hF.bar)ᵀ * Q = ν • 1 ∧
      A * Q = Q * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  by_cases hcube : ∃ μ : F, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    obtain ⟨Q, hQ, hAQ⟩ := twExists_unitaryFrame_of_cube hF h3 hAu hA3 hμ hA
    obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hF Nat.prime_three h3
    exact ⟨Q, 3, three_ne_zero_of_cube_rootU hζ.pow_eq_one (hζ.ne_one (by norm_num)), hQ, hAQ⟩
  · exact irred_frame hF A hAu hA3 fun x hx => hcube ⟨x, hx⟩

theorem twExists_unitaryIsom_conj_of_frame (hF : UnitaryFieldData p n F)
    {A B C Q R : Matrix (Fin 3) (Fin 3) F} {ν ρ : F} (hν : ν ≠ 0) (hρ : ρ ≠ 0)
    (hQ : (Q.map hF.bar)ᵀ * Q = ν • 1) (hR : (R.map hF.bar)ᵀ * R = ρ • 1)
    (hAQ : A * Q = Q * C) (hBR : B * R = R * C) :
    ∃ g : Matrix (Fin 3) (Fin 3) F, (g.map hF.bar)ᵀ * g = 1 ∧ g * A = B * g := by
  have hνb := twBar_eq_of_adj_mul_eq_smul_one hF hQ
  have hρb := twBar_eq_of_adj_mul_eq_smul_one hF hR
  obtain ⟨c, hc⟩ := hF.normHom_surjective
    ⟨ν / ρ, hF.mem_fixedField.2 (by rw [map_div₀, hνb, hρb])⟩
  have hc' : c * hF.bar c = ν / ρ := congrArg Subtype.val hc
  have hQQ : Q * (Q.map hF.bar)ᵀ = ν • 1 := by
    have h1 : (ν⁻¹ • (Q.map hF.bar)ᵀ) * Q = 1 := by
      rw [Matrix.smul_mul, hQ, smul_smul, inv_mul_cancel₀ hν, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc Q * (Q.map hF.bar)ᵀ = ν • (ν⁻¹ • (Q * (Q.map hF.bar)ᵀ)) := by
          rw [smul_smul, mul_inv_cancel₀ hν, one_smul]
      _ = ν • 1 := by rw [h2]
  have hQA : (Q.map hF.bar)ᵀ * A = C * (Q.map hF.bar)ᵀ := by
    calc (Q.map hF.bar)ᵀ * A = ν⁻¹ • ((Q.map hF.bar)ᵀ * A * (Q * (Q.map hF.bar)ᵀ)) := by
          rw [hQQ, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hν, one_smul]
      _ = ν⁻¹ • ((Q.map hF.bar)ᵀ * Q * C * (Q.map hF.bar)ᵀ) := by
          rw [← Matrix.mul_assoc, Matrix.mul_assoc _ A Q, hAQ, ← Matrix.mul_assoc]
      _ = C * (Q.map hF.bar)ᵀ := by
          rw [hQ, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
            inv_mul_cancel₀ hν, one_smul]
  have hs : hF.bar (c * ν⁻¹) * (c * ν⁻¹) * ρ * ν = 1 := by
    rw [map_mul, map_inv₀, hνb]
    calc hF.bar c * ν⁻¹ * (c * ν⁻¹) * ρ * ν = c * hF.bar c * ρ * ν⁻¹ * (ν⁻¹ * ν) := by ring
      _ = 1 := by
        rw [hc', inv_mul_cancel₀ hν, mul_one, div_mul_cancel₀ _ hρ, mul_inv_cancel₀ hν]
  have hdd : (((Q.map hF.bar)ᵀ).map hF.bar)ᵀ = Q := by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  refine ⟨(c * ν⁻¹) • (R * (Q.map hF.bar)ᵀ), ?_, ?_⟩
  · rw [adjU_smul, adjU_mul, hdd, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ R, hR, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hQQ,
      smul_smul, smul_smul, hs, one_smul]
  · calc (c * ν⁻¹) • (R * (Q.map hF.bar)ᵀ) * A
        = (c * ν⁻¹) • (R * ((Q.map hF.bar)ᵀ * A)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (c * ν⁻¹) • (R * C * (Q.map hF.bar)ᵀ) := by rw [hQA, Matrix.mul_assoc]
      _ = (c * ν⁻¹) • (B * R * (Q.map hF.bar)ᵀ) := by rw [hBR]
      _ = B * ((c * ν⁻¹) • (R * (Q.map hF.bar)ᵀ)) := by rw [Matrix.mul_smul, Matrix.mul_assoc]

end Frame

theorem twExists_unitaryIsom_conj_of_hasCyclicVec3 {p n : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1) {A B : GL (Fin 3) F}
    (hAu : A ∈ unitaryIsom3 hF) (hBu : B ∈ unitaryIsom3 hF) {α β : F}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1)
    (hB3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = β • 1)
    (hdet : (A : Matrix (Fin 3) (Fin 3) F).det = (B : Matrix (Fin 3) (Fin 3) F).det)
    (hA : HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) F))
    (hB : HasCyclicVec3 (B : Matrix (Fin 3) (Fin 3) F)) :
    ∃ g ∈ unitaryIsom3 hF, g * A = B * g := by
  have hαβ : α = β := (hA.det_eq hA3).symm.trans (hdet.trans (hB.det_eq hB3))
  subst hαβ
  obtain ⟨Q, ν, hν, hQ, hAQ⟩ := twExists_unitaryFrame hF h3 (mem_unitaryIsom3.1 hAu) hA3 hA
  obtain ⟨R, ρ, hρ, hR, hBR⟩ := twExists_unitaryFrame hF h3 (mem_unitaryIsom3.1 hBu) hB3 hB
  obtain ⟨g, hgu, hgA⟩ := twExists_unitaryIsom_conj_of_frame hF hν hρ hQ hR hAQ hBR
  exact ⟨⟨g, (g.map hF.bar)ᵀ, mul_eq_one_comm.mp hgu, hgu⟩, mem_unitaryIsom3.2 hgu,
    Units.ext hgA⟩

theorem twExists_unitarySU_conj_of_hasCyclicVec3 {p n : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1) {A B : GL (Fin 3) F}
    (hAu : A ∈ unitaryIsom3 hF) (hBu : B ∈ unitaryIsom3 hF) {α β : F}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1)
    (hB3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = β • 1)
    (hdet : (A : Matrix (Fin 3) (Fin 3) F).det = (B : Matrix (Fin 3) (Fin 3) F).det)
    (hA : HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) F))
    (hB : HasCyclicVec3 (B : Matrix (Fin 3) (Fin 3) F)) :
    ∃ g ∈ unitarySU p n F 3, g * A = B * g := by
  obtain ⟨g, hg, hgA⟩ :=
    twExists_unitaryIsom_conj_of_hasCyclicVec3 hF h3 hAu hBu hA3 hB3 hdet hA hB
  obtain ⟨δ, hδ, hdetδ⟩ := exists_unitaryIsom_commute_det_eq_of_pow_three hF h3
    (γ := ⟨A, hAu⟩) hA3 (inv_mem (det_mem_rootsOfUnityU hF hg))
  refine ⟨g * δ, (mem_unitarySU_iff hF).2 ⟨?_, mem_unitaryIsom3.1 (mul_mem hg δ.2)⟩, ?_⟩
  · rw [← GeneralLinearGroup.val_det_apply, map_mul, hdetδ, mul_inv_cancel, Units.val_one]
  · have hδ' : (δ : GL (Fin 3) F) * A = A * δ := hδ
    calc g * (δ : GL (Fin 3) F) * A = g * A * δ := by rw [mul_assoc, hδ', ← mul_assoc]
      _ = B * (g * δ) := by rw [hgA, mul_assoc]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
