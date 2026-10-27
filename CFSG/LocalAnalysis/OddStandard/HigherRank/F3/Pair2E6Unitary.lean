module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Sigma
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockEquiv

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.WeakCT CFSG.LieType.BorelTits
open scoped Matrix MatrixGroups Polynomial

section Unitary

variable {k : Type} [Field k]

private theorem unitaryJInv6_mul_J :
    (unitaryJInv6 : Matrix (Fin 6) (Fin 6) k) * unitaryJ6 = 1 :=
  mul_eq_one_comm.mp unitaryJ6_mul

private theorem adj_mem_iff {C A : Matrix (Fin 6) (Fin 6) k} (hC : C.det = 1) :
    (unitaryJ6 * C.adjugate * unitaryJInv6 = A) ↔
      C * unitaryJInv6 * A = unitaryJInv6 := by
  have hCA : C.adjugate * C = 1 := by rw [Matrix.adjugate_mul, hC, one_smul]
  have hAC : C * C.adjugate = 1 := by rw [Matrix.mul_adjugate, hC, one_smul]
  constructor
  · intro h
    have h1 : C.adjugate * unitaryJInv6 = unitaryJInv6 * A := by
      have h' : unitaryJInv6 * (unitaryJ6 * C.adjugate * unitaryJInv6) = unitaryJInv6 * A := by
        rw [h]
      calc C.adjugate * unitaryJInv6
          = unitaryJInv6 * (unitaryJ6 * C.adjugate * unitaryJInv6) := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, unitaryJInv6_mul_J, Matrix.one_mul]
        _ = unitaryJInv6 * A := h'
    have h2 : C * unitaryJInv6 * A = unitaryJInv6 := by
      calc C * unitaryJInv6 * A
          = C * (unitaryJInv6 * A) := by simp only [Matrix.mul_assoc]
        _ = C * (C.adjugate * unitaryJInv6) := by rw [h1]
        _ = (C * C.adjugate) * unitaryJInv6 := by simp only [Matrix.mul_assoc]
        _ = unitaryJInv6 := by rw [hAC, Matrix.one_mul]
    exact h2
  · intro h
    have h1 : C.adjugate * unitaryJInv6 = unitaryJInv6 * A := by
      calc C.adjugate * unitaryJInv6
          = C.adjugate * (C * unitaryJInv6 * A) := by rw [h]
        _ = unitaryJInv6 * A := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCA, Matrix.one_mul]
    have h2 : unitaryJ6 * C.adjugate * unitaryJInv6 = A := by
      calc unitaryJ6 * C.adjugate * unitaryJInv6
          = unitaryJ6 * (C.adjugate * unitaryJInv6) := by simp only [Matrix.mul_assoc]
        _ = unitaryJ6 * (unitaryJInv6 * A) := by rw [h1]
        _ = A := by rw [← Matrix.mul_assoc, unitaryJ6_mul, Matrix.one_mul]
    exact h2

private theorem det_conjTr (ψ : k ≃+* k) {A : Matrix (Fin 6) (Fin 6) k} (hA : A.det = 1) :
    (conjTr ψ A).det = 1 := by
  have h1 : (conjTr ψ A).det = ψ A.det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingEquiv.map_det ψ A).symm
  rw [h1, hA, map_one]

private theorem coe_sigmaA6 (ψ : k ≃+* k) (A : SL(6, k)) :
    ((sigmaA6 ψ A : SL(6, k)) : Matrix (Fin 6) (Fin 6) k) =
      unitaryJ6 * (Matrix.adjugate ((A : Matrix (Fin 6) (Fin 6) k).map ψ))ᵀ *
        unitaryJInv6 := by
  simp only [sigmaA6, MulEquiv.trans_apply, coe_conjSL, coe_invTransposeSL, coe_fieldAutSL,
    Matrix.SpecialLinearGroup.coe_inv]

private theorem mem_unitaryGroup6_iff (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (A : SL(6, k)) :
    A ∈ unitaryGroup6 θ hθ ↔
      conjTr (involEquiv θ hθ) (A : Matrix (Fin 6) (Fin 6) k) * unitaryJInv6 *
        (A : Matrix (Fin 6) (Fin 6) k) = unitaryJInv6 := by
  rw [mem_unitaryGroup6]
  have hC : (conjTr (involEquiv θ hθ) (A : Matrix (Fin 6) (Fin 6) k)).det = 1 :=
    det_conjTr _ A.2
  rw [← adj_mem_iff (C := conjTr (involEquiv θ hθ) (A : Matrix (Fin 6) (Fin 6) k))
    (A := (A : Matrix (Fin 6) (Fin 6) k)) hC]
  constructor
  · intro h
    have hm := congrArg (fun x : SL(6, k) => (x : Matrix (Fin 6) (Fin 6) k)) h
    rw [coe_sigmaA6 (involEquiv θ hθ) A, Matrix.adjugate_transpose] at hm
    simpa [conjTr] using hm
  · intro h
    apply Subtype.ext
    rw [coe_sigmaA6 (involEquiv θ hθ) A, Matrix.adjugate_transpose]
    simpa [conjTr] using h

private theorem diagonal_antidiag_diagonal {k : Type} [Field k] (a b : Fin 6 → k)
    (i j : Fin 6) :
    (Matrix.diagonal a * (antidiag 6 : Matrix (Fin 6) (Fin 6) k) * Matrix.diagonal b) i j =
      if j = Fin.rev i then a i * b j else 0 := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, antidiag]
  simp only [Matrix.of_apply]
  split_ifs with h
  · subst h; ring
  · ring

private theorem diagonal_antidiag {k : Type} [Field k] (a : Fin 6 → k) (i j : Fin 6) :
    (Matrix.diagonal a * (antidiag 6 : Matrix (Fin 6) (Fin 6) k)) i j =
      if j = Fin.rev i then a i else 0 := by
  rw [Matrix.diagonal_mul, antidiag]
  simp only [Matrix.of_apply]
  split_ifs with h
  · subst h; ring
  · ring

private theorem unitaryJInv6_eq {k : Type} [Field k] :
    (unitaryJInv6 : Matrix (Fin 6) (Fin 6) k) =
      Matrix.diagonal ![1, -1, 1, -1, 1, -1] * (antidiag 6 : Matrix (Fin 6) (Fin 6) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryJInv6, antidiag, Matrix.diagonal_mul, Fin.rev]

theorem exists_ne_of_card_nine [Finite k] (hk : Nat.card k = 9) (θ : k →+* k)
    (hθ3 : ∀ c, θ c = c ^ 3 ^ 1) : ∃ c, θ c ≠ c := by
  by_contra! h
  haveI := Fintype.ofFinite k
  have hdeg : (Polynomial.X ^ 3 - Polynomial.X : k[X]).natDegree = 3 := by
    refine (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_).trans ?_
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      norm_num
    · rw [Polynomial.natDegree_X_pow]
  have hp : (Polynomial.X ^ 3 - Polynomial.X : k[X]) ≠ 0 := by
    intro hp0
    rw [hp0] at hdeg
    simp at hdeg
  have hroot : ∀ c, c ∈ (Polynomial.X ^ 3 - Polynomial.X : k[X]).roots := by
    intro c
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot]
    have hc : c ^ 3 = c := by
      have h1 : c ^ 3 ^ 1 = c := by rw [← hθ3 c, h c]
      simpa only [pow_one] using h1
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hc, sub_self]
  have hsub : (Finset.univ : Finset k).val ⊆ (Polynomial.X ^ 3 - Polynomial.X : k[X]).roots :=
    fun c _ => hroot c
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  have hcard : (Finset.univ : Finset k).card = 9 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
  rw [hcard, hdeg] at hle
  norm_num at hle

theorem exists_neg_of_involution (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (hne : ∃ c, θ c ≠ c) :
    ∃ μ : k, μ ≠ 0 ∧ θ μ = -μ := by
  obtain ⟨c, hc⟩ := hne
  refine ⟨c - θ c, sub_ne_zero.mpr (Ne.symm hc), ?_⟩
  rw [map_sub, hθ c]
  ring

theorem exists_mulEquiv_SU6 (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {μ : k} (hμ0 : μ ≠ 0)
    (hμ : θ μ = -μ) :
    Nonempty (↥(unitaryGroup6 θ hθ) ≃* ↥(SU (involEquiv θ hθ) 6)) := by
  let ψ := involEquiv θ hθ
  have hψμ : ψ μ = -μ := by
    change involEquiv θ hθ μ = -μ
    rw [involEquiv_apply]
    exact hμ
  let v : Fin 6 → k := ![1, 1, 1, μ, -μ, μ]
  let w : Fin 6 → k := ![1, 1, 1, μ⁻¹, -μ⁻¹, μ⁻¹]
  have hvw : v * w = 1 := by
    funext i
    fin_cases i <;> simp [v, w, mul_inv_cancel₀ hμ0, inv_mul_cancel₀ hμ0]
  have hwv : w * v = 1 := by
    funext i
    fin_cases i <;> simp [v, w, mul_inv_cancel₀ hμ0, inv_mul_cancel₀ hμ0]
  have hDmul : Matrix.diagonal v * Matrix.diagonal w = (1 : Matrix (Fin 6) (Fin 6) k) := by
    rw [Matrix.diagonal_mul_diagonal]
    show Matrix.diagonal (v * w) = 1
    rw [hvw]
    exact Matrix.diagonal_one
  have hDmul' : Matrix.diagonal w * Matrix.diagonal v = (1 : Matrix (Fin 6) (Fin 6) k) := by
    rw [Matrix.diagonal_mul_diagonal]
    show Matrix.diagonal (w * v) = 1
    rw [hwv]
    exact Matrix.diagonal_one
  let D : (Matrix (Fin 6) (Fin 6) k)ˣ :=
    ⟨Matrix.diagonal v, Matrix.diagonal w, hDmul, hDmul'⟩
  let Dm : Matrix (Fin 6) (Fin 6) k := (D : Matrix (Fin 6) (Fin 6) k)
  let Di : Matrix (Fin 6) (Fin 6) k :=
    ((D⁻¹ : (Matrix (Fin 6) (Fin 6) k)ˣ) : Matrix (Fin 6) (Fin 6) k)
  have hDm_eq : Dm = Matrix.diagonal v := rfl
  have hDi_eq : Di = Matrix.diagonal w := rfl
  have hdm : conjTr ψ Dm = Matrix.diagonal ![1, 1, 1, -μ, μ, -μ] := by
    rw [hDm_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply,
        v, hψμ]
  have hdi : conjTr ψ Di = Matrix.diagonal ![1, 1, 1, -μ⁻¹, μ⁻¹, -μ⁻¹] := by
    rw [hDi_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply,
        w, hψμ, inv_neg]
  have hD2 : conjTr ψ Dm * antidiag 6 * Dm = μ • unitaryJInv6 := by
    rw [hdm, hDm_eq, unitaryJInv6_eq]
    ext i j
    rw [diagonal_antidiag_diagonal, Matrix.smul_apply, diagonal_antidiag]
    fin_cases i <;> fin_cases j <;> simp [Fin.rev, v] <;> ring
  have hDi : conjTr ψ Di * unitaryJInv6 * Di = μ⁻¹ • antidiag 6 := by
    rw [hdi, hDi_eq, unitaryJInv6_eq]
    rw [← Matrix.mul_assoc (Matrix.diagonal ![1,1,1,-μ⁻¹,μ⁻¹,-μ⁻¹])
      (Matrix.diagonal ![1,-1,1,-1,1,-1]) (antidiag 6)]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    rw [diagonal_antidiag_diagonal, Matrix.smul_apply, antidiag]
    simp only [Matrix.of_apply]
    fin_cases i <;> fin_cases j <;> simp [Fin.rev, w] <;> ring
  have hDmulDinv : Dm * Di = (1 : Matrix (Fin 6) (Fin 6) k) := by
    rw [show Dm = (D : Matrix (Fin 6) (Fin 6) k) from rfl,
      show Di = ((D⁻¹ : (Matrix (Fin 6) (Fin 6) k)ˣ) : Matrix (Fin 6) (Fin 6) k) from rfl,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDimulD : Di * Dm = (1 : Matrix (Fin 6) (Fin 6) k) := by
    rw [show Dm = (D : Matrix (Fin 6) (Fin 6) k) from rfl,
      show Di = ((D⁻¹ : (Matrix (Fin 6) (Fin 6) k)ˣ) : Matrix (Fin 6) (Fin 6) k) from rfl,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have forward : ∀ (A : SL(6, k)), A ∈ unitaryGroup6 θ hθ →
      D * (A : GL (Fin 6) k) * D⁻¹ ∈ SU ψ 6 := by
    intro A hA
    let Am : Matrix (Fin 6) (Fin 6) k := (A : Matrix (Fin 6) (Fin 6) k)
    have hAm : conjTr ψ Am * unitaryJInv6 * Am = unitaryJInv6 :=
      (mem_unitaryGroup6_iff θ hθ A).mp hA
    refine ⟨?_, ?_⟩
    · change (Dm * Am * Di).det = 1
      rw [show Am = (A : Matrix (Fin 6) (Fin 6) k) from rfl]
      rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, hDmulDinv,
        Matrix.det_one]
    · change conjTr ψ (Dm * Am * Di) * antidiag 6 * (Dm * Am * Di) = antidiag 6
      calc conjTr ψ (Dm * Am * Di) * antidiag 6 * (Dm * Am * Di)
          = conjTr ψ Di * (conjTr ψ Am * (conjTr ψ Dm * antidiag 6 * Dm) * Am) * Di := by
              simp only [conjTr_mul, Matrix.mul_assoc]
        _ = conjTr ψ Di * (conjTr ψ Am * (μ • unitaryJInv6) * Am) * Di := by rw [hD2]
        _ = μ • (conjTr ψ Di * (conjTr ψ Am * unitaryJInv6 * Am) * Di) := by
              simp only [Matrix.mul_smul, Matrix.smul_mul]
        _ = μ • (conjTr ψ Di * unitaryJInv6 * Di) := by rw [hAm]
        _ = μ • (μ⁻¹ • antidiag 6) := by rw [hDi]
        _ = antidiag 6 := by rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have backward : ∀ (B : ↥(SU ψ 6)), ∃ (A : SL(6, k)), A ∈ unitaryGroup6 θ hθ ∧
      D * (A : GL (Fin 6) k) * D⁻¹ = (B : GL (Fin 6) k) := by
    intro B
    let Bm : Matrix (Fin 6) (Fin 6) k := ((B : GL (Fin 6) k) : Matrix (Fin 6) (Fin 6) k)
    have hBdet : Bm.det = 1 := B.2.1
    have hBform : conjTr ψ Bm * antidiag 6 * Bm = antidiag 6 := B.2.2
    let Am : Matrix (Fin 6) (Fin 6) k := Di * Bm * Dm
    have hAmdet : Am.det = 1 := by
      show (Di * Bm * Dm).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, hBdet, mul_one, ← Matrix.det_mul, hDimulD,
        Matrix.det_one]
    have hAmform : conjTr ψ Am * unitaryJInv6 * Am = unitaryJInv6 := by
      calc conjTr ψ Am * unitaryJInv6 * Am
          = conjTr ψ Dm * (conjTr ψ Bm * (conjTr ψ Di * unitaryJInv6 * Di) * Bm) * Dm := by
              simp only [Am, conjTr_mul, Matrix.mul_assoc]
        _ = conjTr ψ Dm * (conjTr ψ Bm * (μ⁻¹ • antidiag 6) * Bm) * Dm := by rw [hDi]
        _ = μ⁻¹ • (conjTr ψ Dm * (conjTr ψ Bm * antidiag 6 * Bm) * Dm) := by
              simp only [Matrix.mul_smul, Matrix.smul_mul]
        _ = μ⁻¹ • (conjTr ψ Dm * antidiag 6 * Dm) := by rw [hBform]
        _ = μ⁻¹ • (μ • unitaryJInv6) := by rw [hD2]
        _ = unitaryJInv6 := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨⟨Am, hAmdet⟩, (mem_unitaryGroup6_iff θ hθ ⟨Am, hAmdet⟩).mpr hAmform, ?_⟩
    have hAeq : Matrix.SpecialLinearGroup.toGL (⟨Am, hAmdet⟩ : SL(6, k)) =
        D⁻¹ * (B : GL (Fin 6) k) * D := by
      apply Units.ext
      change Am = Di * Bm * Dm
      rfl
    calc D * Matrix.SpecialLinearGroup.toGL (⟨Am, hAmdet⟩ : SL(6, k)) * D⁻¹
        = D * (D⁻¹ * (B : GL (Fin 6) k) * D) * D⁻¹ := by rw [hAeq]
      _ = (B : GL (Fin 6) k) := by group
  let Φ : ↥(unitaryGroup6 θ hθ) →* ↥(SU ψ 6) :=
    { toFun := fun A =>
        (⟨D * (A.1 : GL (Fin 6) k) * D⁻¹, forward A.1 A.2⟩ : ↥(SU ψ 6))
      map_one' := Subtype.ext (by
        show D * Matrix.SpecialLinearGroup.toGL (1 : SL(6, k)) * D⁻¹ = 1
        rw [map_one]
        group)
      map_mul' := fun A B => Subtype.ext (by
        show D * Matrix.SpecialLinearGroup.toGL ((A * B : ↥(unitaryGroup6 θ hθ)).1) * D⁻¹ =
          (D * Matrix.SpecialLinearGroup.toGL A.1 * D⁻¹) *
            (D * Matrix.SpecialLinearGroup.toGL B.1 * D⁻¹)
        have hAB : (A * B : ↥(unitaryGroup6 θ hθ)).1 = A.1 * B.1 := rfl
        rw [hAB, map_mul]
        group) }
  refine ⟨MulEquiv.ofBijective Φ ?_⟩
  refine ⟨?_, ?_⟩
  · intro A A' h
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val h))
  · intro B
    obtain ⟨A, hA, hAB⟩ := backward B
    exact ⟨⟨A, hA⟩, Subtype.ext hAB⟩

theorem blockData_unitaryGroup6
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) [Finite k] [CharP k 3]
    (hk : Nat.card k = 9) (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (hθ3 : ∀ c, θ c = c ^ 3 ^ 1) : BlockData ↥(unitaryGroup6 θ hθ) := by
  obtain ⟨μ, hμ0, hμ⟩ := exists_neg_of_involution θ hθ (exists_ne_of_card_nine hk θ hθ3)
  obtain ⟨e₁⟩ := exists_mulEquiv_SU6 θ hθ hμ0 hμ
  have hF : Nat.card k = (3 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hψ : involEquiv θ hθ = unitaryInvolution k 3 1 := by
    ext c
    rw [involEquiv_apply, unitaryInvolution_apply]
    exact hθ3 c
  have e₁' : ↥(unitaryGroup6 θ hθ) ≃* ↥(SU (unitaryInvolution k 3 1) 6) := by
    rw [← hψ]
    exact e₁
  have e₂ := equivStatedSU (F := k) (p := 3) (f := 1) hF 6
  have hpow : CFSG.Open.StatedSU 6 (3 ^ 1) k = CFSG.Open.StatedSU 6 3 k := by rw [pow_one]
  exact BlockData.of_mulEquiv (hpow ▸ (e₁'.trans e₂)).symm
    (blockData_statedSU hGA hk (n := 6) (Or.inr rfl))

end Unitary

end CFSG.OddStandard.HigherRank.F3
