module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeNormal
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def hD (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

@[expose] def hS : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem bar_eq_sq_of_cube (h : UnitaryFieldData ℓ f K) (hq : 3 ∣ ℓ ^ f + 1) {z : K}
    (hz : z ^ 3 = 1) : h.bar z = z ^ 2 := by
  rw [h.bar_apply]
  obtain ⟨k, hk⟩ := hq
  have h1 : z ^ (ℓ ^ f + 1) = 1 := by rw [hk, pow_mul, hz, one_pow]
  have h4 : z ^ (ℓ ^ f) * z = 1 := by rw [← pow_succ]; exact h1
  calc z ^ ℓ ^ f = z ^ ℓ ^ f * (z * z ^ 2) := by rw [← pow_succ', hz, mul_one]
    _ = (z ^ ℓ ^ f * z) * z ^ 2 := by ring
    _ = z ^ 2 := by rw [h4, one_mul]

theorem gram_eq_smul_one (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    {X Y P : Matrix (Fin 3) (Fin 3) K} {ω ξ : K} (hω : IsPrimitiveRoot ω 3) (hξ : ξ ^ 3 = 1)
    (hX : (X.map h.bar)ᵀ * X = 1) (hY : (Y.map h.bar)ᵀ * Y = 1)
    (hXP : X * P = P * hS) (hYP : Y * P = P * diagonal ![ξ, ξ * ω, ξ * ω ^ 2]) :
    ∃ ν : K, (P.map h.bar)ᵀ * P = ν • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω.pow_eq_one
  have hbξ : h.bar ξ = ξ ^ 2 := bar_eq_sq_of_cube h hq3 hξ
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    have := hω.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 < 3)
    exact this h2
  set G := (P.map h.bar)ᵀ * P with hG
  have hGdiag : ∀ {M : Matrix (Fin 3) (Fin 3) K}, (M.map h.bar)ᵀ * M = 1 →
      ∀ {N : Matrix (Fin 3) (Fin 3) K}, M * P = P * N →
        ((P * N).map h.bar)ᵀ * (P * N) = G := fun {M} hM {N} hMN => by
    rw [← hMN, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (M.map h.bar)ᵀ, hM, Matrix.one_mul]
  have h1 := hGdiag hY hYP
  have h2 := hGdiag hX hXP
  have hdiag : ∀ d : Fin 3 → K, ((P * diagonal d).map h.bar)ᵀ * (P * diagonal d) =
      diagonal (fun k => h.bar (d k)) * G * diagonal d := fun d => by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, hG, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have hD : ∀ k l : Fin 3, G k l = h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) *
      G k l * (![ξ, ξ * ω, ξ * ω ^ 2] l) := by
    intro k l
    have := congrFun (congrFun h1 k) l
    rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this.symm
  have key : ∀ (c z : K), c ≠ 1 → z = c * z → z = 0 := fun c z hc hz => by
    have : (1 - c) * z = 0 := by linear_combination hz
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc))
  have p01 : h.bar ξ * (ξ * ω) = ω := by rw [hbξ]; linear_combination ω * hξ
  have p02 : h.bar ξ * (ξ * ω ^ 2) = ω ^ 2 := by rw [hbξ]; linear_combination ω ^ 2 * hξ
  have p10 : h.bar (ξ * ω) * ξ = ω ^ 2 := by
    rw [map_mul, hbξ, hbω]; linear_combination ω ^ 2 * hξ
  have p12 : h.bar (ξ * ω) * (ξ * ω ^ 2) = ω := by
    rw [map_mul, hbξ, hbω]; linear_combination ω ^ 4 * hξ + ω * hω3
  have p20 : h.bar (ξ * ω ^ 2) * ξ = ω := by
    rw [map_mul, hbξ, map_pow, hbω]; linear_combination ω ^ 4 * hξ + ω * hω3
  have p21 : h.bar (ξ * ω ^ 2) * (ξ * ω) = ω ^ 2 := by
    rw [map_mul, hbξ, map_pow, hbω]; linear_combination ω ^ 5 * hξ + ω ^ 2 * hω3
  have offd : ∀ (k l : Fin 3) (c : K), c ≠ 1 →
      h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * (![ξ, ξ * ω, ξ * ω ^ 2] l) = c → G k l = 0 :=
    fun k l c hc hcl => key c _ hc (by
      calc G k l = h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * G k l * (![ξ, ξ * ω, ξ * ω ^ 2] l) :=
            hD k l
        _ = (h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * (![ξ, ξ * ω, ξ * ω ^ 2] l)) * G k l := by ring
        _ = c * G k l := by rw [hcl])
  have g01 : G 0 1 = 0 := offd 0 1 ω hω1 p01
  have g02 : G 0 2 = 0 := offd 0 2 (ω ^ 2) hω2 p02
  have g10 : G 1 0 = 0 := offd 1 0 (ω ^ 2) hω2 p10
  have g12 : G 1 2 = 0 := offd 1 2 ω hω1 p12
  have g20 : G 2 0 = 0 := offd 2 0 ω hω1 p20
  have g21 : G 2 1 = 0 := offd 2 1 (ω ^ 2) hω2 p21
  have hSbar : (hS : Matrix (Fin 3) (Fin 3) K).map h.bar = hS := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hS]
  have h2' : hSᵀ * G * hS = G := by
    calc hSᵀ * G * hS = ((P * hS).map h.bar)ᵀ * (P * hS) := by
          rw [Matrix.map_mul, hSbar, Matrix.transpose_mul, hG]
          simp only [Matrix.mul_assoc]
      _ = G := h2
  have s00 := congrFun (congrFun h2' 0) 0
  have s11 := congrFun (congrFun h2' 1) 1
  simp [hS, Matrix.mul_apply, Fin.sum_univ_three] at s00 s11
  refine ⟨G 0 0, ?_⟩
  ext k l
  fin_cases k <;> fin_cases l <;> simp [g01, g02, g10, g12, g20, g21, ← s00, ← s11]

theorem exists_unitary_heisenberg_basis (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    {x y : GL (Fin 3) K} (hx : x ∈ unitarySU ℓ f K 3) (hy : y ∈ unitarySU ℓ f K 3)
    (hyx : ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) =
      c • ((x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)))
    (hne : (x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) ≠
      (y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K))
    (hx3 : ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (P : GL (Fin 3) K) (ω ξ : K), P ∈ primeFormUnitary h (idGram K 3) ∧ IsPrimitiveRoot ω 3 ∧
      ξ ^ 3 = 1 ∧ (x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * hS ∧
      (y : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] := by
  obtain ⟨hdx, hux⟩ := (mem_unitarySU_iff h).1 hx
  obtain ⟨hdy, huy⟩ := (mem_unitarySU_iff h).1 hy
  set X : Matrix (Fin 3) (Fin 3) K := (x : Matrix (Fin 3) (Fin 3) K) with hX
  set Y : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hY
  let x' : Matrix.SpecialLinearGroup (Fin 3) K := ⟨X, hdx⟩
  let y' : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Y, hdy⟩
  obtain ⟨c, hc⟩ := hyx
  obtain ⟨c₃, hc₃⟩ := hx3
  have hcc : c ^ 3 = 1 := by
    have := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hdx, hdy] at this
    simpa using this.symm
  have hc₃c : c₃ ^ 3 = 1 := by
    have := congrArg Matrix.det hc₃
    rw [Matrix.det_pow, Matrix.det_smul, hdx] at this
    simpa using this.symm
  have hcomm : ⁅y', x'⁆ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨c, by simpa using hcc, ?_⟩
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_inv]
    show Matrix.scalar (Fin 3) c = Y * X * Y.adjugate * X.adjugate
    have h1 : Y * X * Y.adjugate * X.adjugate = c • (X * (Y * Y.adjugate) * X.adjugate) := by
      rw [hc, Matrix.smul_mul, Matrix.smul_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_adjugate, hdy, one_smul, Matrix.mul_one, Matrix.mul_adjugate, hdx, one_smul]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hne' : x' * y' ≠ y' * x' := fun hxy => hne (congrArg Subtype.val hxy)
  have hx3' : x' ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨c₃, by simpa using hc₃c, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow]
    show Matrix.scalar (Fin 3) c₃ = X ^ 3
    rw [hc₃]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  obtain ⟨P₀, ω, ξ, hξ, hωq, hω1, hconjY, hconjX⟩ := exists_heisenberg_basis hcomm hne' hx3'
  have hP₀P : (P₀ : Matrix (Fin 3) (Fin 3) K) *
      ((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXP₀ : X * (P₀ : Matrix (Fin 3) (Fin 3) K) = (P₀ : Matrix (Fin 3) (Fin 3) K) * hS := by
    have h1 := congrArg Subtype.val hconjX
    rw [conjUnit_coe, inv_inv] at h1
    have h2 : ((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * X *
        (P₀ : Matrix (Fin 3) (Fin 3) K) = hS := h1
    calc X * (P₀ : Matrix (Fin 3) (Fin 3) K)
        = ((P₀ : Matrix (Fin 3) (Fin 3) K) * ((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            X * (P₀ : Matrix (Fin 3) (Fin 3) K) := by rw [hP₀P, Matrix.one_mul]
      _ = (P₀ : Matrix (Fin 3) (Fin 3) K) * (((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            X * (P₀ : Matrix (Fin 3) (Fin 3) K)) := by simp only [Matrix.mul_assoc]
      _ = (P₀ : Matrix (Fin 3) (Fin 3) K) * hS := by rw [h2]
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hωq
  have hξ3 : ξ ^ 3 = 1 := by linear_combination hξ - ξ ^ 3 * hω3
  have hYP₀ : Y * (P₀ : Matrix (Fin 3) (Fin 3) K) =
      (P₀ : Matrix (Fin 3) (Fin 3) K) * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] := by
    have h1 := congrArg Subtype.val hconjY
    rw [conjUnit_coe, inv_inv] at h1
    have h2 : ((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Y *
        (P₀ : Matrix (Fin 3) (Fin 3) K) = diagonal ![ξ, ξ * ω, ξ * ω ^ 2] := by
      rw [show diagonal ![ξ, ξ * ω, ξ * ω ^ 2] = (!![ξ, 0, 0; 0, ξ * ω, 0; 0, 0, ξ * ω ^ 2] :
        Matrix (Fin 3) (Fin 3) K) by
          ext i j; fin_cases i <;> fin_cases j <;> simp]
      exact h1
    calc Y * (P₀ : Matrix (Fin 3) (Fin 3) K)
        = ((P₀ : Matrix (Fin 3) (Fin 3) K) * ((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            Y * (P₀ : Matrix (Fin 3) (Fin 3) K) := by rw [hP₀P, Matrix.one_mul]
      _ = (P₀ : Matrix (Fin 3) (Fin 3) K) * (((P₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            Y * (P₀ : Matrix (Fin 3) (Fin 3) K)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]
  have hprim : IsPrimitiveRoot ω 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := orderOf_eq_prime hω3 hω1
    rw [← h1]
    exact IsPrimitiveRoot.orderOf ω
  obtain ⟨ν, hν⟩ := gram_eq_smul_one h hq3 hprim hξ3 hux huy hXP₀ hYP₀
  have hν00 : ν = ∑ i : Fin 3, h.bar ((P₀ : Matrix (Fin 3) (Fin 3) K) i 0) *
      (P₀ : Matrix (Fin 3) (Fin 3) K) i 0 := by
    have h00 := congrFun (congrFun hν 0) 0
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] using
      h00.symm
  have hbarν : h.bar ν = ν := by
    conv_lhs => rw [hν00]
    rw [map_sum]
    conv_rhs => rw [hν00]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, h.bar_bar, mul_comm]
  have hdetP₀ : (P₀ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hP₀P
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hν0 : ν ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hν
    have hdb : ((P₀ : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
        h.bar (P₀ : Matrix (Fin 3) (Fin 3) K).det := (RingHom.map_det h.bar _).symm
    rw [h0, zero_smul, Matrix.det_mul, Matrix.det_transpose, hdb] at h1
    have h2 : (0 : Matrix (Fin 3) (Fin 3) K).det = 0 := by
      have : Nonempty (Fin 3) := ⟨0⟩
      exact Matrix.det_zero
    rw [h2] at h1
    exact mul_ne_zero ((h.bar_eq_zero_iff).not.mpr hdetP₀) hdetP₀ h1
  have hνfix : (ν⁻¹ : K) ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hbarν]
  obtain ⟨κ, hκ⟩ := h.normHom_surjective ⟨ν⁻¹, hνfix⟩
  have hκnorm : κ * h.bar κ = ν⁻¹ := by
    have := congrArg Subtype.val hκ
    simpa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] using this
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hκnorm
    exact inv_ne_zero hν0 hκnorm.symm
  set P : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 κ hκ0) * P₀ with hPdef
  have hPmat : (P : Matrix (Fin 3) (Fin 3) K) = κ • (P₀ : Matrix (Fin 3) (Fin 3) K) := by
    rw [hPdef, Units.val_mul, GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hunit : ((P : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hPmat]
    have h1 : ((κ • (P₀ : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
        (κ • (P₀ : Matrix (Fin 3) (Fin 3) K)) = (h.bar κ * κ) •
          (((P₀ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (P₀ : Matrix (Fin 3) (Fin 3) K)) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h1, hν, smul_smul]
    have : h.bar κ * κ * ν = 1 := by
      rw [mul_comm (h.bar κ) κ, hκnorm]; exact inv_mul_cancel₀ hν0
    rw [this, one_smul]
  refine ⟨P, ω, ξ, ?_, hprim, hξ3, ?_, ?_⟩
  · rw [mem_primeFormUnitary]
    simpa [idGram] using hunit
  · rw [hPmat, Matrix.mul_smul, hXP₀, Matrix.smul_mul]
  · rw [hPmat, Matrix.mul_smul, hYP₀, Matrix.smul_mul]

@[expose] def heisLines (ω : K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {hD ω, hS, hD ω * hS, hD ω * hS * hS}

@[expose] def UnitaryHeisCore : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ ω : K, IsPrimitiveRoot ω 3 →
      Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω, ∃ c : K,
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
          c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))} = ⊤

section Transfer

@[expose] def piSU (ℓ f : ℕ) (K : Type) [Field K] :
    unitarySU ℓ f K 3 →* StatedProj (StatedSU 3 (ℓ ^ f) K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (unitarySU ℓ f K 3))

theorem piSU_surjective : Function.Surjective (piSU ℓ f K) := QuotientGroup.mk'_surjective _

theorem piSU_eq_iff {a b : unitarySU ℓ f K 3} :
    piSU ℓ f K a = piSU ℓ f K b ↔
      ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin 3) u =
        ((a⁻¹ * b : unitarySU ℓ f K 3) : GL (Fin 3) K) := by
  unfold piSU
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range]

theorem piSU_commute_of_smul (h : UnitaryFieldData ℓ f K) (a b : unitarySU ℓ f K 3) (c : K)
    (hab : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :
    piSU ℓ f K a * piSU ℓ f K b = piSU ℓ f K b * piSU ℓ f K a := by
  have hda := ((mem_unitarySU_iff h).1 a.2).1
  have hdb := ((mem_unitarySU_iff h).1 b.2).1
  have hc : c ≠ 0 := by
    rintro rfl
    have hdet := congrArg Matrix.det hab
    rw [Matrix.det_mul, zero_smul, hda, hdb] at hdet
    have : Nonempty (Fin 3) := ⟨0⟩
    rw [Matrix.det_zero] at hdet
    simp at hdet
  rw [← map_mul, ← map_mul, piSU_eq_iff]
  refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
  have hGL : ((a * b : unitarySU ℓ f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc) *
        ((b * a : unitarySU ℓ f K 3) : GL (Fin 3) K) := by
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    rw [hab]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hcom := commute_scalar (Units.mk0 c hc) ((b : GL (Fin 3) K) * (a : GL (Fin 3) K))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [show ((a : GL (Fin 3) K) * (b : GL (Fin 3) K)) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc) * ((b : GL (Fin 3) K) * (a : GL (Fin 3) K))
      from by simpa using hGL, _root_.mul_inv_rev, map_inv]
  rw [mul_assoc, ← hcom.inv_right.eq, inv_mul_cancel_left]

theorem piSU_eq_one_commute {z : unitarySU ℓ f K 3} (hz : piSU ℓ f K z = 1)
    (w : unitarySU ℓ f K 3) : z * w = w * z := by
  rw [← map_one (piSU ℓ f K), piSU_eq_iff] at hz
  obtain ⟨u, hu⟩ := hz
  have hz' : ((z : unitarySU ℓ f K 3) : GL (Fin 3) K) =
      (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by
    rw [hu]; simp
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hz']
  exact ((commute_scalar u (w : GL (Fin 3) K)).inv_right).eq.symm

theorem exists_smul_of_piSU_eq {a b : unitarySU ℓ f K 3} (hab : piSU ℓ f K a = piSU ℓ f K b) :
    ∃ c : K, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨u, hu⟩ := (piSU_eq_iff).1 hab
  refine ⟨((u⁻¹ : Kˣ) : K), ?_⟩
  have h1 : ((b : unitarySU ℓ f K 3) : GL (Fin 3) K) =
      (a : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hu]; simp
  have h2 : ((a : unitarySU ℓ f K 3) : GL (Fin 3) K) =
      (b : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
    rw [h1, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, Matrix.smul_eq_mul_diagonal]

theorem closure_centralizers_statedProj_su_three_nonab (hcore : UnitaryHeisCore)
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2)
    (E : Subgroup (StatedProj (StatedSU 3 (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hnc : ∃ x y : unitarySU ℓ f K 3, piSU ℓ f K x ∈ E ∧ piSU ℓ f K y ∈ E ∧ x * y ≠ y * x) :
    Subgroup.closure {k : StatedProj (StatedSU 3 (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  classical
  obtain ⟨x, y, hxE, hyE, hxy⟩ := hnc
  obtain ⟨c, hc⟩ : ∃ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    obtain ⟨c, hc⟩ := exists_smul_of_piSU_eq (a := y * x) (b := x * y)
      (by rw [map_mul, map_mul]; exact hcomm _ hyE _ hxE)
    exact ⟨c, by simpa using hc⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    obtain ⟨c, hc⟩ := exists_smul_of_piSU_eq (a := x ^ 3) (b := 1)
      (by rw [map_pow, map_one]; exact hexp _ hxE)
    exact ⟨c, by simpa using hc⟩
  have hne : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun hxy' =>
    hxy (Subtype.ext (Units.ext hxy'))
  obtain ⟨P, ω, ξ, hPmem, hprim, hξ3, hXP, hYP⟩ :=
    exists_unitary_heisenberg_basis h hq3 x.2 y.2 ⟨c, hc⟩ hne ⟨c₃, hc₃⟩
  set X : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hX
  set Y : Matrix (Fin 3) (Fin 3) K := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hY
  set Pm : Matrix (Fin 3) (Fin 3) K := (P : Matrix (Fin 3) (Fin 3) K) with hPm
  set Pi : Matrix (Fin 3) (Fin 3) K := ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hconjS : Pm * hS * Pi = X := by
    rw [← hXP, Matrix.mul_assoc, hPPi, Matrix.mul_one]
  have hdiag : diagonal ![ξ, ξ * ω, ξ * ω ^ 2] = ξ • hD ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD]
  have hconjD : Pm * hD ω * Pi = ξ⁻¹ • Y := by
    have h1 : Y * Pm = ξ • (Pm * hD ω) := by
      rw [hYP, hdiag, Matrix.mul_smul]
    calc Pm * hD ω * Pi = ξ⁻¹ • (ξ • (Pm * hD ω)) * Pi := by
          rw [smul_smul, inv_mul_cancel₀ hξ0, one_smul]
      _ = ξ⁻¹ • (Y * Pm * Pi) := by rw [← h1, Matrix.smul_mul]
      _ = ξ⁻¹ • Y := by rw [Matrix.mul_assoc, hPPi, Matrix.mul_one]
  have hconjmul : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      Pm * (A * B) * Pi = (Pm * A * Pi) * (Pm * B * Pi) := by
    intro A B
    calc Pm * (A * B) * Pi = Pm * A * (Pi * Pm) * B * Pi := by
          rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (Pm * A * Pi) * (Pm * B * Pi) := by simp only [Matrix.mul_assoc]
  have hnon : ∀ w : unitarySU ℓ f K 3, (w = x ∨ w = y ∨ w = y * x ∨ w = y * x * x) →
      piSU ℓ f K w ≠ 1 := by
    intro w hw hw1
    have hcen := piSU_eq_one_commute hw1
    rcases hw with rfl | rfl | rfl | rfl
    · exact hxy (hcen y)
    · exact hxy (hcen x).symm
    · apply hxy
      have h2 : y * x * x = x * (y * x) := hcen x
      have h3 : y * x * x = x * y * x := by rw [h2, mul_assoc]
      exact (mul_right_cancel h3).symm
    · apply hxy
      have h2 : y * x * x * x = x * (y * x * x) := hcen x
      have h3 : (y * x) * (x * x) = (x * y) * (x * x) := by
        calc (y * x) * (x * x) = y * x * x * x := by simp only [mul_assoc]
          _ = x * (y * x * x) := h2
          _ = (x * y) * (x * x) := by simp only [mul_assoc]
      exact (mul_right_cancel h3).symm
  have hlines : ∀ M ∈ heisLines ω, ∃ (z : unitarySU ℓ f K 3) (r : K), r ≠ 0 ∧
      piSU ℓ f K z ∈ E ∧ piSU ℓ f K z ≠ 1 ∧
      Pm * M * Pi = r • ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro M hM
    simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact ⟨y, ξ⁻¹, inv_ne_zero hξ0, hyE, hnon y (Or.inr (Or.inl rfl)), hconjD⟩
    · exact ⟨x, 1, one_ne_zero, hxE, hnon x (Or.inl rfl), by rw [hconjS, one_smul]⟩
    · refine ⟨y * x, ξ⁻¹, inv_ne_zero hξ0, ?_, hnon _ (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      · rw [map_mul]; exact E.mul_mem hyE hxE
      · rw [hconjmul, hconjD, hconjS, Matrix.smul_mul]; simp [Subgroup.coe_mul, hX, hY]
    · refine ⟨y * x * x, ξ⁻¹, inv_ne_zero hξ0, ?_, hnon _ (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      · rw [map_mul, map_mul]; exact E.mul_mem (E.mul_mem hyE hxE) hxE
      · rw [hconjmul, hconjmul, hconjD, hconjS, Matrix.smul_mul, Matrix.smul_mul]
        simp [Subgroup.coe_mul, hX, hY]
  set Pu : primeFormUnitary h (idGram K 3) := ⟨P, hPmem⟩ with hPu
  set φ := conjSU h Pu with hφ
  set C := Subgroup.closure {k : StatedProj (StatedSU 3 (ℓ ^ f) K) |
    ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  set Kpre : Subgroup (unitarySU ℓ f K 3) := C.comap (piSU ℓ f K) with hKpre
  have hmain : ∀ g ∈ {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω, ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}, φ g ∈ Kpre := by
    rintro g ⟨M, hM, c, hgM⟩
    obtain ⟨z, r, hr, hzE, hz1, hrz⟩ := hlines M hM
    have hG' : (((φ g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi := by
      rw [hφ, coe_conjSU, Units.val_mul, Units.val_mul]
    have hrel : (((φ g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        c • (((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((φ g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      rw [hG']
      have h1 : (Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi) * (Pm * M * Pi) =
          c • ((Pm * M * Pi) * (Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi)) := by
        rw [← hconjmul, ← hconjmul, hgM, Matrix.mul_smul, Matrix.smul_mul]
      rw [hrz, Matrix.mul_smul, Matrix.smul_mul] at h1
      have h2 : r • ((Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi) *
          ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
          r • (c • (((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi))) := by
        rw [h1, smul_comm c r]
      exact smul_right_injective _ hr h2
    show piSU ℓ f K (φ g) ∈ C
    exact Subgroup.subset_closure ⟨piSU ℓ f K z, hzE, hz1,
      piSU_commute_of_smul h (φ g) z c hrel⟩
  have hcl := hcore ℓ f K h hq3 hq2 ω hprim
  have hmap : Subgroup.map (φ : unitarySU ℓ f K 3 →* unitarySU ℓ f K 3)
      (Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω, ∃ c : K,
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
          c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}) ≤ Kpre := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hmain g hg
  rw [hcl, Subgroup.map_top_of_surjective _ φ.surjective] at hmap
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := piSU_surjective k
  exact Subgroup.mem_comap.1 (hmap (Subgroup.mem_top g))

end Transfer

end CFSG.LieType.SeitzGeneration
