module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabArith
public import CFSG.LieType.SeitzGeneration.UnitaryNonabToral
public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPth
public import CFSG.LieType.SeitzGeneration.UnitaryNonabHeis
public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.UnitaryNonabLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

@[expose] def planeFixUnW (ℓ f n p : ℕ) (K : Type) [Field K] (x y : GL (Fin n) K) :
    Set (unitarySU ℓ f K n) :=
  {g | ∃ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) ∧
    g ∈ FixUn ℓ f n K ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}

theorem planeW_pow_smul {X Y : Matrix (Fin n) (Fin n) K} {c : K} (hYX : Y * X = c • (X * Y))
    (hc0 : c ≠ 0) (a b j : ℕ) :
    ∃ s : K, s ≠ 0 ∧ (X ^ a * Y ^ b) ^ j = s • (X ^ (a * j) * Y ^ (b * j)) := by
  refine ⟨(c ^ (a * b)) ^ (j.choose 2), pow_ne_zero _ (pow_ne_zero _ hc0), ?_⟩
  rw [qcommMat_pow_prod (qcommMat_pow_pow hYX a b) j, ← pow_mul X a j, ← pow_mul Y b j]

theorem planeW_caseI {X Y : Matrix (Fin n) (Fin n) K} {c : K} (hYX : Y * X = c • (X * Y))
    (hc0 : c ≠ 0) (a b i j : ℕ) :
    ∃ s : K, s ≠ 0 ∧ X ^ i * (X ^ a * Y ^ b) ^ j = s • (X ^ (i + a * j) * Y ^ (b * j)) := by
  obtain ⟨s, hs, hpow⟩ := planeW_pow_smul hYX hc0 a b j
  refine ⟨s, hs, ?_⟩
  rw [hpow, Matrix.mul_smul, pow_add, Matrix.mul_assoc]

theorem planeW_caseII {X Y : Matrix (Fin n) (Fin n) K} {c : K} (hYX : Y * X = c • (X * Y))
    (hc0 : c ≠ 0) (a b i j : ℕ) :
    ∃ s : K, s ≠ 0 ∧ Y ^ i * (X ^ a * Y ^ b) ^ j = s • (X ^ (a * j) * Y ^ (i + b * j)) := by
  obtain ⟨s, hs, hpow⟩ := planeW_pow_smul hYX hc0 a b j
  refine ⟨s * c ^ ((a * j) * i), mul_ne_zero hs (pow_ne_zero _ hc0), ?_⟩
  rw [hpow, Matrix.mul_smul, ← Matrix.mul_assoc, qcommMat_pow_pow hYX (a * j) i,
    Matrix.smul_mul, Matrix.mul_assoc, ← pow_add, smul_smul]

theorem planeW_comm_caseI {X Y : Matrix (Fin n) (Fin n) K} {c : K}
    (hYX : Y * X = c • (X * Y)) (a b : ℕ) :
    (X ^ a * Y ^ b) * X = c ^ b • (X * (X ^ a * Y ^ b)) := by
  have h := qcommMat_pow_pow hYX 1 b
  simp only [pow_one, one_mul] at h
  rw [Matrix.mul_assoc, h, Matrix.mul_smul, mat_pow_mul_comm]

theorem planeW_comm_caseII {X Y : Matrix (Fin n) (Fin n) K} {c : K}
    (hYX : Y * X = c • (X * Y)) (hc0 : c ≠ 0) (a b : ℕ) :
    (X ^ a * Y ^ b) * Y = (c ^ a)⁻¹ • (Y * (X ^ a * Y ^ b)) := by
  have h := qcommMat_pow_pow hYX a 1
  simp only [pow_one, mul_one] at h
  have hYb : Y * Y ^ b = Y ^ b * Y := (Commute.self_pow Y b).eq
  have key : Y * (X ^ a * Y ^ b) = c ^ a • ((X ^ a * Y ^ b) * Y) := by
    calc Y * (X ^ a * Y ^ b) = (Y * X ^ a) * Y ^ b := (Matrix.mul_assoc _ _ _).symm
      _ = c ^ a • ((X ^ a * Y) * Y ^ b) := by rw [h, Matrix.smul_mul]
      _ = c ^ a • (X ^ a * (Y * Y ^ b)) := by rw [Matrix.mul_assoc (X ^ a) Y (Y ^ b)]
      _ = c ^ a • (X ^ a * (Y ^ b * Y)) := by rw [hYb]
      _ = c ^ a • ((X ^ a * Y ^ b) * Y) := by rw [Matrix.mul_assoc]
  rw [key, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc0), one_smul]

theorem planeW_coe_word (x y : GL (Fin n) K) (a b : ℕ) :
    ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) ^ a * (y : Matrix (Fin n) (Fin n) K) ^ b := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

theorem planeW_eq_inv_smul_one {M : Matrix (Fin n) (Fin n) K} {s : K} (hs : s ≠ 0)
    (h : s • M = 1) : M = s⁻¹ • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [← h, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem planeW_pow_card_succ (h : UnitaryFieldData ℓ f K) {α : K} (hα : h.bar α * α = 1) :
    α ^ (ℓ ^ f + 1) = 1 := by
  rw [pow_succ, ← h.bar_apply, hα]

theorem planeW_det_ne_zero (x : GL (Fin n) K) : (x : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero

theorem planeW_scalar_mem (h : UnitaryFieldData ℓ f K) {u : K} (hu0 : u ≠ 0)
    (hu : h.bar u * u = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 u hu0) ∈
      primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, coe_scalarGL, Units.val_mk0]
  have h1 : ((u • (1 : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ =
      h.bar u • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  rw [h1]
  simp only [idGram, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    hu, one_smul]

theorem planeW_indep {x y x₁ y₁ : GL (Fin n) K}
    (hW : ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∃ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) ∧ ∃ s : K, s ≠ 0 ∧
      ((x₁ ^ i * y₁ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hind : ∀ a b : ℕ, (∃ c' : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c' • 1) → p ∣ a ∧ p ∣ b)
    (i j : ℕ) (ht : ∃ t : K, ((x₁ ^ i * y₁ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      t • 1) : p ∣ i ∧ p ∣ j := by
  obtain ⟨t, ht⟩ := ht
  by_contra hij
  obtain ⟨A, B, hAB, s, hs, hEq⟩ := hW i j hij
  apply hAB
  apply hind A B
  refine ⟨s⁻¹ * t, ?_⟩
  calc ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = s⁻¹ • (s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • (t • (1 : Matrix (Fin n) (Fin n) K)) := by rw [← hEq, ht]
    _ = (s⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) K) := by rw [smul_smul]

theorem planeW_cent [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)} {x y x₁ y₁ : GL (Fin n) K}
    (hW : ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∃ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) ∧ ∃ s : K, s ≠ 0 ∧
      ((x₁ ^ i * y₁ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hH : ∀ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) →
      HeisTensor.Cent H ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (i j : ℕ) (hij : ¬ (p ∣ i ∧ p ∣ j)) :
    HeisTensor.Cent H ((x₁ ^ i * y₁ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨A, B, hAB, s, hs, hEq⟩ := hW i j hij
  rw [hEq]
  exact HeisTensor.Cent.smul (hH A B hAB) hs

theorem eq_top_of_kernel_pair [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hT : TorusFourierGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (hn : 3 ≤ n)
    {x y x₁ y₁ : GL (Fin n) K} (hx₁ : x₁ ∈ primeFormUnitary h (idGram K n))
    (hy₁ : y₁ ∈ primeFormUnitary h (idGram K n)) {α₁ ν c₁ : K} (hα₁ : α₁ ≠ 0) (hν0 : ν ≠ 0)
    (hνN : h.bar ν * ν = 1)
    (hx₁p : ((x₁ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α₁ • 1)
    (hy₁p : ((y₁ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ p) • 1)
    (hc₁ : (y₁ : Matrix (Fin n) (Fin n) K) * (x₁ : Matrix (Fin n) (Fin n) K) =
      c₁ • ((x₁ : Matrix (Fin n) (Fin n) K) * (y₁ : Matrix (Fin n) (Fin n) K)))
    (hexcl₁ : n = p → c₁ ≠ 1 → ∃ μ : K, μ ^ p = α₁)
    (hW : ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∃ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) ∧ ∃ s : K, s ≠ 0 ∧
      ((x₁ ^ i * y₁ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hind : ∀ a b : ℕ, (∃ c' : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c' • 1) → p ∣ a ∧ p ∣ b)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hH : ∀ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) →
      HeisTensor.Cent H ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    H = ⊤ := by
  classical
  haveI := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hp2 : p ≠ 2 := by omega
  have hp1 : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.mp hd)
  have hcent := planeW_cent hW hH
  have hindW := planeW_indep hW hind
  have hcp₁ : c₁ ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα₁ hx₁p hc₁
  have hcentX : HeisTensor.Cent H ((x₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := hcent 1 0 (fun hd => hp1 hd.1)
    simpa using this
  have hcentY : HeisTensor.Cent H ((y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := hcent 0 1 (fun hd => hp1 hd.2)
    simpa using this
  by_cases hc1 : c₁ = 1
  ·
    subst hc1
    have hcomm : (x₁ : Matrix (Fin n) (Fin n) K) * (y₁ : Matrix (Fin n) (Fin n) K) =
        (y₁ : Matrix (Fin n) (Fin n) K) * (x₁ : Matrix (Fin n) (Fin n) K) := by
      rw [hc₁, one_smul]
    have hα₁N : h.bar α₁ * α₁ = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hx₁ hx₁p
    have hν'N : h.bar ν⁻¹ * ν⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hνN, inv_one]
    obtain ⟨y', hy'def⟩ : ∃ g : GL (Fin n) K,
        g = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 ν⁻¹ (inv_ne_zero hν0)) * y₁ :=
      ⟨_, rfl⟩
    have hy'M : (y' : Matrix (Fin n) (Fin n) K) = ν⁻¹ • (y₁ : Matrix (Fin n) (Fin n) K) := by
      rw [hy'def, Units.val_mul, coe_scalarGL, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
    have hy'G : y' ∈ primeFormUnitary h (idGram K n) := by
      rw [hy'def]
      exact Subgroup.mul_mem _ (planeW_scalar_mem h (inv_ne_zero hν0) hν'N) hy₁
    have hy₁M : (y₁ : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hy₁p
    have hy'pow : y' ^ p = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hy'M, smul_pow, hy₁M, smul_smul, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero _ hν0), one_smul, Units.val_one]
    have hy'1 : ∀ t : K, (y' : Matrix (Fin n) (Fin n) K) ≠ t • 1 := by
      intro t ht
      rw [hy'M] at ht
      have hY : (y₁ : Matrix (Fin n) (Fin n) K) = (ν * t) • 1 := by
        calc (y₁ : Matrix (Fin n) (Fin n) K) = ν • (ν⁻¹ • (y₁ : Matrix (Fin n) (Fin n) K)) := by
              rw [smul_smul, mul_inv_cancel₀ hν0, one_smul]
          _ = ν • (t • 1) := by rw [ht]
          _ = (ν * t) • 1 := by rw [smul_smul]
      have h01 : ∃ t' : K, ((x₁ ^ 0 * y₁ ^ 1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          t' • 1 := ⟨ν * t, by simpa using hY⟩
      exact hp1 (hindW 0 1 h01).2
    have hy'comm : x₁ * y' = y' * x₁ := by
      apply Units.ext
      simp only [Units.val_mul, hy'M, Matrix.smul_mul, Matrix.mul_smul, hcomm]
    by_cases hμ : ∃ μ : K, μ ^ p = α₁
    ·
      obtain ⟨μ, hμp⟩ := hμ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hμp
        exact hα₁ hμp.symm
      have hμN : h.bar μ * μ = 1 :=
        bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ0 hμp (planeW_pow_card_succ h hα₁N)
      have hμ'N : h.bar μ⁻¹ * μ⁻¹ = 1 := by
        rw [map_inv₀, ← mul_inv, hμN, inv_one]
      obtain ⟨x', hx'def⟩ : ∃ g : GL (Fin n) K,
          g = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ⁻¹ (inv_ne_zero hμ0)) * x₁ :=
        ⟨_, rfl⟩
      have hx'M : (x' : Matrix (Fin n) (Fin n) K) = μ⁻¹ • (x₁ : Matrix (Fin n) (Fin n) K) := by
        rw [hx'def, Units.val_mul, coe_scalarGL, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
      have hx'G : x' ∈ primeFormUnitary h (idGram K n) := by
        rw [hx'def]
        exact Subgroup.mul_mem _ (planeW_scalar_mem h (inv_ne_zero hμ0) hμ'N) hx₁
      have hx₁M : (x₁ : Matrix (Fin n) (Fin n) K) ^ p = α₁ • 1 := by
        rw [← Units.val_pow_eq_pow_val]; exact hx₁p
      have hx'pow : x' ^ p = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hx'M, smul_pow, hx₁M, smul_smul, inv_pow, hμp,
          inv_mul_cancel₀ hα₁, one_smul, Units.val_one]
      have hx'y' : x' * y' = y' * x' := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hx'M, hy'M]
        simp only [Matrix.smul_mul, Matrix.mul_smul]
        rw [hcomm, smul_comm]
      have hsc : ∀ a b : ℕ, ((x' ^ a * y' ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (μ⁻¹ ^ a * ν⁻¹ ^ b) • ((x₁ ^ a * y₁ ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        intro a b
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, hx'M, hy'M, smul_pow,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [mul_comm (ν⁻¹ ^ b) (μ⁻¹ ^ a)]
      have hind' : ∀ a b : ℕ, x' ^ a * y' ^ b = 1 → p ∣ a ∧ p ∣ b := by
        intro a b hab
        have hs : μ⁻¹ ^ a * ν⁻¹ ^ b ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (inv_ne_zero hμ0)) (pow_ne_zero _ (inv_ne_zero hν0))
        have hM : ((x' ^ a * y' ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
          rw [hab, Units.val_one]
        rw [hsc a b] at hM
        exact hindW a b ⟨(μ⁻¹ ^ a * ν⁻¹ ^ b)⁻¹, planeW_eq_inv_smul_one hs hM⟩
      have hH' : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) →
          HeisTensor.Cent H ((x' ^ a * y' ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        intro a b hab
        rw [hsc a b]
        exact HeisTensor.Cent.smul (hcent a b hab)
          (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hμ0)) (pow_ne_zero _ (inv_ne_zero hν0)))
      exact eq_top_of_abelian_pth h hp hp5 hpq (by omega) hx'G hy'G hx'y' hx'pow hy'pow hind' hH'
    ·
      have hy3' : ((y' ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [hy'pow, Units.val_one]
      have hHy : HeisTensor.Cent H (y' : Matrix (Fin n) (Fin n) K) := by
        rw [hy'M]
        exact HeisTensor.Cent.smul hcentY (inv_ne_zero hν0)
      exact NonPth.eq_top_of_nonpth_pair h hp hp5 hpq hx₁ hy'G hy'comm hx₁p hμ hy3' hy'1 hcentX
        hHy
  ·
    have hζ : IsPrimitiveRoot c₁ p := by
      rw [← orderOf_eq_prime hcp₁ hc1]
      exact IsPrimitiveRoot.orderOf c₁
    have hcn : c₁ ^ n = 1 := by
      have hdet := congrArg Matrix.det hc₁
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hdet
      have hD : (x₁ : Matrix (Fin n) (Fin n) K).det * (y₁ : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
        mul_ne_zero (planeW_det_ne_zero x₁) (planeW_det_ne_zero y₁)
      apply mul_right_cancel₀ hD
      linear_combination -hdet
    have hpn : p ∣ n := hζ.dvd_of_pow_eq_one n hcn
    have hj : ∀ j : ℕ, j < p → HeisTensor.Cent H ((x₁ * y₁ ^ j : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
      intro j _
      have := hcent 1 j (fun hd => hp1 hd.1)
      simpa using this
    exact eq_top_of_heis_pair_all_gu h hT hp hp5 hpq (Nat.le_of_dvd hn0 hpn) hy₁ hx₁ hζ hν0 hνN
      (fun hnp => hexcl₁ hnp hc1) hy₁p hx₁p hc₁ hcentY hj

theorem planeW_words_caseII {x y : GL (Fin n) K} {c : K}
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hc0 : c ≠ 0) (hp : p.Prime) {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : p ∣ b) :
    ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∃ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) ∧ ∃ s : K, s ≠ 0 ∧
      ((y ^ i * (x ^ a * y ^ b) ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  refine ⟨a * j, i + b * j, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    have hj : p ∣ j := by
      rcases (Nat.Prime.dvd_mul hp).1 hA with h1 | h1
      · exact absurd h1 hpa
      · exact h1
    have hbj : p ∣ b * j := dvd_mul_of_dvd_left hpb j
    have hi : p ∣ i := (Nat.dvd_add_left hbj).1 hB
    exact hij ⟨hi, hj⟩
  · obtain ⟨s, hs, hEq⟩ := planeW_caseII hc hc0 a b i j
    refine ⟨s, hs, ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact hEq

theorem planeW_words_caseI {x y : GL (Fin n) K} {c : K}
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hc0 : c ≠ 0) (hp : p.Prime) {a b : ℕ} (hpb : ¬ p ∣ b) :
    ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∃ A B : ℕ, ¬ (p ∣ A ∧ p ∣ B) ∧ ∃ s : K, s ≠ 0 ∧
      ((x ^ i * (x ^ a * y ^ b) ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        s • ((x ^ A * y ^ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  refine ⟨i + a * j, b * j, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    have hj : p ∣ j := by
      rcases (Nat.Prime.dvd_mul hp).1 hB with h1 | h1
      · exact absurd h1 hpb
      · exact h1
    have haj : p ∣ a * j := dvd_mul_of_dvd_right hj a
    have hi : p ∣ i := (Nat.dvd_add_left haj).1 hA
    exact hij ⟨hi, hj⟩
  · obtain ⟨s, hs, hEq⟩ := planeW_caseI hc hc0 a b i j
    refine ⟨s, hs, ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact hEq

theorem eq_top_of_words [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hT : TorusFourierGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (hn : 3 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) {α β c : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hind : ∀ a b : ℕ, (∃ c' : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c' • 1) → p ∣ a ∧ p ∣ b)
    (hexcl : n = p → c ≠ 1 → (∃ μ : K, μ ^ p = α) ∧ ∃ ν : K, ν ^ p = β)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hH : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) →
      HeisTensor.Cent H ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    H = ⊤ := by
  classical
  haveI := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hp2 : p ≠ 2 := by omega
  have hcp : c ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα hx3 hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hx3M : (x : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hx3
  have hy3M : (y : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hy3
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hx hx3
  have hβN : h.bar β * β = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hy hy3
  have hαq : α ^ (ℓ ^ f + 1) = 1 := planeW_pow_card_succ h hαN
  have hβq : β ^ (ℓ ^ f + 1) = 1 := planeW_pow_card_succ h hβN
  have hpK : p ∣ Nat.card K - 1 := by
    have hl : 0 < ℓ := h.prime.pos
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hl
    have key : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hl _)
      zify [hq1, h2]
      ring
    rw [h.card_eq_sq, key]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα hβ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα) (pow_ne_zero _ hβ) hν.symm
  have hαβN : (α ^ a * β ^ b) ^ (ℓ ^ f + 1) = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul, hαq, hβq,
      one_pow, one_pow, one_mul]
  have hνN : h.bar ν * ν = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν0 hν hαβN
  have hYX : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) := hc
  have hy₁G : x ^ a * y ^ b ∈ primeFormUnitary h (idGram K n) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hx a) (Subgroup.pow_mem _ hy b)
  have hy₁p : ((((x ^ a * y ^ b : GL (Fin n) K)) ^ p : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (ν ^ p) • 1 := by
    rw [Units.val_pow_eq_pow_val, planeW_coe_word, pow_word_p hp hp2 hx3M hy3M hYX hcp a b, hν]
  by_cases hpb : p ∣ b
  ·
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, hpb⟩
    have hc₁ : ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (y : Matrix (Fin n) (Fin n) K) = (c ^ a)⁻¹ •
          ((y : Matrix (Fin n) (Fin n) K) * ((x ^ a * y ^ b : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) := by
      rw [planeW_coe_word]
      exact planeW_comm_caseII hYX hc0 a b
    have hexcl₁ : n = p → (c ^ a)⁻¹ ≠ 1 → ∃ μ : K, μ ^ p = β := by
      intro hnp hca
      exact (hexcl hnp (fun hc1 => hca (by rw [hc1, one_pow, inv_one]))).2
    exact eq_top_of_kernel_pair h hT hp hp5 hpq hn (x₁ := y) (y₁ := x ^ a * y ^ b) hy hy₁G
      (α₁ := β) (c₁ := (c ^ a)⁻¹) hβ hν0 hνN hy3 hy₁p hc₁ hexcl₁
      (planeW_words_caseII hYX hc0 hp hpa hpb) hind hH
  ·
    have hc₁ : ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) = c ^ b •
          ((x : Matrix (Fin n) (Fin n) K) * ((x ^ a * y ^ b : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) := by
      rw [planeW_coe_word]
      exact planeW_comm_caseI hYX a b
    have hexcl₁ : n = p → c ^ b ≠ 1 → ∃ μ : K, μ ^ p = α := by
      intro hnp hcb
      exact (hexcl hnp (fun hc1 => hcb (by rw [hc1, one_pow]))).1
    exact eq_top_of_kernel_pair h hT hp hp5 hpq hn (x₁ := x) (y₁ := x ^ a * y ^ b) hx hy₁G
      (α₁ := α) (c₁ := c ^ b) hα hν0 hνN hx3 hy₁p hc₁ hexcl₁
      (planeW_words_caseI hYX hc0 hp hpb) hind hH

theorem closure_planeFixUnW_gu [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hT : TorusFourierGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (hn : 3 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) {α β c : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hind : ∀ a b : ℕ,
      (∃ c' : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c' • 1) →
        p ∣ a ∧ p ∣ b)
    (hexcl : n = p → c ≠ 1 → (∃ μ : K, μ ^ p = α) ∧ ∃ ν : K, ν ^ p = β) :
    Subgroup.closure (planeFixUnW ℓ f n p K x y) = ⊤ := by
  classical
  let ε : SUid (unitaryInvolution K ℓ f) n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let H : Subgroup (SUid (unitaryInvolution K ℓ f) n) :=
    (Subgroup.closure (planeFixUnW ℓ f n p K x y)).comap ε.toMonoidHom
  have hH : H = ⊤ := by
    refine eq_top_of_words h hT hp hp5 hpq hn hx hy hα hβ hx3 hy3 hc hind hexcl ?_
    intro a b hab g hg
    exact Subgroup.subset_closure ⟨a, b, hab, mem_FixUn_of_mul_comm (g := ε g) hg⟩
  rw [eq_top_iff]
  intro u _
  have hu : ε.symm u ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using hu

end CFSG.LieType.SeitzGeneration
