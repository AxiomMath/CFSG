module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank Matrix

section Generic

theorem two_le_pRank_statedProj_of_commute_mod {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : ∃ c ∈ StatedScalars ι K, x * y = y * x * c) (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y) :
    2 ≤ pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  have hcomm : Commute (π ⟨x, hxH⟩) (π ⟨y, hyH⟩) := by
    obtain ⟨c, hc, hxyc⟩ := hxy
    have hcH : c ∈ H := by
      have : c = (y * x)⁻¹ * (x * y) := by rw [hxyc]; group
      rw [this]
      exact H.mul_mem (H.inv_mem (H.mul_mem hyH hxH)) (H.mul_mem hxH hyH)
    change π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩
    have h1 : π ⟨c, hcH⟩ = 1 := by
      change QuotientGroup.mk' N ⟨c, hcH⟩ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hc
    have h2 : (⟨x, hxH⟩ * ⟨y, hyH⟩ : H) = ⟨y, hyH⟩ * ⟨x, hxH⟩ * ⟨c, hcH⟩ :=
      Subtype.ext hxyc
    rw [← map_mul, ← map_mul, h2, map_mul, h1, mul_one]
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy)
    hcomm (fun h => hx1 ?_) (fun n h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

end Generic

section ThreeByThree

variable {K : Type} [Field K]

theorem statedScalars_eq_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] {c : GL ι K}
    (hc : c ∈ StatedScalars ι K) : ∃ u : K, (c : Matrix ι ι K) = Matrix.diagonal fun _ => u := by
  obtain ⟨u, rfl⟩ := hc
  exact ⟨u, by simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]⟩

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cubeDiag (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

theorem cycMat_pow_three : (cycMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem cubeDiag_pow_three {ω : K} (hω : ω ^ 3 = 1) : cubeDiag ω ^ 3 = 1 := by
  rw [cubeDiag, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  ext i
  have h6 : (ω ^ 2) ^ 3 = 1 := by
    calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω, one_pow]
  fin_cases i <;> simp [hω, h6]

theorem cycMat_mul_cubeDiag {ω : K} (hω : ω ^ 3 = 1) :
    (cubeDiag ω : Matrix (Fin 3) (Fin 3) K) * cycMat =
      cycMat * cubeDiag ω * Matrix.diagonal fun _ => ω := by
  ext i j
  have h3 : ω * ω * ω = 1 := by simpa [pow_succ] using hω
  simp only [cubeDiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [cycMat, pow_succ, h3]

@[expose] def glOfPowThree {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h : M ^ 3 = 1) : GL ι K :=
  ⟨M, M ^ 2, (pow_succ' M 2).symm.trans h, (pow_succ M 2).symm.trans h⟩

theorem coe_glOfPowThree {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h : M ^ 3 = 1) : (glOfPowThree M h : Matrix ι ι K) = M := rfl

theorem glOfPowThree_pow_three {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h : M ^ 3 = 1) : glOfPowThree M h ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_glOfPowThree, h, Units.val_one])

theorem det_cycMat : (cycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [cycMat, Matrix.det_fin_three]

theorem det_cubeDiag {ω : K} (hω : ω ^ 3 = 1) : (cubeDiag ω).det = 1 := by
  simp only [cubeDiag, Matrix.det_diagonal, Fin.prod_univ_three]
  calc _ = ω ^ 3 := by simp; ring
    _ = 1 := hω

theorem two_le_pRank_three_of_cycMat_cubeDiag [Finite K] {H : Subgroup (GL (Fin 3) K)} {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hD : glOfPowThree (cubeDiag ω) (cubeDiag_pow_three hω3) ∈ H)
    (hP : glOfPowThree cycMat cycMat_pow_three ∈ H) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  refine two_le_pRank_statedProj_of_commute_mod hD hP
    (glOfPowThree_pow_three _ _) (glOfPowThree_pow_three _ _) ?_ ?_ ?_
  · refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0),
      ⟨_, rfl⟩, Units.ext ?_⟩
    simp only [Units.val_mul, coe_glOfPowThree]
    rw [cycMat_mul_cubeDiag hω3]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  · intro hc
    obtain ⟨u, hu⟩ := statedScalars_eq_diagonal hc
    have h0 := congrFun (congrFun hu 0) 0
    have h1 := congrFun (congrFun hu 1) 1
    simp only [coe_glOfPowThree, cubeDiag, Matrix.diagonal_apply_eq] at h0 h1
    simp at h0 h1
    exact hω1 (h1.trans h0.symm)
  · intro n c hc he
    obtain ⟨u, hu⟩ := statedScalars_eq_diagonal hc
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      he) 1) 0
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_glOfPowThree, cubeDiag, hu,
      Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, cycMat] at this
    simp at this


theorem cycMat_transpose : (cycMat : Matrix (Fin 3) (Fin 3) K)ᵀ = cycMat ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem psl_three_two_le_pRank_three_of_cube_root [Finite K] {ω : K} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : 2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) :=
  two_le_pRank_three_of_cycMat_cubeDiag hω3 hω1
    (Subgroup.subset_closure (by simpa [coe_glOfPowThree] using det_cubeDiag hω3))
    (Subgroup.subset_closure (by simpa [coe_glOfPowThree] using det_cycMat))

theorem psu_three_two_le_pRank_three_of_cube_root [Finite K] {q : ℕ} (hq : q ≠ 0) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hωq : ω ^ (q + 1) = 1) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 q K))) := by
  refine two_le_pRank_three_of_cycMat_cubeDiag hω3 hω1 (Subgroup.subset_closure ?_)
    (Subgroup.subset_closure ?_)
  · refine ⟨by simpa [coe_glOfPowThree] using det_cubeDiag hω3, ?_⟩
    simp only [coe_glOfPowThree, cubeDiag]
    rw [Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    have h2 : (ω ^ 2) ^ q * ω ^ 2 = 1 := by
      calc (ω ^ 2) ^ q * ω ^ 2 = (ω ^ (q + 1)) ^ 2 := by ring
        _ = 1 := by rw [hωq, one_pow]
    have h1 : ω ^ q * ω = 1 := by rw [← pow_succ]; exact hωq
    fin_cases i <;> simp [h1, h2]
  · refine ⟨by simpa [coe_glOfPowThree] using det_cycMat, ?_⟩
    simp only [coe_glOfPowThree]
    have hmap : (cycMat : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = cycMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cycMat, zero_pow hq]
    rw [hmap, cycMat_transpose, ← pow_succ, cycMat_pow_three]

theorem exists_cube_root_of_three_dvd [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  refine ⟨ζ, ?_, ?_⟩
  · have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this |>.trans (by simp)
  · intro h1
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζ
    omega

theorem psl_three_two_le_pRank_three [Finite K] (h : Nat.card K % 3 = 1) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
  obtain ⟨ω, h3, h1⟩ := exists_cube_root_of_three_dvd (K := K) (by
    have : 0 < Nat.card K := Nat.card_pos
    omega)
  exact psl_three_two_le_pRank_three_of_cube_root h3 h1

theorem psu_three_two_le_pRank_three [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) : 2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 q K))) := by
  have hq0 : q ≠ 0 := by omega
  have h3q : 3 ∣ q + 1 := by omega
  obtain ⟨ω, h3, h1⟩ := exists_cube_root_of_three_dvd (K := K) (by
    rw [hK]
    obtain ⟨k, hk⟩ := h3q
    refine ⟨k * (q - 1), ?_⟩
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have : 1 ≤ q := by omega
      zify [this, (by nlinarith : 1 ≤ q ^ 2)]
      ring
    rw [this, hk]
    ring)
  have hωq : ω ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := h3q
    rw [hk, pow_mul, h3, one_pow]
  exact psu_three_two_le_pRank_three_of_cube_root hq0 h3 h1 hωq

end ThreeByThree

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
