module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpBC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Diag
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Orth
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Split

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)} {N : Matrix ι ι K} {z : ι → K}

omit [CharP K 2] in
theorem polMat_zero_left_right (a : ι → K) : polMat Q 0 a = 0 ∧ polMat Q a 0 = 0 :=
  ⟨Matrix.ext_iff_mulVec.mpr fun v => by rw [polMat_mulVec, map_zero, zero_smul, zero_mulVec],
    Matrix.ext_iff_mulVec.mpr fun v => by rw [polMat_mulVec, smul_zero, zero_mulVec]⟩

omit [CharP K 2] in
theorem polMat_adj (y u v : ι → K) :
    Q.polarBilin (polMat Q y y *ᵥ u) v = Q.polarBilin u (polMat Q y y *ᵥ v) := by
  rw [polMat_mulVec, polMat_mulVec, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul, polarBilin_comm Q y v, mul_comm]

variable (hQ : Q.polarBilin.Nondegenerate) (hN : N * N = 0)
  (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
  (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v))

include hQ hN hadj hz

theorem mul_splitBC :
    (N + polMat Q z z) * (N + polMat Q z z) = 0 ∧ (N + polMat Q z z) * polMat Q z z = 0 ∧
      polMat Q z z * (N + polMat Q z z) = 0 := by
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hz
  have h1 : N * polMat Q z z = 0 := by rw [mul_polMat, hNz, (polMat_zero_left_right z).2]
  have h2 : polMat Q z z * N = 0 := by
    rw [polMat_mul_of_adj Q hadj, hNz, (polMat_zero_left_right z).1]
  have h3 := polMat_self_mul_self (Q := Q) z
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hN, h1, h2, h3, add_zero, add_zero]
  · rw [Matrix.add_mul, h1, h3, add_zero]
  · rw [Matrix.mul_add, h2, h3, add_zero]

omit hQ hN in
theorem adj_alt_splitBC :
    (∀ u v, Q.polarBilin ((N + polMat Q z z) *ᵥ u) v =
      Q.polarBilin u ((N + polMat Q z z) *ᵥ v)) ∧
      ∀ v, Q.polarBilin v ((N + polMat Q z z) *ᵥ v) = 0 := by
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · rw [add_mulVec, add_mulVec, map_add, LinearMap.add_apply, map_add, hadj, polMat_adj]
  · rw [add_mulVec, map_add, ← hz, polMat_mulVec, map_smul, smul_eq_mul, pow_two,
      CharTwo.add_self_eq_zero]

omit [CharP K 2] hN hadj hz in
theorem indep_splitBC (hE₁ : ∀ v, Q.polarBilin v ((N + polMat Q z z) *ᵥ v) = 0)
    (hz0 : z ≠ 0) (hE₁0 : N + polMat Q z z ≠ 0) (a b : K)
    (h : a • (N + polMat Q z z) + b • polMat Q z z = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨v, hv⟩ := exists_polarBilin_eq_one hQ hz0
  have h1 := congrArg (fun X : Matrix ι ι K => Q.polarBilin v (X *ᵥ v)) h
  rw [add_mulVec, smul_mulVec, smul_mulVec, map_add, map_smul, map_smul, hE₁, polMat_mulVec,
    map_smul, hv, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one, mul_one,
    zero_mulVec, map_zero] at h1
  refine ⟨?_, h1⟩
  rw [h1, zero_smul, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_right hE₁0

omit [CharP K 2] hQ hN hadj in
theorem ker_le_ker_splitBC {k : ι → K} (hk : N *ᵥ k = 0) : (N + polMat Q z z) *ᵥ k = 0 := by
  have h1 := hz k
  rw [hk, map_zero, pow_eq_zero_iff two_ne_zero] at h1
  rw [add_mulVec, hk, polMat_mulVec, h1, zero_smul, add_zero]

omit hN hadj in
theorem conj_splitBC_of_conj [Finite K] {d : GL ι K}
    (hd : ∀ u v, Q.polarBilin ((d : Matrix ι ι K) *ᵥ u) ((d : Matrix ι ι K) *ᵥ v) =
      Q.polarBilin u v) {c : K}
    (hdN : (d : Matrix ι ι K) * N * ((d⁻¹ : GL ι K) : Matrix ι ι K) = c • N) :
    (d : Matrix ι ι K) * polMat Q z z * ((d⁻¹ : GL ι K) : Matrix ι ι K) = c • polMat Q z z ∧
      (d : Matrix ι ι K) * (N + polMat Q z z) * ((d⁻¹ : GL ι K) : Matrix ι ι K) =
        c • (N + polMat Q z z) := by
  have hdi : ∀ u v, Q.polarBilin ((d : Matrix ι ι K) *ᵥ u) v =
      Q.polarBilin u (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) := fun u v => by
    rw [← hd u, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  obtain ⟨γ, hγ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have hfrob : Function.Injective fun x : K => x ^ 2 := by
    intro a b hab
    simp only at hab
    have h : (a + b) ^ 2 = 0 := by rw [CharTwo.add_sq, hab, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  have hdz : (d : Matrix ι ι K) *ᵥ z = γ • z := by
    have hdd : ∀ v, (d : Matrix ι ι K) *ᵥ (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v := fun v => by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have h1 : ∀ v, Q.polarBilin v ((d : Matrix ι ι K) *ᵥ z) = Q.polarBilin v (γ • z) := fun v => by
      apply hfrob
      simp only
      have h2 := congrArg (fun X : Matrix ι ι K => Q.polarBilin v (X *ᵥ v)) hdN
      simp only [← mulVec_mulVec, smul_mulVec, map_smul, smul_eq_mul] at h2
      calc Q.polarBilin v ((d : Matrix ι ι K) *ᵥ z) ^ 2
          = Q.polarBilin (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) z ^ 2 := by
            rw [← hd (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) z, hdd]
        _ = Q.polarBilin (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
              (N *ᵥ (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)) := hz _
        _ = Q.polarBilin v
              ((d : Matrix ι ι K) *ᵥ (N *ᵥ (((d⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v))) := by
            rw [← hd, hdd]
        _ = (γ * Q.polarBilin v z) ^ 2 := by rw [h2, ← hz, hγ]; ring
        _ = Q.polarBilin v (γ • z) ^ 2 := by rw [map_smul, smul_eq_mul]
    rw [← sub_eq_zero]
    refine hQ.2 _ fun v => ?_
    rw [map_sub, h1, sub_self]
  have hP : (d : Matrix ι ι K) * polMat Q z z * ((d⁻¹ : GL ι K) : Matrix ι ι K) =
      c • polMat Q z z := by
    have h1 := conj_polMat_self_of_polar hd z
    rw [h1, hdz, polMat_smul_left, polMat_smul_right, smul_smul, ← hγ]
  refine ⟨hP, ?_⟩
  rw [Matrix.mul_add, Matrix.add_mul, hdN, hP, smul_add]

end Split

section Hyperbolic

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem polarBilin_hypMat_mulVec {z f : ι → K} (hzf : Q.polarBilin z f = 1) {α : K}
    (hα : α ≠ 0) (u v : ι → K) :
    Q.polarBilin (hypMat Q z f α *ᵥ u) (hypMat Q z f α *ᵥ v) = Q.polarBilin u v := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hzz : Q.polarBilin z z = 0 := TypeCData.pol_self z
  have hff : Q.polarBilin f f = 0 := TypeCData.pol_self f
  have hfz : Q.polarBilin f z = 1 := by rw [hBs]; exact hzf
  rw [hypMat_mulVec, hypMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hzz, hff,
    hzf, hfz, hBs z v, hBs f v]
  field_simp
  ring

end Hyperbolic

section Sp

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rank_splitBC {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hN : N * N = 0)
    (hadj : ∀ u v, (quadPlus n K).polarBilin (N *ᵥ u) v = (quadPlus n K).polarBilin u (N *ᵥ v))
    {z : Fin n ⊕ Fin n → K}
    (hz : ∀ v, (quadPlus n K).polarBilin v z ^ 2 = (quadPlus n K).polarBilin v (N *ᵥ v)) :
    Even (N + polMat (quadPlus n K) z z).rank ∧ (N + polMat (quadPlus n K) z z).rank ≤ N.rank ∧
      N.rank ≤ (N + polMat (quadPlus n K) z z).rank + 1 := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨h11, -, -⟩ := mul_splitBC hQ hN hadj hz
  obtain ⟨hadj₁, halt₁⟩ := adj_alt_splitBC hadj hz
  refine ⟨?_, ?_, ?_⟩
  ·
    by_cases hE0 : N + polMat (quadPlus n K) z z = 0
    · rw [hE0, Matrix.rank_zero]
      exact Even.zero
    have hmem := unipGL_mem_statedSp_of_adj rfl h11 hadj₁ 1
    have h := even_commRank_of_sympForm_eq_zero hmem (orderOf_unipGL h11 one_ne_zero hE0)
      fun v => by
        rw [coe_unipGL, one_smul, ← sympForm_sub_one_mulVec, add_sub_cancel_left,
          ← polarBilin_quadPlus]
        exact halt₁ v
    rwa [commRank_unipGL h11 one_ne_zero] at h
  ·
    have hle : LinearMap.ker N.mulVecLin ≤
        LinearMap.ker (N + polMat (quadPlus n K) z z).mulVecLin := fun k hk => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      exact ker_le_ker_splitBC hz hk
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    have h3 := LinearMap.finrank_range_add_finrank_ker (N + polMat (quadPlus n K) z z).mulVecLin
    rw [Matrix.rank, Matrix.rank]
    omega
  ·
    have h1 : N = (N + polMat (quadPlus n K) z z) + polMat (quadPlus n K) z z := by
      rw [add_assoc, matrix_add_self, add_zero]
    have h2 : LinearMap.range N.mulVecLin ≤
        LinearMap.range (N + polMat (quadPlus n K) z z).mulVecLin ⊔
          LinearMap.range (polMat (quadPlus n K) z z).mulVecLin := by
      conv_lhs => rw [h1]
      rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le _ _
    have h3 := Submodule.finrank_mono h2
    have h4 := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range (N + polMat (quadPlus n K) z z).mulVecLin)
      (LinearMap.range (polMat (quadPlus n K) z z).mulVecLin)
    have h5 : (polMat (quadPlus n K) z z).rank ≤ 1 := by
      by_cases hz0 : z = 0
      · rw [hz0, (polMat_zero_left_right (Q := quadPlus n K) 0).1, Matrix.rank_zero]
        omega
      · rw [rank_polMat_self (nondegenerate_polarBilin_quadPlus n K) hz0]
    rw [Matrix.rank] at h5 ⊢
    rw [Matrix.rank]
    omega

theorem sep_splitBC_sp {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hadj : ∀ u v, (quadPlus n K).polarBilin (N *ᵥ u) v = (quadPlus n K).polarBilin u (N *ᵥ v))
    {z : Fin n ⊕ Fin n → K}
    (hz : ∀ v, (quadPlus n K).polarBilin v z ^ 2 = (quadPlus n K).polarBilin v (N *ᵥ v))
    (hz0 : z ≠ 0)
    (hE₁0 : N + polMat (quadPlus n K) z z ≠ 0) {X : GL (Fin n ⊕ Fin n) K}
    (hX : X ∈ StatedSp n K) :
    (∀ s t : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (N + polMat (quadPlus n K) z z) *
        ((X⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        s • (N + polMat (quadPlus n K) z z) + t • polMat (quadPlus n K) z z → t = 0) ∧
      (∀ s t : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z *
        ((X⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        s • (N + polMat (quadPlus n K) z z) + t • polMat (quadPlus n K) z z → s = 0) := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hXB := polarBilin_mulVec_of_mem_statedSp hX
  obtain ⟨-, halt₁⟩ := adj_alt_splitBC hadj hz
  have hXi : ∀ u v, (quadPlus n K).polarBilin ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
      v = (quadPlus n K).polarBilin u
        (((X⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) :=
    fun u v => by
      rw [← hXB u, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hval : ∀ (s t : K) (v : Fin n ⊕ Fin n → K), (quadPlus n K).polarBilin v
      ((s • (N + polMat (quadPlus n K) z z) + t • polMat (quadPlus n K) z z) *ᵥ v) =
        t * (quadPlus n K).polarBilin v z ^ 2 := fun s t v => by
    rw [add_mulVec, smul_mulVec, smul_mulVec, map_add, map_smul, map_smul, halt₁, polMat_mulVec,
      map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, pow_two]
  obtain ⟨u₀, hu₀⟩ := exists_polarBilin_eq_one hQ hz0
  refine ⟨fun s t h => ?_, fun s t h => ?_⟩
  · have h1 := congrArg (fun Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K =>
      (quadPlus n K).polarBilin u₀ (Y *ᵥ u₀)) h
    rw [hval, hu₀, one_pow, mul_one, ← mulVec_mulVec, ← mulVec_mulVec, polarBilin_comm,
      hXi, polarBilin_comm] at h1
    rw [← h1]
    exact halt₁ _
  ·
    have h1 := conj_polMat_self_of_polar hXB z
    rw [h1] at h
    have hfrob : Function.Injective fun x : K => x ^ 2 := by
      intro a b hab
      simp only at hab
      have h2 : (a + b) ^ 2 = 0 := by rw [CharTwo.add_sq, hab, CharTwo.add_self_eq_zero]
      have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rw [← CharTwo.sub_eq_add] at h'
      exact sub_eq_zero.mp h'
    obtain ⟨γ, hγ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) t
    have hXz : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = γ • z := by
      have h2 : ∀ v, (quadPlus n K).polarBilin v
          ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z) =
            (quadPlus n K).polarBilin v (γ • z) := fun v => by
        apply hfrob
        simp only
        have h3 := congrArg (fun Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K =>
          (quadPlus n K).polarBilin v (Y *ᵥ v)) h
        simp only [polMat_mulVec, map_smul, smul_eq_mul] at h3
        rw [hval] at h3
        rw [map_smul, smul_eq_mul, mul_pow, pow_two ((quadPlus n K).polarBilin v _), h3, hγ]
        ring
      rw [← sub_eq_zero]
      refine hQ.2 _ fun v => ?_
      rw [map_sub, h2, sub_self]
    rw [hXz, polMat_smul_left, polMat_smul_right, smul_smul, ← hγ] at h
    have h2 : s • (N + polMat (quadPlus n K) z z) = 0 := by
      have h3 := congrArg (· - t • polMat (quadPlus n K) z z) h
      simp only [sub_self, add_sub_cancel_right] at h3
      exact h3.symm
    exact (smul_eq_zero.mp h2).resolve_right hE₁0

theorem exists_torus_glob_splitBC_sp {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) {z : Fin n ⊕ Fin n → K}
    (hz : ∀ v, (quadPlus n K).polarBilin v z ^ 2 =
      (quadPlus n K).polarBilin v (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v))
    {c : K} (hc : c ≠ 0) :
    ∃ d ∈ StatedSp n K,
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) + polMat (quadPlus n K) z z) *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        c • (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) + polMat (quadPlus n K) z z) ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        c • polMat (quadPlus n K) z z := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨hN, hadj, -, -⟩ := sp_involution_facts hM hM2
  obtain ⟨Q₀, hpol₀, hQ₀N⟩ := exists_quadraticForm_sub_one hM hM2
  have hQ₀ : Q₀.polarBilin.Nondegenerate := by rw [hpol₀]; exact hQ
  obtain ⟨d, hdQ, hd⟩ := exists_isometry_conj_eq_smul Q₀ hQ₀ hN (by rw [hpol₀]; exact hadj)
    hQ₀N hc
  have hdB : ∀ u v, (quadPlus n K).polarBilin
      ((d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
      ((d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = (quadPlus n K).polarBilin u v :=
    fun u v => by
      rw [← hpol₀]
      exact polarBilin_mulVec_of_isometry Q₀ hdQ u v
  obtain ⟨h1, h2⟩ := conj_splitBC_of_conj hQ hz hdB hd
  exact ⟨d, mem_statedSp_of_isometry hpol₀ hdQ, h2, h1⟩

omit [Finite K] in
theorem exists_torus_hyp_splitBC_sp {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hEE : E * E = 0)
    (hadjE : ∀ u v, (quadPlus n K).polarBilin (E *ᵥ u) v = (quadPlus n K).polarBilin u (E *ᵥ v))
    (haltE : ∀ v, (quadPlus n K).polarBilin v (E *ᵥ v) = 0) {z y₁ : Fin n ⊕ Fin n → K}
    (hz0 : z ≠ 0) (hEz : E *ᵥ z = 0) (hy₁ : E *ᵥ y₁ = z) {ν : K} (hν : ν ≠ 0) :
    ∃ d ∈ StatedSp n K,
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = E ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = ν • z := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
    polarBilin_comm (quadPlus n K)
  have hE2 : ∀ a, E *ᵥ (E *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hEE, zero_mulVec]
  obtain ⟨y₀', hy₀'⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = y₀' + (quadPlus n K).polarBilin y₁ y₀' • (E *ᵥ y₀') := ⟨_, rfl⟩
  have hzy₀ : (quadPlus n K).polarBilin z y₀ = 1 := by
    rw [hy₀, map_add, map_smul, smul_eq_mul, ← hadjE, hEz, map_zero, LinearMap.zero_apply,
      mul_zero, add_zero, hBs]
    exact hy₀'
  have hy₁E : (quadPlus n K).polarBilin y₁ (E *ᵥ y₀') = 1 := by
    rw [← hadjE, hy₁, hBs]
    exact hy₀'
  have hy₁y₀ : (quadPlus n K).polarBilin y₁ y₀ = 0 := by
    rw [hy₀, map_add, map_smul, smul_eq_mul, hy₁E, mul_one, CharTwo.add_self_eq_zero]
  obtain ⟨w, hw⟩ : ∃ w, w = E *ᵥ y₀ := ⟨_, rfl⟩
  have hy₁w : (quadPlus n K).polarBilin y₁ w = 1 := by rw [hw, ← hadjE, hy₁, hzy₀]
  have hzz : (quadPlus n K).polarBilin z z = 0 := TypeCData.pol_self z
  have hzw : (quadPlus n K).polarBilin z w = 0 := by
    rw [hw, ← hadjE, hEz, map_zero, LinearMap.zero_apply]
  have hzy₁ : (quadPlus n K).polarBilin z y₁ = 0 := by rw [← hy₁, hBs, haltE]
  have hy₀w : (quadPlus n K).polarBilin y₀ w = 0 := by rw [hw]; exact haltE y₀
  have hEw : E *ᵥ w = 0 := by rw [hw]; exact hE2 y₀
  have hwy₀ : (quadPlus n K).polarBilin w y₀ = 0 := by rw [hBs]; exact hy₀w
  have hy₁z : (quadPlus n K).polarBilin y₁ z = 0 := by rw [hBs]; exact hzy₁
  have hwz : (quadPlus n K).polarBilin w z = 0 := by rw [hBs]; exact hzw
  have hT₁B := polarBilin_hypMat_mulVec (Q := quadPlus n K) hzy₀ hν
  have hT₂B := polarBilin_hypMat_mulVec (Q := quadPlus n K) hy₁w hν
  set D := hypGL (Q := quadPlus n K) hzy₀ hν * hypGL (Q := quadPlus n K) hy₁w hν with hD
  have hdB : ∀ u v, (quadPlus n K).polarBilin
      ((D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
      ((D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = (quadPlus n K).polarBilin u v :=
    fun u v => by
      rw [hD, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_hypGL, coe_hypGL, hT₁B, hT₂B]
  have hDv : ∀ v, (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v =
      v + ((ν - 1) * (quadPlus n K).polarBilin v w) • y₁ +
        ((ν⁻¹ - 1) * (quadPlus n K).polarBilin v y₁) • w +
        ((ν - 1) * (quadPlus n K).polarBilin v y₀) • z +
        ((ν⁻¹ - 1) * (quadPlus n K).polarBilin v z) • y₀ := fun v => by
    rw [hD, Units.val_mul, ← mulVec_mulVec, coe_hypGL, coe_hypGL, hypMat_mulVec, hypMat_mulVec]
    simp only [map_add, map_smul, smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply,
      hy₁y₀, hwy₀, hy₁z, hwz, mul_zero, add_zero]
  have hcomm : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E =
      E * (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hDv, hDv]
    simp only [mulVec_add, mulVec_smul, hadjE, hy₁, ← hw, hEw, hEz, map_zero, mul_zero,
      zero_smul, smul_zero, add_zero]
    abel
  have hDz : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = ν • z := by
    rw [hDv, hzw, hzz, hzy₁, hzy₀]
    simp only [mul_zero, zero_smul, add_zero, mul_one]
    module
  refine ⟨D, mem_statedSp_of_polarBilin hdB, ?_, hDz⟩
  rw [hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem exists_torus_fix_splitBC_sp {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hEE : E * E = 0)
    (hadjE : ∀ u v, (quadPlus n K).polarBilin (E *ᵥ u) v = (quadPlus n K).polarBilin u (E *ᵥ v))
    {z : Fin n ⊕ Fin n → K} (hz0 : z ≠ 0) (hEz : E *ᵥ z = 0) (hzE : ¬∃ y, E *ᵥ y = z) {κ : K}
    (hκ : κ ≠ 0) :
    ∃ d ∈ StatedSp n K,
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = κ • E ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = z := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  by_cases hE0 : E = 0
  · exact ⟨1, one_mem _, by rw [hE0, smul_zero, Matrix.mul_zero, Matrix.zero_mul],
      by rw [Units.val_one, one_mulVec]⟩
  obtain ⟨Q₁, hpol₁, hQ₁⟩ : ∃ Q₁ : QuadraticForm K (Fin n ⊕ Fin n → K),
      Q₁.polarBilin = (quadPlus n K).polarBilin ∧ ∀ v, Q₁ (E *ᵥ v) = 0 := by
    have hmem := unipGL_mem_statedSp_of_adj rfl hEE hadjE 1
    obtain ⟨Q₁, hpol₁, hQ₁⟩ := exists_quadraticForm_sub_one hmem
      (orderOf_unipGL hEE one_ne_zero hE0)
    refine ⟨Q₁, hpol₁, fun v => ?_⟩
    have h1 := hQ₁ v
    rwa [coe_unipGL, one_smul, add_sub_cancel_left] at h1
  have hQ₁' : Q₁.polarBilin.Nondegenerate := by rw [hpol₁]; exact hQ
  have hli : LinearIndependent K ![z] := linearIndependent_unique_iff.mpr (by simpa using hz0)
  have hdisj : Disjoint (LinearMap.range E.mulVecLin) (Submodule.span K (Set.range ![z])) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨y, rfl⟩ := hx1
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Submodule.mem_span_singleton] at hx2
    obtain ⟨c, hc⟩ := hx2
    by_contra hne
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hne hc.symm
    apply hzE
    refine ⟨c⁻¹ • y, ?_⟩
    rw [mulVec_smul, ← Matrix.mulVecLin_apply, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨D, hDQ, hDz, hD⟩ := exists_torus Q₁ hQ₁' hEE (by rw [hpol₁]; exact hadjE) hQ₁ ![z]
    (fun j => by fin_cases j; exact hEz) hli hdisj hκ
  have hDz' : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = z := by simpa using hDz 0
  have hDB : ∀ u v, (quadPlus n K).polarBilin
      (((D⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
      (((D⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
        (quadPlus n K).polarBilin u v := fun u v => by
    rw [← hpol₁, ← polarBilin_mulVec_of_isometry Q₁ hDQ, mulVec_mulVec, mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, one_mulVec]
  refine ⟨D⁻¹, mem_statedSp_of_polarBilin hDB, by rw [inv_inv]; exact hD, ?_⟩
  conv_lhs => rw [← hDz']
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

omit [Finite K] [CharP K 2] in
theorem conj_mul_eq_smul {ι : Type} [Fintype ι] [DecidableEq ι] {d₁ d₂ : GL ι K}
    {E : Matrix ι ι K} {c₁ c₂ : K}
    (h₁ : (d₁ : Matrix ι ι K) * E * ((d₁⁻¹ : GL ι K) : Matrix ι ι K) = c₁ • E)
    (h₂ : (d₂ : Matrix ι ι K) * E * ((d₂⁻¹ : GL ι K) : Matrix ι ι K) = c₂ • E) :
    ((d₁ * d₂ : GL ι K) : Matrix ι ι K) * E * (((d₁ * d₂)⁻¹ : GL ι K) : Matrix ι ι K) =
      (c₁ * c₂) • E := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul,
    show (d₁ : Matrix ι ι K) * d₂ * E * (((d₂⁻¹ : GL ι K) : Matrix ι ι K) *
      ((d₁⁻¹ : GL ι K) : Matrix ι ι K)) = (d₁ : Matrix ι ι K) * ((d₂ : Matrix ι ι K) * E *
        ((d₂⁻¹ : GL ι K) : Matrix ι ι K)) * ((d₁⁻¹ : GL ι K) : Matrix ι ι K) by
      simp only [Matrix.mul_assoc], h₂, Matrix.mul_smul, Matrix.smul_mul, h₁, smul_smul,
    mul_comm]

theorem exists_torus_splitBC_sp {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) {z : Fin n ⊕ Fin n → K}
    (hz : ∀ v, (quadPlus n K).polarBilin v z ^ 2 =
      (quadPlus n K).polarBilin v (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v))
    (hz0 : z ≠ 0) {l m : K} (hl : l ≠ 0) (hm : m ≠ 0) :
    ∃ d ∈ StatedSp n K,
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) + polMat (quadPlus n K) z z) *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        l • (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) + polMat (quadPlus n K) z z) ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        m • polMat (quadPlus n K) z z := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨hN, hadj, -, -⟩ := sp_involution_facts hM hM2
  obtain ⟨h11, -, -⟩ := mul_splitBC hQ hN hadj hz
  obtain ⟨hadj₁, halt₁⟩ := adj_alt_splitBC hadj hz
  have hNz := mulVec_sqrt_vector_of_adj hQ hN hadj hz
  have hE₁z := ker_le_ker_splitBC hz hNz
  have hP : ∀ d ∈ StatedSp n K, ∀ c : K, (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z =
      c • z → (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z *
        ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
          (c * c) • polMat (quadPlus n K) z z := fun d hd c hdz => by
    rw [conj_polMat_self_of_polar (polarBilin_mulVec_of_mem_statedSp hd), hdz, polMat_smul_left,
      polMat_smul_right, smul_smul]
  by_cases hzE : ∃ y₁, (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) +
      polMat (quadPlus n K) z z) *ᵥ y₁ = z
  · obtain ⟨y₁, hy₁⟩ := hzE
    obtain ⟨ν, hν⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (m * l⁻¹)
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hν
      exact mul_ne_zero hm (inv_ne_zero hl) hν
    obtain ⟨d₁, hd₁, h₁a, h₁b⟩ := exists_torus_glob_splitBC_sp hM hM2 hz hl
    obtain ⟨d₂, hd₂, h₂a, h₂z⟩ := exists_torus_hyp_splitBC_sp h11 hadj₁ halt₁ hz0 hE₁z hy₁ hν0
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_, ?_⟩
    · have h := conj_mul_eq_smul (c₂ := 1) h₁a (by rw [one_smul]; exact h₂a)
      rwa [mul_one] at h
    · have h := conj_mul_eq_smul h₁b (hP d₂ hd₂ ν h₂z)
      rwa [← hν, mul_comm m, ← mul_assoc, mul_inv_cancel₀ hl, one_mul] at h
  · obtain ⟨d₁, hd₁, h₁a, h₁b⟩ := exists_torus_glob_splitBC_sp hM hM2 hz hm
    obtain ⟨d₂, hd₂, h₂a, h₂z⟩ := exists_torus_fix_splitBC_sp h11 hadj₁ hz0 hE₁z hzE
      (mul_ne_zero hl (inv_ne_zero hm))
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_, ?_⟩
    · have h := conj_mul_eq_smul h₁a h₂a
      rwa [show m * (l * m⁻¹) = l by field_simp] at h
    · have h := conj_mul_eq_smul h₁b (hP d₂ hd₂ 1 (by rw [one_smul]; exact h₂z))
      rwa [mul_one, mul_one] at h

omit [Finite K] in
theorem exists_lift_splitBC_sp {G : Type} [Group G] {A : Subgroup G}
    {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)} (hZ : Odd (Nat.card (center ↥A)))
    {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hEE : E * E = 0) (hE0 : E ≠ 0)
    (hadjE : ∀ u v, (quadPlus n K).polarBilin (E *ᵥ u) v = (quadPlus n K).polarBilin u (E *ᵥ v)) :
    ∃ a : G, orderOf a = 2 ∧ Represents e a (unipGL E hEE 1) ∧
      ∃ φ : Multiplicative K →* G, Function.Injective φ ∧ φ.range = alphaGroup e a ∧
        ∀ t : K, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
          Represents e (φ (Multiplicative.ofAdd t)) (unipGL E hEE t) := by
  have hH : ∀ t : K, unipGL E hEE t ∈ StatedSp n K := unipGL_mem_statedSp_of_adj rfl hEE hadjE
  obtain ⟨a, ha2, ha⟩ := exists_represents_sq_eq_one hZ (hH 1) (unipGL_sq hEE 1)
  have hM2 := orderOf_unipGL hEE one_ne_zero hE0
  have hMa : ((unipGL E hEE 1 : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) -
      1 = E := by rw [coe_unipGL, one_smul, add_sub_cancel_left]
  have hE' : (((unipGL E hEE 1 : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) -
      1) * (((unipGL E hEE 1 : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) -
      1) = 0 := by rw [hMa]; exact hEE
  have hcongr : ∀ t : K, unipGL (((unipGL E hEE 1 : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE' t = unipGL E hEE t := fun t =>
    Units.ext (by rw [coe_unipGL, hMa, coe_unipGL])
  obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom hZ ha hM2 hE' fun t => by
    rw [hcongr]; exact hH t
  have hφ' : ∀ t : K, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
      Represents e (φ (Multiplicative.ofAdd t)) (unipGL E hEE t) := fun t =>
    ⟨(hφ t).1, by rw [← hcongr]; exact (hφ t).2⟩
  have haφ : a = φ (Multiplicative.ofAdd 1) :=
    eq_of_represents hZ ha (hφ' 1).2 (k := 1) (by rw [pow_one]; exact ha2) (k' := 1)
      (by rw [pow_one]; exact (hφ' 1).1)
  have ha1 : a ≠ 1 := fun h => by
    rw [h] at haφ
    have h1 := hinj (haφ.symm.trans (map_one φ).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd h1)
  exact ⟨a, orderOf_eq_prime ha2 ha1, ha, φ, hinj, hrange, hφ'⟩

theorem symplecticJ23_of_family (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (D : ClassicalModel A) (hD : D.family = .symplectic) (hZ : Odd (Nat.card (center A)))
    (p : G) (ℓ : ℕ) (hp : (1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨ D.SuzukiType p .c ℓ) :
    ∃ a b : G, ((1 < ℓ ∧ D.SuzukiType p .b ℓ ∧ D.SuzukiType a .a (ℓ - 1)) ∨
        (D.SuzukiType p .c ℓ ∧ D.SuzukiType a .a ℓ)) ∧ D.SuzukiType b .b 1 ∧
      DeltaNormal A p (D.alpha a ⊔ D.alpha b) ∧ DeltaCentral A p (D.alpha a ⊔ D.alpha b) ∧
      D.alpha b ≤ centralizer (D.alpha a : Set G) ∧ p ∉ D.alpha a ∧ p ∉ D.alpha b ∧
      RegularOn A (D.alpha a ⊔ D.alpha b)
        {j | j ∈ D.alpha a ⊔ D.alpha b ∧ j ∉ D.alpha a ∧ j ∉ D.alpha b} ∧
      AutDiagonal A (D.alpha a ⊔ D.alpha b) (D.alpha a) (D.alpha b) (D.q - 1) := by
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    have hQ := nondegenerate_polarBilin_quadPlus n K
    have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
      polarBilin_comm (quadPlus n K)
    have hp' : (1 < ℓ ∧ HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .b ℓ) ∨
        HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
          sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .c ℓ := hp
    obtain ⟨hp2, M, hpM, hM2, hrk, hnz, hcase⟩ : orderOf p = 2 ∧ ∃ M : GL (Fin n ⊕ Fin n) K,
        Represents e p M ∧ orderOf M = 2 ∧ commRank M = ℓ ∧
          (∃ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) ≠ 0) ∧
          ((1 < ℓ ∧ Odd ℓ) ∨ Even ℓ) := by
      rcases hp' with ⟨h1, hp2, M, hpM, hM2, hrk, hodd⟩ | ⟨hp2, M, hpM, hM2, hrk, hev, v, hv⟩
      · refine ⟨hp2, M, hpM, hM2, hrk, ?_, Or.inl ⟨h1, hodd⟩⟩
        by_contra! h0
        have h2 := even_commRank_of_sympForm_eq_zero hpM.2.1 hM2 h0
        rw [hrk] at h2
        exact Nat.not_even_iff_odd.mpr hodd h2
      · exact ⟨hp2, M, hpM, hM2, hrk, ⟨v, hv⟩, Or.inr hev⟩
    have hMsp : M ∈ StatedSp n K := hpM.2.1
    have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
    obtain ⟨hN, hadj, -, hcomm⟩ := sp_involution_facts hMsp hM2
    obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 :=
      ⟨_, rfl⟩
    rw [← hNdef] at hN hadj hcomm
    have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
      rw [hNdef, add_sub_cancel]
    obtain ⟨z, hz⟩ := exists_sqrt_vector_of_adj hQ hBs hadj
    have hzM : ∀ v, (quadPlus n K).polarBilin v z ^ 2 = (quadPlus n K).polarBilin v
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) := fun v => by
      rw [← hNdef]; exact hz v
    have hz0 : z ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv⟩ := hnz
      apply hv
      rw [← sympForm_sub_one_mulVec, ← polarBilin_quadPlus, ← hzM v, map_zero,
        zero_pow two_ne_zero]
    obtain ⟨h11, h12, h21⟩ := mul_splitBC hQ hN hadj hz
    have h22 := polMat_self_mul_self (Q := quadPlus n K) z
    obtain ⟨hadj₁, halt₁⟩ := adj_alt_splitBC hadj hz
    obtain ⟨⟨k, hk⟩, hle₁, hge₁⟩ := rank_splitBC hN hadj hz
    have hrkN : N.rank = ℓ := by rw [hNdef]; exact hrk
    rw [hrkN] at hle₁ hge₁
    have hℓ : 2 ≤ ℓ := by
      rcases hcase with ⟨h1, -⟩ | ⟨j, hj⟩
      · omega
      · have h0 : ℓ ≠ 0 := fun h0 => by
          rw [h0] at hrkN
          obtain ⟨v, hv⟩ := hnz
          apply hv
          rw [← sympForm_sub_one_mulVec, ← polarBilin_quadPlus, ← hNdef,
            eq_zero_of_rank_eq_zero hrkN, zero_mulVec, map_zero]
        omega
    set E₁ := N + polMat (quadPlus n K) z z with hE₁
    set P := polMat (quadPlus n K) z z with hP
    have hrkP : P.rank = 1 := rank_polMat_self hQ hz0
    have hE₁0 : E₁ ≠ 0 := fun h0 => by
      rw [h0, Matrix.rank_zero] at hge₁
      omega
    have hP0 : P ≠ 0 := fun h0 => by
      rw [h0, Matrix.rank_zero] at hrkP
      exact zero_ne_one hrkP
    have hind := indep_splitBC hQ halt₁ hz0 hE₁0
    have hME : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + E₁ + P := by
      rw [hMN, hE₁, add_assoc, add_assoc, matrix_add_self, add_zero]
    obtain ⟨a, ha2, haM, φ₁, hinj₁, hrange₁, hφ₁⟩ := exists_lift_splitBC_sp hZ h11 hE₁0 hadj₁
    obtain ⟨b, hb2, hbM, φ₂, hinj₂, hrange₂, hφ₂⟩ :=
      exists_lift_splitBC_sp hZ h22 hP0 (polMat_adj z)
    have hta : ∀ r, E₁.rank = r → HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) a .a r :=
      fun r hr => ⟨ha2, unipGL E₁ h11 1, haM, orderOf_unipGL h11 one_ne_zero hE₁0,
        by rw [commRank_unipGL h11 one_ne_zero, hr], ⟨hr ▸ ⟨k, hk⟩, fun v => by
          beta_reduce
          rw [coe_unipGL, one_smul, ← sympForm_sub_one_mulVec, add_sub_cancel_left,
            ← polarBilin_quadPlus]
          exact halt₁ v⟩⟩
    have htb : HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) b .b 1 :=
      ⟨hb2, unipGL P h22 1, hbM, orderOf_unipGL h22 one_ne_zero hP0,
        by rw [commRank_unipGL h22 one_ne_zero, hrkP], odd_one⟩
    have hcent : ∀ X ∈ StatedSp n K, X * M = M * X →
        (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E₁ = E₁ * X ∧
          (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * P = P * X := by
      intro X hX hXM
      have hXN := hcomm X hXM
      have hXB := polarBilin_mulVec_of_mem_statedSp hX
      have hXz := mulVec_sqrt_vector_of_commute_adj hQ hz hXB hXN
      have hXP : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * P = P * X := by
        have h1 := conj_polMat_self_of_polar hXB z
        rw [hXz, ← hP] at h1
        calc (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * P =
            X * P * ((X⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
              X := by
              rw [Matrix.mul_assoc _ (((X⁻¹ : GL (Fin n ⊕ Fin n) K) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)), Units.inv_mul, Matrix.mul_one]
          _ = P * X := by rw [h1]
      exact ⟨by rw [hE₁, Matrix.mul_add, Matrix.add_mul, hXN, hXP], hXP⟩
    have hp12 : p = φ₁ (Multiplicative.ofAdd 1) * φ₂ (Multiplicative.ofAdd 1) := by
      have h := represents_diag hZ h12 h21 hφ₁ hφ₂ 1 1
      have hM' : unipGL E₁ h11 1 * unipGL P h22 1 = M := Units.ext (by
        rw [coe_unipGL_mul_unipGL h12, one_smul, one_smul, hME])
      rw [hM'] at h
      exact eq_of_represents hZ hpM h.2 (k := 1) (by rw [pow_one]; exact hp2') (k' := 1)
        (by rw [pow_one]; exact h.1)
    have hreg := regularOn_autDiagonal_of hZ h12 h21 hφ₁ hφ₂ hE₁0 hP0 hind hinj₁ hinj₂
      (fun X hX => sep_splitBC_sp hadj hz hz0 hE₁0 hX) (fun l m hl hm => by
        obtain ⟨d, hd, h1, h2⟩ := exists_torus_splitBC_sp hMsp hM2 hzM hz0 hl hm
        rw [← hNdef] at h1
        exact ⟨d, hd, h1, h2⟩)
    refine ⟨a, b, ?_, htb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hp' with ⟨h1, hpb⟩ | hpc
      · rcases hcase with ⟨-, j, hj⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨h1, hpb, hta _ (by omega)⟩
        · obtain ⟨-, -, -, -, -, i, hi⟩ := hpb
          exfalso
          rw [← hrk] at hj
          omega
      · rcases hcase with ⟨-, j, hj⟩ | ⟨j, hj⟩
        · obtain ⟨-, -, -, -, -, ⟨i, hi⟩, -⟩ := hpc
          exfalso
          omega
        · exact Or.inr ⟨hpc, hta _ (by omega)⟩
    · show DeltaNormal A p (alphaGroup e a ⊔ alphaGroup e b)
      rw [← hrange₁, ← hrange₂]
      exact deltaNormal_diag_of hZ h12 h21 hφ₁ hφ₂ hpM hM2' hME hcent
    · show DeltaCentral A p (alphaGroup e a ⊔ alphaGroup e b)
      rw [← hrange₁, ← hrange₂]
      refine deltaCentral_diag_of hZ h12 h21 hφ₁ hφ₂ hp2' hpM hM2 fun X hXH hXM hXg => ?_
      obtain ⟨s, t, hst⟩ := commutant_typeBC_sp hMsp hM2 hzM hz0 hXH hXM hXg
      refine ⟨1, s, s + t, Units.ext ?_⟩
      rw [Units.val_mul, map_one, Units.val_one, Matrix.mul_one, coe_unipGL_mul_unipGL h12, hst,
        ← hNdef, hE₁, smul_add, add_smul, ← hP]
      have h2 : s • P + s • P = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
      linear_combination (norm := module) -h2
    · show alphaGroup e b ≤ centralizer (alphaGroup e a : Set G)
      rw [← hrange₁, ← hrange₂]
      rintro _ ⟨t, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact commute_diag hZ h12 h21 hφ₁ hφ₂ s t
    · show p ∉ alphaGroup e a
      rw [← hrange₁]
      rintro ⟨s, hs⟩
      have h1 : φ₁ (Multiplicative.ofAdd 1) * φ₂ (Multiplicative.ofAdd 1) =
          φ₁ (Multiplicative.ofAdd (Multiplicative.toAdd s)) * φ₂ (Multiplicative.ofAdd 0) := by
        rw [← hp12, ofAdd_toAdd, hs, ofAdd_zero, map_one, mul_one]
      exact one_ne_zero (eq_of_diag_eq hZ h12 h21 hφ₁ hφ₂ hP0 hind h1).2
    · show p ∉ alphaGroup e b
      rw [← hrange₂]
      rintro ⟨s, hs⟩
      have h1 : φ₁ (Multiplicative.ofAdd 1) * φ₂ (Multiplicative.ofAdd 1) =
          φ₁ (Multiplicative.ofAdd 0) * φ₂ (Multiplicative.ofAdd (Multiplicative.toAdd s)) := by
        rw [← hp12, ofAdd_toAdd, hs, ofAdd_zero, map_one, one_mul]
      exact one_ne_zero (eq_of_diag_eq hZ h12 h21 hφ₁ hφ₂ hP0 hind h1).1
    · show RegularOn A (alphaGroup e a ⊔ alphaGroup e b)
        {j | j ∈ alphaGroup e a ⊔ alphaGroup e b ∧ j ∉ alphaGroup e a ∧ j ∉ alphaGroup e b}
      rw [← hrange₁, ← hrange₂]
      exact hreg.1
    · show AutDiagonal A (alphaGroup e a ⊔ alphaGroup e b) (alphaGroup e a) (alphaGroup e b)
        (2 ^ m - 1)
      rw [← hrange₁, ← hrange₂, ← hK]
      exact hreg.2
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem symplecticJ23 : SymplecticJ23 := fun G _ _ A D hD _ hZ _ p ℓ hp =>
  symplecticJ23_of_family G A D hD hZ p ℓ hp

end Sp

end CFSG.ComponentClassification.RankTwoClassical
