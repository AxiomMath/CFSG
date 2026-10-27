module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Sp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_eq_smul_of_ker_le {L N : Matrix ι ι K} (h : ∀ v, ∃ c : K, L *ᵥ v = c • (N *ᵥ v))
    (hker : ∀ v, N *ᵥ v = 0 → L *ᵥ v = 0) : ∃ c : K, L = c • N := by
  by_cases hN : ∀ v, N *ᵥ v = 0
  · exact ⟨0, Matrix.ext_iff_mulVec.mpr fun v => by rw [hker v (hN v), zero_smul, zero_mulVec]⟩
  push Not at hN
  obtain ⟨x, hx⟩ := hN
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  rw [smul_mulVec]
  by_cases hind : ∃ t : K, N *ᵥ v = t • (N *ᵥ x)
  · obtain ⟨t, ht⟩ := hind
    have h1 : N *ᵥ (v - t • x) = 0 := by rw [mulVec_sub, mulVec_smul, ht, sub_self]
    have h2 := hker _ h1
    rw [mulVec_sub, mulVec_smul, hc, sub_eq_zero] at h2
    rw [h2, ht, smul_comm]
  · push Not at hind
    obtain ⟨cv, hcv⟩ := h v
    obtain ⟨cs, hcs⟩ := h (v + x)
    rw [mulVec_add, mulVec_add, hcv, hc, smul_add] at hcs
    have h3 : (cv - cs) • (N *ᵥ v) = (cs - c) • (N *ᵥ x) := by
      linear_combination (norm := module) hcs
    by_cases h4 : cv - cs = 0
    · rw [h4, zero_smul] at h3
      have h5 : cs - c = 0 := (smul_eq_zero.mp h3.symm).resolve_right hx
      rw [hcv, sub_eq_zero.mp h4, sub_eq_zero.mp h5]
    · exfalso
      apply hind ((cv - cs)⁻¹ * (cs - c))
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ h4, one_smul]

theorem conj_transvection_of_alt {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {w : ι → K}
    (hw : Q.polarBilin w (N *ᵥ w) = 0) :
    (1 + polMat Q w w) * N * (1 + polMat Q w w) = N + cTwoX Q (N *ᵥ w) w :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
    have hww : Q.polarBilin (N *ᵥ w) w = 0 := by rw [hBs]; exact hw
    simp only [← mulVec_mulVec, add_mulVec, one_mulVec, polMat_mulVec, mulVec_add, mulVec_smul,
      cTwoX_mulVec, hww, add_zero, zero_smul, hadj v w]
    abel

theorem conj_siegel_of_ker {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {w k : ι → K}
    (hk : N *ᵥ k = 0) :
    (1 + cTwoX Q w k) * N * (1 + cTwoX Q w k) =
      N + cTwoX Q (N *ᵥ w) k + Q.polarBilin w (N *ᵥ w) • polMat Q k k :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
    have h1 : Q.polarBilin (N *ᵥ v) k = 0 := by rw [hadj, hk, map_zero]
    have h2 : Q.polarBilin (N *ᵥ w) k = 0 := by rw [hadj, hk, map_zero]
    have h3 : Q.polarBilin (N *ᵥ w) w = Q.polarBilin w (N *ᵥ w) := hBs _ _
    simp only [← mulVec_mulVec, add_mulVec, one_mulVec, cTwoX_mulVec, polMat_mulVec, mulVec_add,
      mulVec_smul, smul_mulVec, hk, smul_zero, add_zero, h1, h2, h3, hadj v w, zero_smul,
      zero_add, map_zero, LinearMap.zero_apply]
    module

theorem mul_cTwoX_ker {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {k : ι → K}
    (hk : N *ᵥ k = 0) (w : ι → K) (c : K) :
    N * (cTwoX Q (N *ᵥ w) k + c • polMat Q k k) = 0 ∧
      (cTwoX Q (N *ᵥ w) k + c • polMat Q k k) * N = 0 := by
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  constructor
  · refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [← mulVec_mulVec, add_mulVec, smul_mulVec, cTwoX_mulVec, polMat_mulVec, mulVec_add,
      mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, hk, hNN, smul_zero,
      smul_zero, smul_zero, add_zero, zero_mulVec, add_zero]
  · refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have e1 : Q.polarBilin (N *ᵥ v) (N *ᵥ w) = 0 := by rw [hadj, hNN, map_zero]
    have e2 : Q.polarBilin (N *ᵥ v) k = 0 := by rw [hadj, hk, map_zero]
    simp only [← mulVec_mulVec, add_mulVec, smul_mulVec, cTwoX_mulVec, polMat_mulVec, e1, e2,
      zero_smul, smul_zero, add_zero, zero_mulVec]

variable [CharP K 2]

theorem exists_sub_one_mulVec_of_commute (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X) {w : ι → K} (hw : N *ᵥ w ≠ 0)
    (hXw : (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) :
    ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hc := conj_cTwoX_of_polar hXB (N *ᵥ w) w
  rw [hXw, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hXNv] at hc
  have hP : ∀ u : ι → K, N * cTwoX Q (N *ᵥ u) u = polMat Q (N *ᵥ u) (N *ᵥ u) := fun u =>
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, cTwoX_mulVec, mulVec_add, mulVec_smul, mulVec_smul, hNN, smul_zero,
        add_zero, polMat_mulVec]
  have h1 := congrArg (N * ·) hc
  simp only [hP] at h1
  have hNXw := eq_of_polMat_self_eq hQ hw h1
  have h2 : cTwoX Q (N *ᵥ w) ((X : Matrix ι ι K) *ᵥ w - w) = 0 := by
    have h3 := hc.symm
    rw [← hNXw] at h3
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h4 := congrArg (· *ᵥ v) h3
    simp only [cTwoX_mulVec, map_sub, smul_sub, zero_mulVec] at h4 ⊢
    linear_combination (norm := module) h4
  obtain ⟨v, hv⟩ := exists_polarBilin_eq_one hQ hw
  have h5 := congrArg (· *ᵥ v) h2
  simp only [cTwoX_mulVec, hv, one_smul, zero_mulVec] at h5
  refine ⟨Q.polarBilin v ((X : Matrix ι ι K) *ᵥ w - w), ?_⟩
  rw [sub_mulVec, one_mulVec]
  linear_combination (norm := module) h5 -
    CharTwo.two_eq_zero (R := K) • (Q.polarBilin v ((X : Matrix ι ι K) *ᵥ w - w) • (N *ᵥ w))

theorem eq_of_fix_of_mem [Finite K] (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    {z : ι → K} (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v)) (hz0 : z ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hfix : ∀ k, N *ᵥ k = 0 → (X : Matrix ι ι K) *ᵥ k = k)
    (hmem : ∀ w, Q.polarBilin w z = 0 →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w)) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hz
  obtain ⟨u₀, hu₀⟩ := exists_polarBilin_eq_one hQ hz0
  have hπ : ∀ v, (1 - polMat Q z u₀) *ᵥ v = v - Q.polarBilin v z • u₀ := fun v => by
    rw [sub_mulVec, one_mulVec, polMat_mulVec]
  have hπz : ∀ v, Q.polarBilin ((1 - polMat Q z u₀) *ᵥ v) z = 0 := fun v => by
    rw [hπ, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hu₀, smul_eq_mul,
      mul_one, sub_self]
  obtain ⟨s, hs⟩ := exists_eq_smul_of_ker_le (L := ((X : Matrix ι ι K) - 1) * (1 - polMat Q z u₀))
    (N := N * (1 - polMat Q z u₀)) (fun v => by
      rw [← mulVec_mulVec, ← mulVec_mulVec]
      exact hmem _ (hπz v)) (fun v hv => by
      rw [← mulVec_mulVec] at hv ⊢
      rw [sub_mulVec, one_mulVec, hfix _ hv, sub_self])
  set y := ((X : Matrix ι ι K) - 1) *ᵥ u₀ - s • (N *ᵥ u₀) with hy
  have hL : ∀ v, ((X : Matrix ι ι K) - 1) *ᵥ v = s • (N *ᵥ v) + Q.polarBilin v z • y := by
    intro v
    have h1 := congrArg (· *ᵥ v) hs
    simp only [← mulVec_mulVec, hπ, smul_mulVec, mulVec_sub, mulVec_smul] at h1
    rw [hy, smul_sub, smul_smul, mul_comm, ← smul_smul]
    linear_combination (norm := module) h1
  have hNy : N *ᵥ y = 0 := by
    have h1 : ∀ v, N *ᵥ (((X : Matrix ι ι K) - 1) *ᵥ v) = ((X : Matrix ι ι K) - 1) *ᵥ (N *ᵥ v) :=
      fun v => by rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, mulVec_sub, hXNv]
    have h2 := h1 u₀
    rw [hL, hL, mulVec_add, mulVec_smul, mulVec_smul, hNN, smul_zero, zero_add, zero_add, hu₀,
      one_smul, hadj, hNz, map_zero, zero_smul] at h2
    exact h2
  have hyz : y = Q.polarBilin y u₀ • z := by
    have hperp : ∀ v, Q.polarBilin v z = 0 → Q.polarBilin y v = 0 := fun v hv => by
      have h1 := hXB u₀ v
      have hXu : (X : Matrix ι ι K) *ᵥ u₀ = u₀ + (s • (N *ᵥ u₀) + y) := by
        have h2 := hL u₀
        rw [hu₀, one_smul] at h2
        rw [← h2, sub_mulVec, one_mulVec, add_sub_cancel]
      have hXv : (X : Matrix ι ι K) *ᵥ v = v + s • (N *ᵥ v) := by
        have h2 := hL v
        rw [hv, zero_smul, add_zero] at h2
        rw [← h2, sub_mulVec, one_mulVec, add_sub_cancel]
      rw [hXu, hXv] at h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
      have e1 : Q.polarBilin (N *ᵥ u₀) (N *ᵥ v) = 0 := by rw [hadj, hNN, map_zero]
      have e2 : Q.polarBilin y (N *ᵥ v) = 0 := by rw [← hadj, hNy, map_zero, LinearMap.zero_apply]
      have e3 : Q.polarBilin (N *ᵥ u₀) v = Q.polarBilin u₀ (N *ᵥ v) := hadj u₀ v
      rw [e1, e2, e3] at h1
      linear_combination h1 - s * Q.polarBilin u₀ (N *ᵥ v) * CharTwo.two_eq_zero (R := K)
    rw [← sub_eq_zero]
    refine hQ.1 _ fun v => ?_
    have h1 := hperp _ (hπz v)
    rw [hπ, map_sub, map_smul, smul_eq_mul] at h1
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hBs z v]
    linear_combination h1
  refine ⟨s, Q.polarBilin y u₀, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  have h1 := hL v
  rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add] at h1
  rw [h1, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, polMat_mulVec, smul_smul,
    mul_comm, ← smul_smul, ← hyz]
  abel

theorem commutant_typeBC [Finite K] (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    {z : ι → K} (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v)) (hz0 : z ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hτ : ∀ w, Q.polarBilin w z = 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X)
    (hS : ∀ w k, N *ᵥ k = 0 → Q.polarBilin w k = 0 →
      (X : Matrix ι ι K) * (cTwoX Q (N *ᵥ w) k + Q.polarBilin w (N *ᵥ w) • polMat Q k k) =
        (cTwoX Q (N *ᵥ w) k + Q.polarBilin w (N *ᵥ w) • polMat Q k k) * X) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hXz : (X : Matrix ι ι K) *ᵥ z = z := mulVec_sqrt_vector_of_commute_adj hQ hz hXB hXN
  have hfix : ∀ k, N *ᵥ k = 0 → (X : Matrix ι ι K) *ᵥ k = k := by
    intro k hk
    by_cases hli : LinearIndependent K ![k, z]
    · obtain ⟨w', hw'⟩ := exists_polar_dual Q hQ ![k, z] hli
      have hkw : Q.polarBilin k (w' 1) = 0 := by simpa using hw' 0 1
      have hzw : Q.polarBilin z (w' 1) = 1 := by simpa using hw' 1 1
      have hwNw : Q.polarBilin (w' 1) (N *ᵥ w' 1) = 1 := by rw [← hz, hBs, hzw, one_pow]
      have h1 := hS (w' 1) k hk (by rw [hBs]; exact hkw)
      rw [hwNw, one_smul] at h1
      refine mulVec_sqrt_vector_of_commute_adj hQ (fun v => ?_) hXB h1
      rw [add_mulVec, cTwoX_mulVec, polMat_mulVec, map_add, map_add, map_smul, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul]
      linear_combination (-(Q.polarBilin v (N *ᵥ w' 1) * Q.polarBilin v k)) *
        CharTwo.two_eq_zero (R := K)
    · rw [LinearIndependent.pair_iff] at hli
      push Not at hli
      obtain ⟨s, t, hst, hne⟩ := hli
      have hs : s ≠ 0 := fun hs0 => by
        rw [hs0, zero_smul, zero_add] at hst
        exact hne hs0 ((smul_eq_zero.mp hst).resolve_right hz0)
      have hk' : k = (-(s⁻¹ * t)) • z := by
        have h1 : s⁻¹ • (s • k + t • z) = 0 := by rw [hst, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h1
      rw [hk', mulVec_smul, hXz]
  have hmem : ∀ w, Q.polarBilin w z = 0 →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hwz
    by_cases hw : N *ᵥ w = 0
    · exact ⟨0, by rw [hw, smul_zero, sub_mulVec, one_mulVec, hfix w hw, sub_self]⟩
    exact exists_sub_one_mulVec_of_commute hQ hN hXB hXN hw (hτ w hwz)
  exact eq_of_fix_of_mem hQ hN hadj hz hz0 hXB hXN hfix hmem

end Linear

section Sp

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem commutant_typeBC_sp {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) {z : Fin n ⊕ Fin n → K}
    (hz : ∀ v, (quadPlus n K).polarBilin v z ^ 2 =
      (quadPlus n K).polarBilin v (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v))
    (hz0 : z ≠ 0) {X : GL (Fin n ⊕ Fin n) K} (hXH : X ∈ StatedSp n K) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedSp n K, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ s t : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      1 + s • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) +
        t • polMat (quadPlus n K) z z := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hB0 : ∀ a, (quadPlus n K).polarBilin a a = 0 := fun a => TypeCData.pol_self a
  have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
    polarBilin_comm (quadPlus n K)
  obtain ⟨hN, hadj, -, hcomm⟩ := sp_involution_facts hM hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hcomm hz ⊢
  have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
    rw [hNdef, add_sub_cancel]
  have hXN := hcomm X hXM
  have hconj : ∀ (S : GL (Fin n ⊕ Fin n) K) (E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
      S ∈ StatedSp n K → ((S * M * S⁻¹ : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N + E → E * N = N * E →
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E = E * X := by
    intro S E hS hSM hEN
    have hXS := hXg S hS (Units.ext (by
      rw [Units.val_mul (S * M * S⁻¹) M, Units.val_mul M (S * M * S⁻¹), hSM, hMN]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hN, hEN]
      abel))
    have h1 := congrArg (fun Y : GL (Fin n ⊕ Fin n) K =>
      (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hXS
    rw [Units.val_mul X (S * M * S⁻¹), Units.val_mul (S * M * S⁻¹) X, hSM] at h1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hXN] at h1
    exact add_left_cancel h1
  have hinv : ∀ (E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hE : E * E = 0),
      (((sqZeroGL E hE)⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        1 + E := fun E hE => by
    show 1 - E = 1 + E
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (matrix_add_self _)]
  refine commutant_typeBC hQ hN hadj hz hz0 (polarBilin_mulVec_of_mem_statedSp hXH) hXN
    (fun w hwz => ?_) (fun w k hk hwk => ?_)
  ·
    have hww : polMat (quadPlus n K) w w * polMat (quadPlus n K) w w = 0 := by
      rw [polMat_mul, hB0, zero_smul]
    have hwadj : ∀ u v, (quadPlus n K).polarBilin (polMat (quadPlus n K) w w *ᵥ u) v =
        (quadPlus n K).polarBilin u (polMat (quadPlus n K) w w *ᵥ v) := fun u v => by
      rw [polMat_mulVec, polMat_mulVec, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
        smul_eq_mul, hBs w v, mul_comm]
    have hwN : (quadPlus n K).polarBilin w (N *ᵥ w) = 0 := by rw [← hz, hwz, zero_pow two_ne_zero]
    refine hconj (sqZeroGL _ hww) _
      (mem_statedSp_of_polarBilin (polarBilin_sqZeroGL_mulVec hww hwadj)) ?_
      (cTwoX_commute_typeA hN hadj w)
    rw [Units.val_mul, Units.val_mul, hinv, coe_sqZeroGL, hMN]
    calc (1 + polMat (quadPlus n K) w w) * (1 + N) * (1 + polMat (quadPlus n K) w w)
        = (1 + polMat (quadPlus n K) w w) * (1 + polMat (quadPlus n K) w w) +
          (1 + polMat (quadPlus n K) w w) * N * (1 + polMat (quadPlus n K) w w) := by
            noncomm_ring
      _ = 1 + N + cTwoX (quadPlus n K) (N *ᵥ w) w := by
        rw [conj_transvection_of_alt hadj hwN, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
          Matrix.mul_one, hww, add_zero, add_assoc (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
          matrix_add_self, add_zero, add_assoc]
  ·
    obtain ⟨h1, h2⟩ := mul_cTwoX_ker hN hadj hk w ((quadPlus n K).polarBilin w (N *ᵥ w))
    refine hconj (sqZeroGL _ (cTwoX_mul_self hwk)) _
      (mem_statedSp_of_polarBilin (polarBilin_siegel_mulVec hwk)) ?_ (by rw [h1, h2])
    rw [Units.val_mul, Units.val_mul, hinv, coe_sqZeroGL, hMN]
    calc (1 + cTwoX (quadPlus n K) w k) * (1 + N) * (1 + cTwoX (quadPlus n K) w k)
        = (1 + cTwoX (quadPlus n K) w k) * (1 + cTwoX (quadPlus n K) w k) +
          (1 + cTwoX (quadPlus n K) w k) * N * (1 + cTwoX (quadPlus n K) w k) := by
            noncomm_ring
      _ = 1 + N + (cTwoX (quadPlus n K) (N *ᵥ w) k +
            (quadPlus n K).polarBilin w (N *ᵥ w) • polMat (quadPlus n K) k k) := by
        rw [conj_siegel_of_ker hadj hk, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
          Matrix.mul_one, cTwoX_mul_self hwk, add_zero,
          add_assoc (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K), matrix_add_self, add_zero,
          add_assoc, add_assoc]

end Sp

end CFSG.ComponentClassification.RankTwoClassical
