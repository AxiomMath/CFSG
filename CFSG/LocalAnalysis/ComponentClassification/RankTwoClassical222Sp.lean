module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpPairA2

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

omit [Fintype ι] [DecidableEq ι] in
theorem exists_polarBilin_eq_one (hQ : Q.polarBilin.Nondegenerate) {y : ι → K} (hy : y ≠ 0) :
    ∃ v, Q.polarBilin v y = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, Q.polarBilin v y ≠ 0 := by
    by_contra! h
    exact hy (hQ.2 y h)
  exact ⟨(Q.polarBilin v y)⁻¹ • v, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hv]⟩

omit [DecidableEq ι] in
theorem exists_eq_smul_of_mulVec_mem {L N : Matrix ι ι K} {x y : ι → K}
    (hli : ∀ a b : K, a • (N *ᵥ x) + b • (N *ᵥ y) = 0 → a = 0 ∧ b = 0)
    (h : ∀ w, N *ᵥ w ≠ 0 → ∃ c : K, L *ᵥ w = c • (N *ᵥ w)) : ∃ c : K, L = c • N := by
  classical
  have hx0 : N *ᵥ x ≠ 0 := fun h0 => by
    have := hli 1 0 (by rw [h0, smul_zero, zero_smul, add_zero])
    exact one_ne_zero this.1
  have hy0 : N *ᵥ y ≠ 0 := fun h0 => by
    have := hli 0 1 (by rw [h0, smul_zero, zero_smul, zero_add])
    exact one_ne_zero this.2
  obtain ⟨c, hc⟩ := h x hx0
  have hpair : ∀ {u w : ι → K}, (∀ a b : K, a • (N *ᵥ u) + b • (N *ᵥ w) = 0 → a = 0 ∧ b = 0) →
      ∀ cu cw : K, L *ᵥ u = cu • (N *ᵥ u) → L *ᵥ w = cw • (N *ᵥ w) → cu = cw := by
    intro u w huw cu cw hu hw
    have hsum : N *ᵥ (u + w) ≠ 0 := fun h0 => by
      rw [mulVec_add] at h0
      have := huw 1 1 (by rw [one_smul, one_smul]; exact h0)
      exact one_ne_zero this.1
    obtain ⟨cs, hcs⟩ := h (u + w) hsum
    rw [mulVec_add, mulVec_add, hu, hw, smul_add] at hcs
    have h0 : (cu - cs) • (N *ᵥ u) + (cw - cs) • (N *ᵥ w) = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, hcs, sub_self]
    have h1 := huw (cu - cs) (cw - cs) h0
    rw [sub_eq_zero.mp h1.1, sub_eq_zero.mp h1.2]
  have hall : ∀ w, N *ᵥ w ≠ 0 → L *ᵥ w = c • (N *ᵥ w) := by
    intro w hw
    obtain ⟨cw, hcw⟩ := h w hw
    by_cases hwx : ∀ a b : K, a • (N *ᵥ w) + b • (N *ᵥ x) = 0 → a = 0 ∧ b = 0
    · rw [hcw, hpair hwx cw c hcw hc]
    ·
      push Not at hwx
      obtain ⟨a, b, hab, hne⟩ := hwx
      have ha0 : a ≠ 0 := fun ha => by
        rw [ha, zero_smul, zero_add] at hab
        exact hne ha ((smul_eq_zero.mp hab).resolve_right hx0)
      have hwy : ∀ a' b' : K, a' • (N *ᵥ w) + b' • (N *ᵥ y) = 0 → a' = 0 ∧ b' = 0 := by
        intro a' b' h'
        have hNw : N *ᵥ w = (-(a⁻¹ * b)) • (N *ᵥ x) := by
          have h1 : a⁻¹ • (a • (N *ᵥ w) + b • (N *ᵥ x)) = 0 := by rw [hab, smul_zero]
          rw [smul_add, smul_smul, inv_mul_cancel₀ ha0, one_smul, smul_smul] at h1
          rw [neg_smul, eq_neg_iff_add_eq_zero]
          exact h1
        rw [hNw, smul_smul] at h'
        obtain ⟨h1, h2⟩ := hli _ _ h'
        refine ⟨?_, h2⟩
        rcases mul_eq_zero.mp h1 with h3 | h3
        · exact h3
        · exact absurd (neg_eq_zero.mp h3) (by
            intro h4
            rw [h4, neg_zero, zero_smul] at hNw
            exact hw hNw)
      obtain ⟨cy, hcy⟩ := h y hy0
      have h1 := hpair hli c cy hc hcy
      rw [hcw, hpair hwy cw cy hcw hcy, ← h1]
  refine ⟨c, Matrix.ext_iff_mulVec.mpr fun w => ?_⟩
  rw [smul_mulVec]
  by_cases hw : N *ᵥ w = 0
  ·
    have hwx : N *ᵥ (w + x) ≠ 0 := by rwa [mulVec_add, hw, zero_add]
    have h1 := hall (w + x) hwx
    rw [mulVec_add, mulVec_add, hw, zero_add, hc] at h1
    rw [hw, smul_zero]
    exact add_eq_right.mp h1
  · exact hall w hw

theorem conj_cTwoX_of_polar {D : GL ι K}
    (hD : ∀ v w, Q.polarBilin ((D : Matrix ι ι K) *ᵥ v) ((D : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (u z : ι → K) :
    (D : Matrix ι ι K) * cTwoX Q u z * ((D⁻¹ : GL ι K) : Matrix ι ι K) =
      cTwoX Q ((D : Matrix ι ι K) *ᵥ u) ((D : Matrix ι ι K) *ᵥ z) := by
  have hDi : ∀ v w, Q.polarBilin (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
      (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = Q.polarBilin v w := fun v w => by
    rw [← hD, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, one_mulVec]
  have h1 := conj_polMat_of_polar hDi u z
  have h2 := conj_polMat_of_polar hDi z u
  rw [inv_inv] at h1 h2
  rw [cTwoX, Matrix.mul_add, Matrix.add_mul, h1, h2, cTwoX]

theorem conj_polMat_self_of_polar {D : GL ι K}
    (hD : ∀ v w, Q.polarBilin ((D : Matrix ι ι K) *ᵥ v) ((D : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (y : ι → K) :
    (D : Matrix ι ι K) * polMat Q y y * ((D⁻¹ : GL ι K) : Matrix ι ι K) =
      polMat Q ((D : Matrix ι ι K) *ᵥ y) ((D : Matrix ι ι K) *ᵥ y) := by
  have hDi : ∀ v w, Q.polarBilin (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
      (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = Q.polarBilin v w := fun v w => by
    rw [← hD, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, one_mulVec]
  have h1 := conj_polMat_of_polar hDi y y
  rwa [inv_inv] at h1

variable [CharP K 2]

theorem eq_of_polMat_self_eq (hQ : Q.polarBilin.Nondegenerate) {y y' : ι → K} (hy : y ≠ 0)
    (h : polMat Q y y = polMat Q y' y') : y = y' := by
  obtain ⟨v, hv⟩ := exists_polarBilin_eq_one hQ hy
  have h1 := congrArg (· *ᵥ v) h
  simp only [polMat_mulVec, hv, one_smul] at h1
  set c := Q.polarBilin v y' with hc
  have h2 : polMat Q y y = (c * c) • polMat Q y y := by
    conv_lhs => rw [h1]
    rw [polMat_smul_left, polMat_smul_right, smul_smul, ← h, h1]
  have h3 : polMat Q y y ≠ 0 := fun h0 => by
    have := congrArg (· *ᵥ v) h0
    simp only [polMat_mulVec, hv, one_smul, zero_mulVec] at this
    exact hy this
  have hcc : c * c = 1 := by
    by_contra hne
    apply h3
    have h4 : (1 - c * c) • polMat Q y y = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have hc1 : c = 1 := by
    have h4 : (c - 1) * (c - 1) = 0 := by
      linear_combination hcc + (1 - c) * CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h4)
  rw [h1, hc1, one_smul]

end Linear

section Commutant

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

omit [CharP K 2] in
theorem exists_polMat_of_rank_one (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) (hr : N.rank = 1) :
    ∃ (z : ι → K) (c : K), z ≠ 0 ∧ c ≠ 0 ∧ N = c • polMat Q z z := by
  classical
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  obtain ⟨v₀, hv₀⟩ : ∃ v, N *ᵥ v ≠ 0 := by
    by_contra! h
    have hN0 : N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec]
    rw [hN0, Matrix.rank_zero] at hr
    exact zero_ne_one hr
  set u := N *ᵥ v₀ with hu
  have hline : ∀ v, ∃ a : K, N *ᵥ v = a • u := by
    have hle : (K ∙ u) ≤ LinearMap.range N.mulVecLin := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨v₀, rfl⟩
    have heq : (K ∙ u) = LinearMap.range N.mulVecLin := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [finrank_span_singleton hv₀]
      exact hr.symm
    intro v
    have hv : N *ᵥ v ∈ (K ∙ u) := by
      rw [heq]
      exact ⟨v, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨a, ha.symm⟩
  choose φ hφ using hline
  obtain ⟨w₀, hw₀⟩ := exists_polarBilin_eq_one hQ hv₀
  have hφv : ∀ v, φ v = φ w₀ * Q.polarBilin v u := fun v => by
    have h1 := hadj v w₀
    rw [hφ, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hBs u w₀,
      hw₀, mul_one] at h1
    rw [h1, mul_comm]
  have hc0 : φ w₀ ≠ 0 := fun h0 => by
    apply hv₀
    rw [hu, hφ, hφv, h0, zero_mul, zero_smul]
  refine ⟨u, φ w₀, hv₀, hc0, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  rw [hφ, smul_mulVec, polMat_mulVec, hφv, smul_smul]

omit [CharP K 2] in
theorem conj_transvection_typeA {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (w : ι → K) :
    (1 + polMat Q w w) * N * (1 + polMat Q w w) = N + cTwoX Q (N *ᵥ w) w :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
    have hww : Q.polarBilin (N *ᵥ w) w = 0 := by rw [hBs]; exact halt w
    simp only [← mulVec_mulVec, add_mulVec, one_mulVec, polMat_mulVec, mulVec_add, mulVec_smul,
      cTwoX_mulVec, hww, add_zero, zero_smul, hadj v w]
    abel

omit [CharP K 2] in
theorem cTwoX_commute_typeA {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) (w : ι → K) :
    cTwoX Q (N *ᵥ w) w * N = N * cTwoX Q (N *ᵥ w) w :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, cTwoX_mulVec, cTwoX_mulVec, mulVec_add, mulVec_smul,
      mulVec_smul, hNN, smul_zero, add_zero, ← hadj, ← hadj, hNN, map_zero, LinearMap.zero_apply,
      zero_smul, zero_add, hadj]

theorem commutant_typeA (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hN0 : N ≠ 0) {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hτ : ∀ w, (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • N := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ := exists_polarBilin_eq_one hQ hy
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hli : ∀ a b : K, a • (N *ᵥ x) + b • (N *ᵥ y) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg (Q.polarBilin x) hab
    have h2 := congrArg (Q.polarBilin y) hab
    simp only [map_add, map_smul, smul_eq_mul, halt, hxy, hyx, map_zero, mul_zero, mul_one,
      zero_add, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  have hmem : ∀ w, N *ᵥ w ≠ 0 → ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hw
    have hc := conj_cTwoX_of_polar hXB (N *ᵥ w) w
    rw [hτ w, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hXNv] at hc
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
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mulVec_mem hli hmem
  exact ⟨c, by rw [← hc, add_sub_cancel]⟩

omit [CharP K 2] in
theorem eq_one_add_smul_of_fix_perp (hQ : Q.polarBilin.Nondegenerate) {z : ι → K} (hz : z ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hfix : ∀ b, Q.polarBilin b z = 0 → (X : Matrix ι ι K) *ᵥ b = b) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • polMat Q z z := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  obtain ⟨v₀, hv₀⟩ := exists_polarBilin_eq_one hQ hz
  have hperp : ∀ v, Q.polarBilin (v - Q.polarBilin v z • v₀) z = 0 := fun v => by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv₀, mul_one,
      sub_self]
  obtain ⟨y, hy⟩ : ∃ y, y = (X : Matrix ι ι K) *ᵥ v₀ - v₀ := ⟨_, rfl⟩
  have hXv : ∀ v, (X : Matrix ι ι K) *ᵥ v = v + Q.polarBilin v z • y := fun v => by
    have h1 := hfix _ (hperp v)
    rw [mulVec_sub, mulVec_smul] at h1
    rw [hy, smul_sub]
    linear_combination (norm := module) h1
  have hyb : ∀ b, Q.polarBilin b z = 0 → Q.polarBilin y b = 0 := fun b hb => by
    have h1 := hXB v₀ b
    rw [hfix b hb] at h1
    rw [hy, map_sub, LinearMap.sub_apply, h1, sub_self]
  have hyz : y = Q.polarBilin y v₀ • z := by
    rw [← sub_eq_zero]
    refine hQ.1 _ fun u => ?_
    have h1 := hyb _ (hperp u)
    rw [map_sub, map_smul, smul_eq_mul] at h1
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hBs z u]
    linear_combination h1
  refine ⟨Q.polarBilin y v₀, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  rw [hXv, add_mulVec, one_mulVec, smul_mulVec, polMat_mulVec, smul_smul, mul_comm, ← smul_smul,
    ← hyz]

theorem commutant_transvection (hQ : Q.polarBilin.Nondegenerate) {z : ι → K} (hz : z ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXz : (X : Matrix ι ι K) * polMat Q z z = polMat Q z z * X)
    (hXb : ∀ b, Q.polarBilin b z = 0 → (∀ t : K, b ≠ t • z) →
      (X : Matrix ι ι K) * polMat Q (z + b) (z + b) = polMat Q (z + b) (z + b) * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • polMat Q z z := by
  have hfixy : ∀ y : ι → K, y ≠ 0 →
      (X : Matrix ι ι K) * polMat Q y y = polMat Q y y * X → (X : Matrix ι ι K) *ᵥ y = y := by
    intro y hy h
    have h1 := conj_polMat_self_of_polar hXB y
    rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
    exact (eq_of_polMat_self_eq hQ hy h1).symm
  have hXz' := hfixy z hz hXz
  refine eq_one_add_smul_of_fix_perp hQ hz hXB fun b hb => ?_
  by_cases hbz : ∀ t : K, b ≠ t • z
  · have hzb : z + b ≠ 0 := fun h0 => hbz (-1) (by
      rw [neg_smul, one_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact h0)
    have h1 := hfixy (z + b) hzb (hXb b hb hbz)
    rw [mulVec_add, hXz'] at h1
    exact add_left_cancel h1
  · push Not at hbz
    obtain ⟨t, rfl⟩ := hbz
    rw [mulVec_smul, hXz']

theorem polarBilin_siegel_mulVec {a b : ι → K} (hab : Q.polarBilin a b = 0) (v w : ι → K) :
    Q.polarBilin ((sqZeroGL (cTwoX Q a b) (cTwoX_mul_self hab) : Matrix ι ι K) *ᵥ v)
      ((sqZeroGL (cTwoX Q a b) (cTwoX_mul_self hab) : Matrix ι ι K) *ᵥ w) = Q.polarBilin v w :=
  polarBilin_sqZeroGL_mulVec _ (fun u v => by
    have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
    rw [cTwoX_mulVec, cTwoX_mulVec, map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_smul,
      map_smul, smul_eq_mul, smul_eq_mul, hBs b v, hBs a v]
    ring) v w

end Commutant

section Sp

variable {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem sp_involution_facts {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) :
    ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *
        ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) = 0 ∧
      (∀ u v, (quadPlus n K).polarBilin
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ u) v =
        (quadPlus n K).polarBilin u (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v)) ∧
      ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) ≠ 0 ∧
      ∀ X : GL (Fin n ⊕ Fin n) K, X * M = M * X →
        (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) =
          ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) * X := by
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  refine ⟨sub_one_mul_self hM2',
    polarBilin_sub_one_adj (polarBilin_mulVec_of_mem_statedSp hM) hM2, sub_one_ne_zero fun h => by
      rw [h, orderOf_one] at hM2
      omega, fun X hXM => ?_⟩
  have h1 := congrArg (fun Y : GL (Fin n ⊕ Fin n) K =>
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hXM
  simp only [Units.val_mul] at h1
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]

theorem commutant_typeA_sp {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2)
    (h0 : ∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0)
    {X : GL (Fin n ⊕ Fin n) K} (hXH : X ∈ StatedSp n K) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedSp n K, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ c : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      1 + c • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hB0 : ∀ a, (quadPlus n K).polarBilin a a = 0 := fun a => TypeCData.pol_self a
  obtain ⟨hN, hadj, hN0, hcomm⟩ := sp_involution_facts hM hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hN0 hcomm ⊢
  have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
    rw [hNdef, add_sub_cancel]
  have halt : ∀ v, (quadPlus n K).polarBilin v (N *ᵥ v) = 0 := fun v => by
    rw [hNdef, polarBilin_quadPlus, sympForm_sub_one_mulVec]
    exact h0 v
  have hXN := hcomm X hXM
  refine commutant_typeA hQ hN hadj halt hN0 (polarBilin_mulVec_of_mem_statedSp hXH) hXN
    fun w => ?_
  have hww : polMat (quadPlus n K) w w * polMat (quadPlus n K) w w = 0 := by
    rw [polMat_mul, hB0, zero_smul]
  have hwadj : ∀ u v, (quadPlus n K).polarBilin (polMat (quadPlus n K) w w *ᵥ u) v =
      (quadPlus n K).polarBilin u (polMat (quadPlus n K) w w *ᵥ v) := fun u v => by
    rw [polMat_mulVec, polMat_mulVec, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul, polarBilin_comm (quadPlus n K) w v, mul_comm]
  have hτH : sqZeroGL (polMat (quadPlus n K) w w) hww ∈ StatedSp n K :=
    mem_statedSp_of_polarBilin (polarBilin_sqZeroGL_mulVec hww hwadj)
  have hτi : (((sqZeroGL (polMat (quadPlus n K) w w) hww)⁻¹ : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + polMat (quadPlus n K) w w := by
    show 1 - polMat (quadPlus n K) w w = 1 + polMat (quadPlus n K) w w
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (matrix_add_self _)]
  have hconj : ((sqZeroGL (polMat (quadPlus n K) w w) hww * M *
      (sqZeroGL (polMat (quadPlus n K) w w) hww)⁻¹ : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N + cTwoX (quadPlus n K) (N *ᵥ w) w := by
    rw [Units.val_mul, Units.val_mul, hτi, coe_sqZeroGL, hMN]
    calc (1 + polMat (quadPlus n K) w w) * (1 + N) * (1 + polMat (quadPlus n K) w w)
        = (1 + polMat (quadPlus n K) w w) * (1 + polMat (quadPlus n K) w w) +
          (1 + polMat (quadPlus n K) w w) * N * (1 + polMat (quadPlus n K) w w) := by
            noncomm_ring
      _ = 1 + N + cTwoX (quadPlus n K) (N *ᵥ w) w := by
        rw [conj_transvection_typeA hadj halt w, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
          Matrix.mul_one, hww, add_zero]
        rw [add_assoc (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K), matrix_add_self, add_zero,
          add_assoc]
  set S := sqZeroGL (polMat (quadPlus n K) w w) hww with hS
  have hXτ := hXg _ hτH (Units.ext (by
    rw [Units.val_mul (S * M * S⁻¹) M, Units.val_mul M (S * M * S⁻¹), hconj, hMN]
    have h1 := cTwoX_commute_typeA hN hadj w
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hN, h1]
    abel))
  have h1 := congrArg (fun Y : GL (Fin n ⊕ Fin n) K =>
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hXτ
  rw [Units.val_mul X (S * M * S⁻¹), Units.val_mul (S * M * S⁻¹) X, hconj] at h1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hXN] at h1
  exact add_left_cancel h1

theorem commutant_b1_sp {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) (hr : commRank M = 1) {X : GL (Fin n ⊕ Fin n) K}
    (hXH : X ∈ StatedSp n K) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedSp n K, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ c : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      1 + c • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hB0 : ∀ a, (quadPlus n K).polarBilin a a = 0 := fun a => TypeCData.pol_self a
  have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
    polarBilin_comm (quadPlus n K)
  obtain ⟨-, hadj, -, hcomm⟩ := sp_involution_facts hM hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hadj hcomm ⊢
  have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
    rw [hNdef, add_sub_cancel]
  obtain ⟨z, c₀, hz, hc₀, hNz⟩ := exists_polMat_of_rank_one hQ hadj (by rw [hNdef]; exact hr)
  have hXB := polarBilin_mulVec_of_mem_statedSp hXH
  have hXz : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z =
      polMat (quadPlus n K) z z * X := by
    have h1 := hcomm X hXM
    rw [hNz, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ hc₀ h1
  obtain ⟨d, hd⟩ := commutant_transvection hQ hz hXB hXz fun b hbz hb => by
    have hzb : (quadPlus n K).polarBilin z b = 0 := by rw [hBs]; exact hbz
    have hli : LinearIndependent K ![z, b] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hz, ht⟩
      · exfalso
        apply hb (-(t⁻¹ * s))
        have h1 : t⁻¹ • (s • z + t • b) = 0 := by rw [hst, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
        exact h1
    obtain ⟨w, hw⟩ := exists_polar_dual (quadPlus n K) hQ ![z, b] hli
    have hza : (quadPlus n K).polarBilin z (w 0) = 1 := by simpa using hw 0 0
    have hab : (quadPlus n K).polarBilin (w 0) b = 0 := by rw [hBs]; simpa using hw 1 0
    have hSB := polarBilin_siegel_mulVec hab
    have hSH : sqZeroGL (cTwoX (quadPlus n K) (w 0) b) (cTwoX_mul_self hab) ∈ StatedSp n K :=
      mem_statedSp_of_polarBilin hSB
    have hSz : (sqZeroGL (cTwoX (quadPlus n K) (w 0) b) (cTwoX_mul_self hab) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = z + b := by
      rw [coe_sqZeroGL, add_mulVec, one_mulVec, cTwoX_mulVec, hza, hzb, one_smul, zero_smul,
        add_zero]
    have hconj : ((sqZeroGL (cTwoX (quadPlus n K) (w 0) b) (cTwoX_mul_self hab) * M *
        (sqZeroGL (cTwoX (quadPlus n K) (w 0) b) (cTwoX_mul_self hab))⁻¹ :
          GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        1 + c₀ • polMat (quadPlus n K) (z + b) (z + b) := by
      rw [Units.val_mul, Units.val_mul, hMN, hNz, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
        Units.mul_inv, Matrix.mul_smul, Matrix.smul_mul, conj_polMat_self_of_polar hSB, hSz]
    have hPP : polMat (quadPlus n K) (z + b) (z + b) * polMat (quadPlus n K) z z =
        polMat (quadPlus n K) z z * polMat (quadPlus n K) (z + b) (z + b) := by
      simp only [polMat_mul, map_add, LinearMap.add_apply, hB0, hzb, hbz, add_zero, zero_smul]
    set S := sqZeroGL (cTwoX (quadPlus n K) (w 0) b) (cTwoX_mul_self hab) with hS
    have hXS := hXg _ hSH (Units.ext (by
      rw [Units.val_mul (S * M * S⁻¹) M, Units.val_mul M (S * M * S⁻¹), hconj, hMN, hNz]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hPP]
      module))
    have h1 := congrArg (fun Y : GL (Fin n ⊕ Fin n) K =>
      (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hXS
    rw [Units.val_mul X (S * M * S⁻¹), Units.val_mul (S * M * S⁻¹) X, hconj, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ hc₀ (add_left_cancel h1)
  refine ⟨d * c₀⁻¹, ?_⟩
  rw [hd, hNz, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀, mul_one]

theorem deltaAlpha_symplectic : DeltaAlpha .symplectic := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    have hp' : (∃ ℓ, HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .a ℓ) ∨
        HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
          sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .b 1 := hp
    obtain ⟨hp2, M, hpM, hM2, hcase⟩ : orderOf p = 2 ∧ ∃ M : GL (Fin n ⊕ Fin n) K,
        Represents e p M ∧ orderOf M = 2 ∧
          ((∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0) ∨
            commRank M = 1) := by
      rcases hp' with ⟨ℓ, hp2, M, hpM, hM2, -, -, h0⟩ | ⟨hp2, M, hpM, hM2, hr, -⟩
      · exact ⟨hp2, M, hpM, hM2, Or.inl h0⟩
      · exact ⟨hp2, M, hpM, hM2, Or.inr hr⟩
    have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
    show DeltaCentral A p (alphaGroup e p)
    refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X hXH hXM hXg => ⟨X, hXH,
      ⟨1, by rw [map_one, mul_one]⟩, ?_⟩
    obtain ⟨c, hc⟩ : ∃ c : K, (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        1 + c • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) := by
      rcases hcase with h0 | hr
      · exact commutant_typeA_sp hpM.2.1 hM2 h0 hXH hXM hXg
      · exact commutant_b1_sp hpM.2.1 hM2 hr hXH hXM hXg
    exact ⟨c, by rw [hc, add_sub_cancel_left]⟩
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Sp


end CFSG.ComponentClassification.RankTwoClassical
