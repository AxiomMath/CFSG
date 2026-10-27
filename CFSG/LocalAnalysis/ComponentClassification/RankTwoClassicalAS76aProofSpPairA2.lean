module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpPerf

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

theorem conj_polMat_of_polar {D : GL ι K}
    (hD : ∀ v w, Q.polarBilin ((D : Matrix ι ι K) *ᵥ v) ((D : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (a b : ι → K) :
    ((D⁻¹ : GL ι K) : Matrix ι ι K) * polMat Q a b * D =
      polMat Q (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a) (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ b) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, polMat_mulVec, mulVec_smul, polMat_mulVec]
  congr 1
  conv_lhs => rw [show a = (D : Matrix ι ι K) *ᵥ (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a) by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]]
  exact hD v _

variable [CharP K 2]

theorem polarBilin_sqZeroGL_mulVec {E : Matrix ι ι K} (hE : E * E = 0)
    (hadj : ∀ v w, Q.polarBilin (E *ᵥ v) w = Q.polarBilin v (E *ᵥ w)) (v w : ι → K) :
    Q.polarBilin ((sqZeroGL E hE : Matrix ι ι K) *ᵥ v) ((sqZeroGL E hE : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w := by
  rw [coe_sqZeroGL, add_mulVec, add_mulVec, one_mulVec, one_mulVec]
  have hEE : Q.polarBilin (E *ᵥ v) (E *ᵥ w) = 0 := by
    rw [hadj, mulVec_mulVec, hE, zero_mulVec, map_zero]
  simp only [map_add, LinearMap.add_apply, hEE, hadj v w, add_zero]
  linear_combination Q.polarBilin v (E *ᵥ w) * CharTwo.two_eq_zero (R := K)

theorem exists_pairA2 (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hr : N.rank = 2) :
    ∃ (T : GL ι K) (N' Z : Matrix ι ι K) (b : ι → K),
      (∀ v w, Q.polarBilin ((T : Matrix ι ι K) *ᵥ v) ((T : Matrix ι ι K) *ᵥ w) =
        Q.polarBilin v w) ∧
      ((T⁻¹ : GL ι K) : Matrix ι ι K) * N * T = N' ∧ N * N' = Z ∧ N' * N = Z ∧
      (∀ s t c : K, 1 + t • N' = c • (1 + s • N) → s = 0) ∧
      (∀ s t : K, s ≠ 0 → t ≠ 0 → (s • N + t • N' + (s * t) • Z).rank = 2) ∧
      ∀ s t : K, Q.polarBilin b ((s • N + t • N' + (s * t) • Z) *ᵥ b) = s * t := by
  classical
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hB0 : ∀ a, Q.polarBilin a a = 0 := fun a => TypeCData.pol_self a
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  have hNNv : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hN0 : N ≠ 0 := fun h => by
    rw [h, Matrix.rank_zero] at hr
    exact absurd hr (by norm_num)
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) ≠ 0 := by
      by_contra! h
      exact hy (hQ.2 _ h)
    exact ⟨(Q.polarBilin x (N *ᵥ y))⁻¹ • x, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hxx : Q.polarBilin x (N *ᵥ x) = 0 := halt x
  have hyy : Q.polarBilin y (N *ᵥ y) = 0 := halt y
  have hNE : N = cTwoX Q (N *ᵥ y) (N *ᵥ x) := by
    obtain ⟨-, -, -, -, -, hrk⟩ := sub_cTwoX_of_alt hN hadj halt hxy rfl
    rw [hr] at hrk
    exact sub_eq_zero.mp (eq_zero_of_rank_eq_zero hrk)
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = N *ᵥ x := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, a₂ = N *ᵥ y := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b₂, b₂ = x + Q.polarBilin y x • (N *ᵥ x) := ⟨_, rfl⟩
  have h11 : Q.polarBilin a₁ a₁ = 0 := hB0 a₁
  have h12 : Q.polarBilin a₁ a₂ = 0 := by rw [ha₁, ha₂, hNN]
  have h21 : Q.polarBilin a₂ a₁ = 0 := by rw [ha₁, ha₂, hNN]
  have hab11 : Q.polarBilin a₁ y = 1 := by rw [ha₁, hadj, hxy]
  have hab21 : Q.polarBilin a₂ y = 0 := by rw [ha₂, hadj, hyy]
  have hab12 : Q.polarBilin a₁ b₂ = 0 := by
    rw [hb₂, ha₁, map_add, map_smul, smul_eq_mul, hNN, mul_zero, add_zero, hadj, hxx]
  have hab22 : Q.polarBilin a₂ b₂ = 1 := by
    rw [hb₂, ha₂, map_add, map_smul, smul_eq_mul, hNN, mul_zero, add_zero, hadj, hyx]
  have hbb : Q.polarBilin y b₂ = 0 := by
    rw [hb₂, map_add, map_smul, smul_eq_mul, hyx, mul_one, CharTwo.add_self_eq_zero]
  have hba11 : Q.polarBilin y a₁ = 1 := by rw [hBs, hab11]
  have hba12 : Q.polarBilin y a₂ = 0 := by rw [hBs, hab21]
  have hba21 : Q.polarBilin b₂ a₁ = 0 := by rw [hBs, hab12]
  have hba22 : Q.polarBilin b₂ a₂ = 1 := by rw [hBs, hab22]
  have hbb' : Q.polarBilin b₂ y = 0 := by rw [hBs, hbb]
  have hb22 : Q.polarBilin b₂ b₂ = 0 := hB0 b₂
  have hNv : ∀ v, N *ᵥ v = Q.polarBilin v a₂ • a₁ + Q.polarBilin v a₁ • a₂ := fun v => by
    rw [hNE, cTwoX_mulVec, ← ha₁, ← ha₂]
  have hNcX : N = cTwoX Q a₂ a₁ := by rw [ha₁, ha₂]; exact hNE
  have ha₁0 : a₁ ≠ 0 := fun h => by rw [h, map_zero, LinearMap.zero_apply] at hab11; simp at hab11
  obtain ⟨w, hw⟩ : ∃ w, w = a₂ + b₂ := ⟨_, rfl⟩
  have hww : polMat Q w w * polMat Q w w = 0 := by rw [polMat_mul, hB0, zero_smul]
  have hwadj : ∀ u v, Q.polarBilin (polMat Q w w *ᵥ u) v = Q.polarBilin u (polMat Q w w *ᵥ v) :=
    fun u v => by
      rw [polMat_mulVec, polMat_mulVec, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
        smul_eq_mul, hBs w v, mul_comm]
  have hTB := polarBilin_sqZeroGL_mulVec hww hwadj
  have hTinv : (((sqZeroGL (polMat Q w w) hww)⁻¹ : GL ι K) : Matrix ι ι K) =
      1 - polMat Q w w := rfl
  have hTa₁ : (((sqZeroGL (polMat Q w w) hww)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a₁ = a₁ := by
    rw [hTinv, sub_mulVec, one_mulVec, polMat_mulVec, hw, map_add, h12, hab12, add_zero,
      zero_smul, sub_zero]
  have hTa₂ : (((sqZeroGL (polMat Q w w) hww)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a₂ = b₂ := by
    rw [hTinv, sub_mulVec, one_mulVec, polMat_mulVec, hw, map_add, hB0, hab22, zero_add,
      one_smul, sub_add_cancel_left, neg_eq_iff_add_eq_zero, add_self_vec]
  refine ⟨sqZeroGL (polMat Q w w) hww, cTwoX Q b₂ a₁, polMat Q a₁ a₁, y, hTB, ?_, ?_, ?_,
    fun s t c h => ?_, fun s t hs ht => ?_, fun s t => ?_⟩
  · rw [hNcX, cTwoX, Matrix.mul_add, Matrix.add_mul, conj_polMat_of_polar hTB,
      conj_polMat_of_polar hTB, hTa₁, hTa₂, cTwoX]
  · rw [hNcX]
    simp only [cTwoX, Matrix.add_mul, Matrix.mul_add, polMat_mul, h12, hba22, h11, hba21,
      zero_smul, one_smul, zero_add, add_zero]
  · rw [hNcX]
    simp only [cTwoX, Matrix.add_mul, Matrix.mul_add, polMat_mul, hab12, hab22, h11, h21,
      zero_smul, one_smul, zero_add, add_zero]
  ·
    have hN'v : ∀ v, cTwoX Q b₂ a₁ *ᵥ v = Q.polarBilin v b₂ • a₁ + Q.polarBilin v a₁ • b₂ :=
      fun v => cTwoX_mulVec b₂ a₁ v
    have h1 := congrArg (· *ᵥ a₁) h
    simp only [add_mulVec, one_mulVec, smul_mulVec, hN'v, hNv, h11, hab12, h12, zero_smul,
      smul_zero, add_zero] at h1
    have hc : c = 1 := by
      by_contra hc
      have h2 : (c - 1) • a₁ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact ha₁0 ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc))
    rw [hc, one_smul, add_right_inj] at h
    have h3 := congrArg (fun X => Q.polarBilin (X *ᵥ y) b₂) h
    simp only [smul_mulVec, hN'v, hNv, map_smul, map_add, LinearMap.smul_apply,
      LinearMap.add_apply, smul_eq_mul, hba12, hba11, hab12, hab22, hbb, hb22, mul_zero,
      mul_one, add_zero, zero_add] at h3
    exact h3.symm
  ·
    have hYv : ∀ v, (s • N + t • cTwoX Q b₂ a₁ + (s * t) • polMat Q a₁ a₁) *ᵥ v =
        (s * Q.polarBilin v a₂ + t * Q.polarBilin v b₂ + s * t * Q.polarBilin v a₁) • a₁ +
          Q.polarBilin v a₁ • (s • a₂ + t • b₂) := fun v => by
      rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, hNv, cTwoX_mulVec,
        polMat_mulVec]
      module
    refine rank_eq_two_of (u := a₁) (w := s • a₂ + t • b₂) (fun α β h => ?_)
      (fun v => ⟨_, _, hYv v⟩) ⟨s⁻¹ • b₂, ?_⟩ ⟨y - t • b₂, ?_⟩
    · have h1 := congrArg (fun z => Q.polarBilin z y) h
      have h2 := congrArg (fun z => Q.polarBilin z b₂) h
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hab11, hab21, hbb', hab12, hab22, hb22, map_zero, LinearMap.zero_apply, mul_zero,
        mul_one, add_zero, zero_add] at h1 h2
      exact ⟨h1, (mul_eq_zero.mp h2).resolve_right hs⟩
    · rw [mulVec_smul, hYv, hba22, hb22, hba21, mul_one, mul_zero, mul_zero, add_zero, add_zero,
        zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hs, one_smul]
    · rw [mulVec_sub, mulVec_smul, hYv, hYv, hba12, hbb, hba11, hba22, hb22, hba21]
      module
  ·
    rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, hNv, cTwoX_mulVec,
      polMat_mulVec]
    simp only [map_add, map_smul, smul_eq_mul, hba12, hba11, hbb]
    ring

theorem symplecticPairA2 : SymplecticPairA2 := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hpM, hM2, hr, -, h0⟩ := hp
    have hMsp : M ∈ StatedSp n K := hpM.2.1
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    have hH : ∀ a : K, unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a ∈
        StatedSp n K := fun a => unipGL_mem_statedSp hMsp hMsq hE a
    obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom hZ hpM hM2 hE hH
    have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_mem_statedSp hMsp) hM2
    have halt : ∀ v, (quadPlus n K).polarBilin v
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0 := fun v => by
      rw [polarBilin_quadPlus, sympForm_sub_one_mulVec]
      exact h0 v
    obtain ⟨T, N', Z, b, hTB, hconj, hNZ, hN'Z, hinf, hrank, hform⟩ :=
      exists_pairA2 (nondegenerate_polarBilin_quadPlus n K) hE hadj halt hr
    have hTsp : T ∈ StatedSp n K := mem_statedSp_of_polarBilin hTB
    obtain ⟨a, ha⟩ := exists_represents_of_mem (e := e) hTsp
    have hmem : ∀ x ∈ ClassicalModel.alpha (.symplectic n m hn hm hnm K hK e) p,
        ∃ s : K, x = φ (Multiplicative.ofAdd s) := fun x hx => by
      have hx' : x ∈ φ.range := by rw [hrange]; exact hx
      obtain ⟨d, rfl⟩ := hx'
      exact ⟨Multiplicative.toAdd d, rfl⟩
    have hconjv : ∀ t : K,
        ((T⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (1 + t • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)) *
        (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + t • N' := fun t => by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Units.inv_mul, Matrix.mul_smul,
        Matrix.smul_mul, hconj]
    have hrepc : ∀ t : K, Represents e (a⁻¹ * φ (Multiplicative.ofAdd t) * a)
        (T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T) := by
      intro t
      have h := (hφ t).2.conj ha.inv
      rwa [inv_inv, inv_inv] at h
    have hsq : ∀ t : K, (a⁻¹ * φ (Multiplicative.ofAdd t) * a) ^ 2 = 1 := fun t => by
      rw [show a⁻¹ * φ (Multiplicative.ofAdd t) * a =
        a⁻¹ * φ (Multiplicative.ofAdd t) * a⁻¹⁻¹ by rw [inv_inv], conj_pow, (hφ t).1, mul_one,
        mul_inv_cancel]
    have hcommM : ∀ s t : K, (1 + s • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)) *
        (1 + t • N') = (1 + t • N') *
          (1 + s • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)) := fun s t => by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        smul_mul_smul_comm, hNZ, hN'Z, mul_comm s t]
      abel
    have hUV : ∀ s t : K, Commute (unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)
        hE s) (T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T) :=
      fun s t => Units.ext (by
        simp only [Units.val_mul, coe_unipGL, hconjv]
        exact hcommM s t)
    refine ⟨a, ha.1, fun x hx y hy => ?_, fun x hx y hy hxy => ?_,
      fun x hx hx1 y hy hy1 => ?_⟩
    ·
      obtain ⟨s, rfl⟩ := hmem x hx
      obtain ⟨t, rfl⟩ := hmem y hy
      exact commute_of_represents hZ (hφ s).2 (hrepc t) (hsq t) (hUV s t)
    ·
      obtain ⟨s, rfl⟩ := hmem x hx
      obtain ⟨t, rfl⟩ := hmem y hy
      have hrep2 : Represents e (φ (Multiplicative.ofAdd s))
          (T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T) :=
        hxy ▸ hrepc t
      obtain ⟨c, hc⟩ := (hφ s).2.exists_scalar hrep2
      have h1 := congrArg (fun X : GL (Fin n ⊕ Fin n) K =>
        (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hc
      simp only [Units.val_mul, coe_unipGL, hconjv, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one] at h1
      have hs := hinf s t c h1
      rw [hs, ofAdd_zero, map_one]
    ·
      obtain ⟨s, rfl⟩ := hmem x hx
      obtain ⟨t, rfl⟩ := hmem y hy
      have hs : s ≠ 0 := fun h => hx1 (by rw [h, ofAdd_zero, map_one])
      have ht : t ≠ 0 := fun h => hy1 (by rw [h, ofAdd_zero, map_one])
      obtain ⟨Y, hY⟩ : ∃ Y, Y = s • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) +
          t • N' + (s * t) • Z := ⟨_, rfl⟩
      obtain ⟨X, hXdef⟩ : ∃ X, X = unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)
          hE s * (T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T) :=
        ⟨_, rfl⟩
      have hXv : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + Y := by
        rw [hXdef, hY]
        simp only [Units.val_mul, coe_unipGL, hconjv]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          smul_mul_smul_comm, hNZ]
        abel
      have hrepX : Represents e (φ (Multiplicative.ofAdd s) *
          (a⁻¹ * φ (Multiplicative.ofAdd t) * a)) X := hXdef ▸ (hφ s).2.mul (hrepc t)
      have hcommX : Commute (φ (Multiplicative.ofAdd s)) (a⁻¹ * φ (Multiplicative.ofAdd t) * a) :=
        commute_of_represents hZ (hφ s).2 (hrepc t) (hsq t) (hUV s t)
      have hrY : Y.rank = 2 := by rw [hY]; exact hrank s t hs ht
      have hY0 : Y ≠ 0 := fun h => by
        rw [h, Matrix.rank_zero] at hrY
        exact absurd hrY (by norm_num)
      have hV2 : (T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t *
          T) ^ 2 = 1 := by
        rw [show T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T =
          T⁻¹ * unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE t * T⁻¹⁻¹ by
          rw [inv_inv], conj_pow, unipGL_sq, mul_one, mul_inv_cancel]
      have hX2 : X ^ 2 = 1 := by rw [hXdef, (hUV s t).mul_pow, unipGL_sq, hV2, one_mul]
      have hYY : Y * Y = 0 := by
        have h1 := congrArg (fun W : GL (Fin n ⊕ Fin n) K =>
          (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hX2
        simp only [pow_two, Units.val_mul, Units.val_one, hXv] at h1
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, add_assoc,
          add_eq_left, ← add_assoc, matrix_add_self, zero_add] at h1
        exact h1
      have hX1 : X ≠ 1 := fun h => hY0 (by
        have h1 := congrArg (fun W : GL (Fin n ⊕ Fin n) K =>
          (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
        simp only [hXv, Units.val_one, add_eq_left] at h1
        exact h1)
      have hz2 : (φ (Multiplicative.ofAdd s) * (a⁻¹ * φ (Multiplicative.ofAdd t) * a)) ^ 2 =
          1 := by
        rw [hcommX.mul_pow, (hφ s).1, hsq t, one_mul]
      have hz1 : φ (Multiplicative.ofAdd s) * (a⁻¹ * φ (Multiplicative.ofAdd t) * a) ≠ 1 := by
        intro h
        rw [h] at hrepX
        obtain ⟨c, hc⟩ := represents_one.exists_scalar hrepX
        have h1 := congrArg (fun W : GL (Fin n ⊕ Fin n) K =>
          (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hc
        simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.one_mul] at h1
        rw [hXv, ← one_smul K Y] at h1
        exact one_ne_zero (eq_zero_of_unip_eq_scalar hYY hY0 h1)
      refine ⟨orderOf_eq_prime hz2 hz1, X, hrepX, orderOf_eq_prime hX2 hX1, ?_, even_two, b, ?_⟩
      · rw [commRank, hXv, add_sub_cancel_left]
        exact hrY
      · show sympForm n K b ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ b) ≠ 0
        rw [hXv, add_mulVec, one_mulVec, ← polarBilin_quadPlus, map_add, TypeCData.pol_self,
          zero_add, hY, hform]
        exact mul_ne_zero hs ht
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
