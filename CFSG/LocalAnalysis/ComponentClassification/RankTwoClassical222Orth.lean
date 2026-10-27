module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Sp
public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

variable (Q) in
theorem natCast_commRank_mul (hQ : Q.polarBilin.Nondegenerate) {M M' : GL ι K}
    (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v)
    (hM' : ∀ v, Q ((M' : Matrix ι ι K) *ᵥ v) = Q v) :
    (commRank (M * M') : ZMod 2) = commRank M + commRank M' := by
  set φ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)) with hφdef
  have hφ : ∀ (N : GL ι K) v, φ N v = (N : Matrix ι ι K) *ᵥ v := fun _ _ => rfl
  have hO : ∀ N : GL ι K, (∀ v, Q ((N : Matrix ι ι K) *ᵥ v) = Q v) →
      φ N ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun N hN =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hφ]; exact hN v
  have hrange : ∀ N : GL ι K, commSpace (φ N) =
      LinearMap.range ((N : Matrix ι ι K) - 1).mulVecLin := fun N => by
    ext v
    simp [hφ]
  have h1 := natCast_finrank_commSpace_mul hQ (hO M hM) (hO M' hM')
  rw [← map_mul, hrange, hrange, hrange] at h1
  exact h1

theorem rank_polMat_self (hQ : Q.polarBilin.Nondegenerate) {w : ι → K} (hw : w ≠ 0) :
    (polMat Q w w).rank = 1 := by
  rw [Matrix.rank]
  have hR : LinearMap.range (polMat Q w w).mulVecLin = K ∙ w := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, polMat_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨v, hv⟩ := exists_polarBilin_eq_one hQ hw
      exact ⟨v, by rw [Matrix.mulVecLin_apply, polMat_mulVec, hv, one_smul]⟩
  rw [hR, finrank_span_singleton hw]

omit [DecidableEq ι] in
theorem exists_mem_range_perp_not_mem (N : Matrix ι ι K) (w : ι → K)
    {T : Submodule K (ι → K)} (hT : finrank K T + 2 ≤ N.rank) :
    ∃ h, h ∈ LinearMap.range N.mulVecLin ∧ Q.polarBilin h w = 0 ∧ h ∉ T := by
  set φ : (ι → K) →ₗ[K] K := Q.polarBilin.flip w with hφ
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range N.mulVecLin)
    (LinearMap.ker φ)
  have h2 := Submodule.finrank_le (LinearMap.range N.mulVecLin ⊔ LinearMap.ker φ)
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 := Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card] at h2 h3
  rw [Module.finrank_self] at h4
  have h5 : N.rank = finrank K (LinearMap.range N.mulVecLin) := rfl
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.range N.mulVecLin ⊓ LinearMap.ker φ ≤ T := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    have hx3 := LinearMap.mem_ker.mp hx2
    rw [hφ, LinearMap.flip_apply] at hx3
    exact hcon x hx1 hx3
  have h6 := Submodule.finrank_mono hle
  omega

variable [CharP K 2]

theorem polMat_self_mul_self (w : ι → K) : polMat Q w w * polMat Q w w = 0 := by
  rw [polMat_mul, TypeCData.pol_self, zero_smul]

theorem quad_transvection_mulVec {w : ι → K} (hw : Q w = 1) (v : ι → K) :
    Q ((1 + polMat Q w w) *ᵥ v) = Q v := by
  rw [add_mulVec, one_mulVec, polMat_mulVec, quad_add, QuadraticMap.map_smul, hw, map_smul,
    smul_eq_mul, smul_eq_mul, mul_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

omit [CharP K 2] in
theorem cTwoX_adj (a b u v : ι → K) :
    Q.polarBilin (cTwoX Q a b *ᵥ u) v = Q.polarBilin u (cTwoX Q a b *ᵥ v) := by
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := polarBilin_comm Q
  rw [cTwoX_mulVec, cTwoX_mulVec, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul, hBs b v, hBs a v]
  ring

omit [CharP K 2] in
theorem cTwoX_zero_left (z : ι → K) : cTwoX Q 0 z = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [cTwoX_mulVec, map_zero, zero_smul, smul_zero, add_zero, zero_mulVec]

omit [CharP K 2] in
theorem cTwoX_add_smul_right (u z z' : ι → K) (t : K) :
    cTwoX Q u (z + t • z') = cTwoX Q u z + t • cTwoX Q u z' :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [add_mulVec, smul_mulVec, cTwoX_mulVec, cTwoX_mulVec, cTwoX_mulVec, map_add, map_smul,
      smul_eq_mul]
    module

omit [DecidableEq ι] in
theorem exists_quad_eq_one_mulVec (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (hsing : ∀ v, Q (N *ᵥ v) = 0) {w₀ : ι → K} (h0 : N *ᵥ w₀ ≠ 0) :
    ∃ w, Q w = 1 ∧ N *ᵥ w = N *ᵥ w₀ := by
  obtain ⟨y, hy⟩ := exists_polarBilin_eq_one hQ h0
  refine ⟨w₀ + N *ᵥ ((1 + Q w₀) • y), ?_, ?_⟩
  · rw [quad_add, hsing, add_zero, ← hadj, map_smul, smul_eq_mul, polarBilin_comm Q (N *ᵥ w₀),
      hy, mul_one, add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  · rw [mulVec_add, mulVec_mulVec, hN, zero_mulVec, add_zero]

omit [CharP K 2] in
theorem exists_mulVec_eq_smul_of_commute_cTwoX (hQ : Q.polarBilin.Nondegenerate)
    {X : Matrix ι ι K} {a u u' : ι → K} (hli : LinearIndependent K ![u', u, a])
    (hXu : X * cTwoX Q a u = cTwoX Q a u * X) (hXu' : X * cTwoX Q a u' = cTwoX Q a u' * X) :
    ∃ c : K, X *ᵥ a = c • a := by
  obtain ⟨z, hz⟩ := exists_polar_dual Q hQ ![u', u, a] hli
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := polarBilin_comm Q
  have h00 : Q.polarBilin u' (z 0) = 1 := by simpa using hz 0 0
  have h10 : Q.polarBilin u (z 0) = 0 := by simpa using hz 1 0
  have h20 : Q.polarBilin a (z 0) = 0 := by simpa using hz 2 0
  have h11 : Q.polarBilin u (z 1) = 1 := by simpa using hz 1 1
  have h21 : Q.polarBilin a (z 1) = 0 := by simpa using hz 2 1
  have e1 : X *ᵥ a = Q.polarBilin (X *ᵥ z 1) a • u + Q.polarBilin (X *ᵥ z 1) u • a := by
    have h := congrArg (· *ᵥ z 1) hXu
    simp only [← mulVec_mulVec, cTwoX_mulVec, hBs (z 1) a, h21, hBs (z 1) u, h11, zero_smul,
      one_smul, zero_add] at h
    exact h
  have e2 : X *ᵥ a = Q.polarBilin (X *ᵥ z 0) a • u' + Q.polarBilin (X *ᵥ z 0) u' • a := by
    have h := congrArg (· *ᵥ z 0) hXu'
    simp only [← mulVec_mulVec, cTwoX_mulVec, hBs (z 0) a, h20, hBs (z 0) u', h00, zero_smul,
      one_smul, zero_add] at h
    exact h
  have hα : Q.polarBilin (X *ᵥ z 0) a = 0 := by
    have h := congrArg (fun v => Q.polarBilin v (z 0)) (e1.symm.trans e2)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h10,
      h20, h00, mul_zero, mul_one, add_zero] at h
    exact h.symm
  exact ⟨Q.polarBilin (X *ᵥ z 0) u', by rw [e2, hα, zero_smul, zero_add]⟩

omit [DecidableEq ι] in
theorem mulVec_eq_self_of_eigen (hQ : Q.polarBilin.Nondegenerate) {N X : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0)
    (hXB : ∀ v w, Q.polarBilin (X *ᵥ v) (X *ᵥ w) = Q.polarBilin v w)
    (hXN : ∀ v, X *ᵥ (N *ᵥ v) = N *ᵥ (X *ᵥ v))
    (heig : ∀ y, ∃ c : K, X *ᵥ (N *ᵥ y) = c • (N *ᵥ y)) (y : ι → K) :
    X *ᵥ (N *ᵥ y) = N *ᵥ y := by
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := polarBilin_comm Q
  by_cases hy : N *ᵥ y = 0
  · rw [hy, mulVec_zero]
  obtain ⟨z, hz⟩ := exists_polarBilin_eq_one hQ hy
  obtain ⟨ca, hca⟩ := heig y
  obtain ⟨cb, hcb⟩ := heig z
  obtain ⟨cab, hcab⟩ := heig (y + z)
  have hay : Q.polarBilin (N *ᵥ y) y = 0 := by rw [hBs]; exact halt y
  have hby : Q.polarBilin (N *ᵥ z) y = 1 := by rw [hadj, hz]
  rw [mulVec_add, mulVec_add, hca, hcb, smul_add] at hcab
  have h1 : cb = cab := by
    have h := congrArg (fun v => Q.polarBilin v y) hcab
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hay,
      hby, mul_zero, mul_one, zero_add] at h
    exact h
  rw [h1] at hcab
  have h2 : ca = cab := by
    have h3 : (ca - cab) • (N *ᵥ y) = 0 := by linear_combination (norm := module) hcab
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy)
  have h4 : ca * cb = 1 := by
    have h5 := hXB z (N *ᵥ y)
    rw [hz, hca, map_smul, smul_eq_mul, ← hadj, ← hXN, hcb, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hby, mul_one] at h5
    exact h5
  rw [h1, ← h2] at h4
  have h6 : (ca - 1) * (ca - 1) = 0 := by
    linear_combination h4 - (ca - 1) * CharTwo.two_eq_zero (R := K)
  rw [hca, sub_eq_zero.mp (mul_self_eq_zero.mp h6), one_smul]

end Linear

section Scalars

variable {K : Type} [Field K] [Finite K]

theorem exists_ne_zero_ne_one_of_three_le_card (hK : 3 ≤ Nat.card K) : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

omit [Field K] in
theorem exists_two_ne (hK : 4 ≤ Nat.card K) (a b : K) :
    ∃ t₁ t₂ : K, t₁ ≠ t₂ ∧ t₁ ≠ a ∧ t₁ ≠ b ∧ t₂ ≠ a ∧ t₂ ≠ b := by
  classical
  have := Fintype.ofFinite K
  have hs : 1 < ((Finset.univ.erase a).erase b).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase a) (a := b)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset K)) (a := a)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := Finset.one_lt_card.mp hs
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ht₁ ht₂
  exact ⟨t₁, t₂, h12, ht₁.2, ht₁.1, ht₂.2, ht₂.1⟩

end Scalars

section Pairs

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem transvection_mul_mem_statedOmega [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {w w' : ι → K}
    (hw : Q w = 1) (hw' : Q w' = 1) :
    sqZeroGL (polMat Q w w) (polMat_self_mul_self w) *
      sqZeroGL (polMat Q w' w') (polMat_self_mul_self w') ∈ StatedOmega ⇑Q := by
  have hiso : ∀ {u : ι → K}, Q u = 1 → ∀ v, Q (((sqZeroGL (polMat Q u u)
      (polMat_self_mul_self u) : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun hu v => by
    rw [coe_sqZeroGL]
    exact quad_transvection_mulVec hu v
  have hrk : ∀ {u : ι → K}, Q u = 1 →
      commRank (sqZeroGL (polMat Q u u) (polMat_self_mul_self u)) = 1 := fun {u} hu => by
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0, QuadraticMap.map_zero] at hu
      exact zero_ne_one hu
    rw [commRank, coe_sqZeroGL, add_sub_cancel_left, rank_polMat_self hQ hu0]
  refine mem_statedOmega_of Q hQ hT (fun v => by
    rw [Units.val_mul, ← mulVec_mulVec, hiso hw, hiso hw']) ?_
  have h1 := natCast_commRank_mul Q hQ (hiso hw) (hiso hw')
  rw [hrk hw, hrk hw', Nat.cast_one, CharTwo.add_self_eq_zero,
    ZMod.natCast_eq_zero_iff_even] at h1
  exact h1

theorem conj_transvection_pair {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) {w₁ w₂ : ι → K}
    (h21 : cTwoX Q (N *ᵥ w₂) w₂ *ᵥ w₁ = 0) :
    (1 + polMat Q w₁ w₁) * (1 + polMat Q w₂ w₂) * (1 + N) *
        ((1 + polMat Q w₂ w₂) * (1 + polMat Q w₁ w₁)) =
      1 + N + cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂ := by
  have hsq : ∀ w : ι → K, (1 + polMat Q w w) * (1 + polMat Q w w) = 1 := fun w => by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, polMat_self_mul_self,
      add_zero, add_assoc, matrix_add_self, add_zero]
  have hconj : ∀ w : ι → K, (1 + polMat Q w w) * (1 + N) * (1 + polMat Q w w) =
      1 + N + cTwoX Q (N *ᵥ w) w := fun w => by
    calc (1 + polMat Q w w) * (1 + N) * (1 + polMat Q w w)
        = (1 + polMat Q w w) * (1 + polMat Q w w) +
          (1 + polMat Q w w) * N * (1 + polMat Q w w) := by
            noncomm_ring
      _ = 1 + N + cTwoX Q (N *ᵥ w) w := by
        rw [hsq, conj_transvection_typeA hadj halt w, add_assoc]
  have hP0 : polMat Q (0 : ι → K) w₁ = 0 ∧ polMat Q w₁ (0 : ι → K) = 0 :=
    ⟨Matrix.ext_iff_mulVec.mpr fun v => by rw [polMat_mulVec, map_zero, zero_smul, zero_mulVec],
      Matrix.ext_iff_mulVec.mpr fun v => by rw [polMat_mulVec, smul_zero, zero_mulVec]⟩
  have h1 : polMat Q w₁ w₁ * cTwoX Q (N *ᵥ w₂) w₂ = 0 := by
    rw [polMat_mul_of_adj Q (cTwoX_adj _ _), h21, hP0.1]
  have h2 : cTwoX Q (N *ᵥ w₂) w₂ * polMat Q w₁ w₁ = 0 := by
    rw [mul_polMat, h21, hP0.2]
  calc (1 + polMat Q w₁ w₁) * (1 + polMat Q w₂ w₂) * (1 + N) *
        ((1 + polMat Q w₂ w₂) * (1 + polMat Q w₁ w₁))
      = (1 + polMat Q w₁ w₁) * ((1 + polMat Q w₂ w₂) * (1 + N) * (1 + polMat Q w₂ w₂)) *
          (1 + polMat Q w₁ w₁) := by simp only [Matrix.mul_assoc]
    _ = (1 + polMat Q w₁ w₁) * (1 + N) * (1 + polMat Q w₁ w₁) +
          (1 + polMat Q w₁ w₁) * cTwoX Q (N *ᵥ w₂) w₂ * (1 + polMat Q w₁ w₁) := by
        rw [hconj w₂]
        noncomm_ring
    _ = 1 + N + cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂ := by
        rw [hconj w₁]
        congr 1
        rw [Matrix.add_mul, Matrix.one_mul, h1, add_zero, Matrix.mul_add, Matrix.mul_one, h2,
          add_zero]

theorem commute_cTwoX_pair [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {M X : GL ι K}
    {N : Matrix ι ι K} (hMN : (M : Matrix ι ι K) = 1 + N) (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X)
    {w₁ w₂ : ι → K} (hw₁ : Q w₁ = 1) (hw₂ : Q w₂ = 1) (h21 : cTwoX Q (N *ᵥ w₂) w₂ *ᵥ w₁ = 0) :
    (X : Matrix ι ι K) * (cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂) =
      (cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂) * X := by
  have hinv : ∀ w : ι → K, (((sqZeroGL (polMat Q w w) (polMat_self_mul_self w))⁻¹ : GL ι K) :
      Matrix ι ι K) = 1 + polMat Q w w := fun w => by
    show 1 - polMat Q w w = 1 + polMat Q w w
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (matrix_add_self _)]
  set S := sqZeroGL (polMat Q w₁ w₁) (polMat_self_mul_self w₁) *
    sqZeroGL (polMat Q w₂ w₂) (polMat_self_mul_self w₂) with hS
  have hg : ((S * M * S⁻¹ : GL ι K) : Matrix ι ι K) =
      1 + N + cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂ := by
    rw [hS, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
      hinv, hinv, coe_sqZeroGL, coe_sqZeroGL, hMN]
    exact conj_transvection_pair hadj halt h21
  have hcomm := hXg S (transvection_mul_mem_statedOmega hQ hT hw₁ hw₂) (Units.ext (by
    rw [Units.val_mul (S * M * S⁻¹) M, Units.val_mul M (S * M * S⁻¹), hg, hMN]
    have h1 := cTwoX_commute_typeA hN hadj w₁
    have h2 := cTwoX_commute_typeA hN hadj w₂
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hN, h1, h2]
    abel))
  have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hcomm
  rw [Units.val_mul X (S * M * S⁻¹), Units.val_mul (S * M * S⁻¹) X, hg] at h1
  calc (X : Matrix ι ι K) * (cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂)
      = X * (1 + N + cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂) - (X + X * N) := by
        simp only [Matrix.mul_add, Matrix.mul_one]
        abel
    _ = (1 + N + cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂) * X - (X + N * X) := by
        rw [h1, hXN]
    _ = (cTwoX Q (N *ᵥ w₁) w₁ + cTwoX Q (N *ᵥ w₂) w₂) * X := by
        simp only [Matrix.add_mul, Matrix.one_mul]
        abel

theorem commute_cTwoX_of_quad_eq_one [Finite K] (hK : 4 ≤ Nat.card K) {N X : Matrix ι ι K}
    (hu : ∃ u, Q u ≠ 0)
    (h1 : ∀ w, Q w = 1 → X * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) (w : ι → K) :
    X * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
  have hnz : ∀ w, Q w ≠ 0 → X * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
    intro w hw
    obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w)⁻¹
    have hμ0 : μ * μ ≠ 0 := by rw [← hμ]; exact inv_ne_zero hw
    have h2 := h1 (μ • w) (by rw [QuadraticMap.map_smul, smul_eq_mul, ← hμ, inv_mul_cancel₀ hw])
    rw [mulVec_smul, cTwoX_smul, Matrix.mul_smul, Matrix.smul_mul] at h2
    exact smul_right_injective _ hμ0 h2
  by_cases hw : Q w = 0
  · obtain ⟨u, hu⟩ := hu
    set Y := cTwoX Q (N *ᵥ w) u + cTwoX Q (N *ᵥ u) w with hY
    have hgood : ∀ t : K, t ≠ 0 → t ≠ Q.polarBilin w u / Q u →
        (X * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) + t • (X * Y - Y * X) = 0 := by
      intro t ht0 ht
      have hQt : Q (w + t • u) ≠ 0 := by
        rw [quad_add, hw, zero_add, QuadraticMap.map_smul, smul_eq_mul, map_smul, smul_eq_mul]
        intro h0
        have h3 : t * (t * Q u + Q.polarBilin w u) = 0 := by linear_combination h0
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact ht0 h4
        · apply ht
          rw [eq_div_iff hu]
          linear_combination h4 - Q.polarBilin w u * CharTwo.two_eq_zero (R := K)
      have h3 := hnz _ hQt
      have hexp : cTwoX Q (N *ᵥ (w + t • u)) (w + t • u) =
          cTwoX Q (N *ᵥ w) w + t • Y + (t * t) • cTwoX Q (N *ᵥ u) u :=
        Matrix.ext_iff_mulVec.mpr fun v => by
          simp only [hY, mulVec_add, mulVec_smul, add_mulVec, smul_mulVec, cTwoX_mulVec, map_add,
            map_smul, smul_eq_mul]
          module
      have hXu := hnz u hu
      rw [hexp] at h3
      calc (X * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) + t • (X * Y - Y * X)
          = (X * (cTwoX Q (N *ᵥ w) w + t • Y + (t * t) • cTwoX Q (N *ᵥ u) u) -
              (cTwoX Q (N *ᵥ w) w + t • Y + (t * t) • cTwoX Q (N *ᵥ u) u) * X) -
              (t * t) • (X * cTwoX Q (N *ᵥ u) u - cTwoX Q (N *ᵥ u) u * X) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
            module
        _ = 0 := by rw [h3, hXu, sub_self, sub_self, smul_zero, sub_zero]
    obtain ⟨t₁, t₂, h12, ht₁0, ht₁1, ht₂0, ht₂1⟩ := exists_two_ne hK 0 (Q.polarBilin w u / Q u)
    have g1 := hgood t₁ ht₁0 ht₁1
    have g2 := hgood t₂ ht₂0 ht₂1
    have hY0 : X * Y - Y * X = 0 := by
      have h3 : (t₁ - t₂) • (X * Y - Y * X) = 0 := by
        linear_combination (norm := module) g1 - g2
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h12)
    rw [hY0, smul_zero, add_zero] at g1
    exact sub_eq_zero.mp g1
  · exact hnz w hw

theorem commute_cTwoX_of_ker [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {M X : GL ι K}
    {N : Matrix ι ι K} (hMN : (M : Matrix ι ι K) = 1 + N) (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X)
    {h : ι → K} (hh : N *ᵥ h = 0) (hQh : Q h ≠ 0) {w : ι → K} (hw : Q w = 1) :
    (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q h)⁻¹
  have hQμ : Q (μ • h) = 1 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hμ, inv_mul_cancel₀ hQh]
  have hNμ : N *ᵥ (μ • h) = 0 := by rw [mulVec_smul, hh, smul_zero]
  have h1 := commute_cTwoX_pair hQ hT hMN hN hadj halt hXN hXg hw hQμ (by
    rw [hNμ, cTwoX_zero_left, zero_mulVec])
  simp only [hNμ, cTwoX_zero_left, add_zero] at h1
  exact h1

theorem commute_cTwoX_of_ker_singular [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : 3 ≤ Nat.card K) (hι : 8 ≤ Fintype.card ι) {M X : GL ι K} {N : Matrix ι ι K}
    (hMN : (M : Matrix ι ι K) = 1 + N) (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hsing : ∀ v, Q (N *ᵥ v) = 0)
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X)
    (hker : ∀ k, N *ᵥ k = 0 → Q k = 0) {w : ι → K} (hw : Q w = 1) :
    (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hrk : 4 ≤ N.rank := by
    have h1 := two_mul_finrank_le_of_forall_eq_zero hQ (U := LinearMap.ker N.mulVecLin)
      fun x hx => hker x (by simpa using hx)
    have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h1 h2
    show 4 ≤ finrank K (LinearMap.range N.mulVecLin)
    omega
  have hNw : ∀ {w : ι → K}, Q w = 1 → N *ᵥ w ≠ 0 := fun hw h0 => by
    rw [hker _ h0] at hw
    exact zero_ne_one hw
  have hrange : ∀ {h : ι → K}, h ∈ LinearMap.range N.mulVecLin → ∃ y, N *ᵥ y = h :=
    fun ⟨y, hy⟩ => ⟨y, hy⟩
  have hXu : ∀ {w u : ι → K}, Q w = 1 → N *ᵥ u = 0 → Q.polarBilin u w = 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) u = cTwoX Q (N *ᵥ w) u * X := by
    intro w u hw hu huw
    have hQ₂ : Q (w + u) = 1 := by rw [quad_add, hw, hker u hu, hBs, huw, add_zero, add_zero]
    have hN₂ : N *ᵥ (w + u) = N *ᵥ w := by rw [mulVec_add, hu, add_zero]
    have h21 : cTwoX Q (N *ᵥ (w + u)) (w + u) *ᵥ w = 0 := by
      rw [hN₂, cTwoX_mulVec, halt, zero_smul, zero_add, map_add, TypeCData.pol_self, zero_add,
        hBs w u, huw, zero_smul]
    have h := commute_cTwoX_pair hQ hT hMN hN hadj halt hXN hXg hw hQ₂ h21
    have hsum : cTwoX Q (N *ᵥ w) w + cTwoX Q (N *ᵥ w) (w + u) = cTwoX Q (N *ᵥ w) u := by
      rw [show w + u = w + (1 : K) • u by rw [one_smul], cTwoX_add_smul_right, one_smul,
        ← add_assoc, matrix_add_self, zero_add]
    rwa [hN₂, hsum] at h
  have heig : ∀ y, ∃ c : K, (X : Matrix ι ι K) *ᵥ (N *ᵥ y) = c • (N *ᵥ y) := by
    intro y
    by_cases hy : N *ᵥ y = 0
    · exact ⟨0, by rw [hy, mulVec_zero, smul_zero]⟩
    obtain ⟨w, hw, hwy⟩ := exists_quad_eq_one_mulVec hQ hN hadj hsing hy
    rw [← hwy]
    have ha0 := hNw hw
    obtain ⟨u, hu, huw, hua⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
      (T := Submodule.span K (Set.range ![N *ᵥ w])) (by
        have h := finrank_range_le_card (R := K) ![N *ᵥ w]
        rw [Fintype.card_fin] at h
        change finrank K (Submodule.span K (Set.range ![N *ᵥ w])) ≤ 1 at h
        omega)
    obtain ⟨u', hu', hu'w, hu'T⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
      (T := Submodule.span K (Set.range ![u, N *ᵥ w])) (by
        have h := finrank_range_le_card (R := K) ![u, N *ᵥ w]
        rw [Fintype.card_fin] at h
        change finrank K (Submodule.span K (Set.range ![u, N *ᵥ w])) ≤ 2 at h
        omega)
    have hli1 : LinearIndependent K ![N *ᵥ w] :=
      linearIndependent_unique_iff.mpr (by simpa using ha0)
    have hli2 : LinearIndependent K ![u, N *ᵥ w] := linearIndependent_finCons.mpr ⟨hli1, hua⟩
    have hli3 : LinearIndependent K ![u', u, N *ᵥ w] :=
      linearIndependent_finCons.mpr ⟨hli2, hu'T⟩
    obtain ⟨yu, rfl⟩ := hrange hu
    obtain ⟨yu', rfl⟩ := hrange hu'
    exact exists_mulVec_eq_smul_of_commute_cTwoX hQ hli3 (hXu hw (hNN yu) huw)
      (hXu hw (hNN yu') hu'w)
  have hfix := mulVec_eq_self_of_eigen hQ hadj halt hXB hXNv heig
  have hXab : ∀ y y', (X : Matrix ι ι K) * cTwoX Q (N *ᵥ y) (N *ᵥ y') =
      cTwoX Q (N *ᵥ y) (N *ᵥ y') * X := by
    intro y y'
    have h := conj_cTwoX_of_polar hXB (N *ᵥ y) (N *ᵥ y')
    rw [hfix, hfix] at h
    calc (X : Matrix ι ι K) * cTwoX Q (N *ᵥ y) (N *ᵥ y') =
        X * cTwoX Q (N *ᵥ y) (N *ᵥ y') * ((X⁻¹ : GL ι K) : Matrix ι ι K) * X := by
          rw [Matrix.mul_assoc _ (((X⁻¹ : GL ι K) : Matrix ι ι K)), Units.inv_mul, Matrix.mul_one]
      _ = cTwoX Q (N *ᵥ y) (N *ᵥ y') * X := by rw [h]
  have hw0 := hNw hw
  have hpair : LinearIndependent K ![w, N *ᵥ w] := LinearIndependent.pair_iff.mpr fun s t hst => by
    have h1 := congrArg (N *ᵥ ·) hst
    simp only [mulVec_add, mulVec_smul, hNN, smul_zero, add_zero, mulVec_zero] at h1
    have hs : s = 0 := (smul_eq_zero.mp h1).resolve_right hw0
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.mp hst).resolve_right hw0⟩
  obtain ⟨h, hhr, hhw, hhT⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
    (T := Submodule.span K (Set.range ![w, N *ᵥ w])) (by
      have h := finrank_range_le_card (R := K) ![w, N *ᵥ w]
      rw [Fintype.card_fin] at h
      change finrank K (Submodule.span K (Set.range ![w, N *ᵥ w])) ≤ 2 at h
      omega)
  obtain ⟨yh, rfl⟩ := hrange hhr
  have hli : LinearIndependent K ![N *ᵥ yh, w, N *ᵥ w] :=
    linearIndependent_finCons.mpr ⟨hpair, hhT⟩
  obtain ⟨z, hz⟩ := exists_polar_dual Q hQ ![N *ᵥ yh, w, N *ᵥ w] hli
  have hhh' : Q.polarBilin (N *ᵥ yh) (z 0) = 1 := by simpa using hz 0 0
  have hwh' : Q.polarBilin w (z 0) = 0 := by simpa using hz 1 0
  have hNwh' : Q.polarBilin (N *ᵥ w) (z 0) = 0 := by simpa using hz 2 0
  set h' := z 0 with hh'
  have key : ∀ μ : K, μ ≠ 0 →
      ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) +
        (μ * μ) • ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ h') h' - cTwoX Q (N *ᵥ h') h' * X) = 0 := by
    intro μ hμ
    set t := μ⁻¹ * μ⁻¹ + Q h' with ht
    have hQ₂ : Q (μ • (h' + t • N *ᵥ yh)) = 1 := by
      rw [QuadraticMap.map_smul, quad_add, QuadraticMap.map_smul, hsing, smul_zero, add_zero,
        map_smul, hBs h', hhh', smul_eq_mul, smul_eq_mul, mul_one, ht, add_left_comm,
        CharTwo.add_self_eq_zero, add_zero, ← mul_inv, mul_inv_cancel₀ (mul_ne_zero hμ hμ)]
    have hN₂ : N *ᵥ (μ • (h' + t • N *ᵥ yh)) = μ • (N *ᵥ h') := by
      rw [mulVec_smul, mulVec_add, mulVec_smul, hNN, smul_zero, add_zero]
    have h21 : cTwoX Q (N *ᵥ (μ • (h' + t • N *ᵥ yh))) (μ • (h' + t • N *ᵥ yh)) *ᵥ w = 0 := by
      rw [hN₂, cTwoX_mulVec, map_smul, ← hadj w h', hNwh', smul_zero, zero_smul, zero_add,
        map_smul, map_add, map_smul, hwh', hBs w (N *ᵥ yh), hhw, smul_zero, add_zero, smul_zero,
        zero_smul]
    have hp := commute_cTwoX_pair hQ hT hMN hN hadj halt hXN hXg hw hQ₂ h21
    have hF₂ : cTwoX Q (N *ᵥ (μ • (h' + t • N *ᵥ yh))) (μ • (h' + t • N *ᵥ yh)) =
        (μ * μ) • cTwoX Q (N *ᵥ h') h' + (μ * μ * t) • cTwoX Q (N *ᵥ h') (N *ᵥ yh) := by
      rw [hN₂, cTwoX_smul, cTwoX_add_smul_right, smul_add, smul_smul]
    have hC := hXab h' yh
    rw [hF₂] at hp
    calc ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) +
          (μ * μ) • ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ h') h' - cTwoX Q (N *ᵥ h') h' * X)
        = (X : Matrix ι ι K) * (cTwoX Q (N *ᵥ w) w + ((μ * μ) • cTwoX Q (N *ᵥ h') h' +
            (μ * μ * t) • cTwoX Q (N *ᵥ h') (N *ᵥ yh))) -
          (cTwoX Q (N *ᵥ w) w + ((μ * μ) • cTwoX Q (N *ᵥ h') h' +
            (μ * μ * t) • cTwoX Q (N *ᵥ h') (N *ᵥ yh))) * X := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hC]
          module
      _ = 0 := sub_eq_zero.mpr hp
  obtain ⟨μ₀, hμ₀0, hμ₀1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  have k1 := key 1 one_ne_zero
  have k2 := key μ₀ hμ₀0
  rw [mul_one, one_smul] at k1
  have hD : (X : Matrix ι ι K) * cTwoX Q (N *ᵥ h') h' - cTwoX Q (N *ᵥ h') h' * X = 0 := by
    have h3 : (μ₀ * μ₀ - 1) •
        ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ h') h' - cTwoX Q (N *ᵥ h') h' * X) = 0 := by
      linear_combination (norm := module) k2 - k1
    refine (smul_eq_zero.mp h3).resolve_left fun h0 => hμ₀1 ?_
    have h4 : (μ₀ - 1) * (μ₀ - 1) = 0 := by
      linear_combination h0 - (μ₀ - 1) * CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h4)
  rw [hD, add_zero] at k1
  exact sub_eq_zero.mp k1

end Pairs

section Commutant

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem commutant_typeA_orth (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : 4 ≤ Nat.card K) (hι : 8 ≤ Fintype.card ι) {M X : GL ι K}
    (hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0)
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • ((M : Matrix ι ι K) - 1) := by
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  have hXN : (X : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) = ((M : Matrix ι ι K) - 1) * X := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hN0 : (M : Matrix ι ι K) - 1 ≠ 0 := sub_one_ne_zero fun h => by
    rw [h, orderOf_one] at hM2
    omega
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hMsq
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hadj hsing hXN hN0 hN ⊢
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  have hone : ∀ w, Q w = 1 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
    by_cases hA : ∃ h, N *ᵥ h = 0 ∧ Q h ≠ 0
    · obtain ⟨h, hh, hQh⟩ := hA
      exact fun w hw => commute_cTwoX_of_ker hQ hT hMN hN hadj halt hXN hXg hh hQh hw
    · push Not at hA
      exact fun w hw => commute_cTwoX_of_ker_singular hQ hT (by omega) hι hMN hN hadj halt hsing
        hXB hXN hXg hA hw
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨w₀, hw₀, -⟩ := exists_quad_eq_one_mulVec hQ hN hadj hsing hy
  have hall := commute_cTwoX_of_quad_eq_one hK ⟨w₀, by rw [hw₀]; exact one_ne_zero⟩ hone
  exact commutant_typeA hQ hN hadj halt hN0 hXB hXN hall

end Commutant

section Families

theorem deltaCentral_of_typeA_orth {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (q : (ι → K) → K) (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : 4 ≤ Nat.card K) (hι : 8 ≤ Fintype.card ι)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {ℓ : ℕ} (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .a ℓ) :
    DeltaCentral A p (alphaGroup e p) := by
  subst hq
  obtain ⟨hp2, M, hpM, hM2, -, -, hsing⟩ := hp
  replace hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0 := hsing
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X hXH hXM hXg => ⟨X, hXH,
    ⟨1, by rw [map_one, mul_one]⟩, ?_⟩
  obtain ⟨c, hc⟩ := commutant_typeA_orth hQ hT hK hι (statedOmega_isometry hpM.2.1) hM2 hsing
    (statedOmega_isometry hXH) hXM hXg
  exact ⟨c, by rw [hc, add_sub_cancel_left]⟩

theorem deltaAlpha_orthPlus : DeltaAlpha .orthPlus := by
  intro G _ _ A D hD _ hZ hq p hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    show DeltaCentral A p (alphaGroup e p)
    exact deltaCentral_of_typeA_orth (quadPlus n K) (StatedQuadPlus n K) (coe_quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K) (exists_totallySingular_quadPlus (by omega) K)
      (by rw [hK]; exact hq) (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem deltaAlpha_orthMinus : DeltaAlpha .orthMinus := by
  intro G _ _ A D hD _ hZ hq p hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    show DeltaCentral A p (alphaGroup e p)
    exact deltaCentral_of_typeA_orth (quadMinus n K b c) (StatedQuadMinus n K b c)
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) (by rw [hK]; exact hq)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end Families

end CFSG.ComponentClassification.RankTwoClassical
