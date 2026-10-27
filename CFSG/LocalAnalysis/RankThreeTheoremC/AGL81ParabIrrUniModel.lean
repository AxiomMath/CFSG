module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrUniBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
open scoped Pointwise

section BlockFrob

variable {K : Type} [Field K] {r ε : ℕ}

theorem block_conj_frob {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → HypIndex r ε}
    (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {M G : GL (HypIndex r ε) K} {τ : K ≃+* K} {k : ℕ} (hτ : ∀ x : K, τ x = x ^ 2 ^ k)
    (hMa : CutPat a (M : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hMb : CutPat b (M : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hM'a : CutPat a ((M⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hM'b : CutPat b ((M⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hGa : CutPat a (G : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hGb : CutPat b (G : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hYa : CutPat a (((G ^ 2 ^ k)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hYb : CutPat b (((G ^ 2 ^ k)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K))
    {c : K} (hc : (G : Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix φ φ = c • 1) :
    ((M * glAut τ G * M⁻¹ * (G ^ 2 ^ k)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix φ φ = 1 := by
  have hZ : ((G ^ 2 ^ k : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (G : Matrix (HypIndex r ε) (HypIndex r ε) K) ^ 2 ^ k := Units.val_pow_eq_pow_val _ _
  have hYZ : ((G ^ 2 ^ k)⁻¹ : GL (HypIndex r ε) K) * (G : Matrix (HypIndex r ε) (HypIndex r ε) K) ^
      2 ^ k = 1 := by
    rw [← hZ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYZφ : c ^ 2 ^ k • ((((G ^ 2 ^ k)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix φ φ) = 1 := by
    have h1 := submatrix_mul_of_cutPat hφ hrange hYa (cutPat_pow hGb (2 ^ k))
    rw [hYZ, Matrix.submatrix_one _ hφ, submatrix_pow_of_cutPat hφ hrange hGa hGb, hc, smul_pow,
      one_pow, Matrix.mul_smul, Matrix.mul_one] at h1
    exact h1.symm
  have hX : ((glAut τ G : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix φ φ = τ c • 1 := by
    rw [coe_glAut, Matrix.submatrix_map, hc, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_map (map_zero τ), ← Matrix.smul_one_eq_diagonal]
  have e : (M : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((M⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXa : CutPat a ((glAut τ G : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_glAut]
    exact hGa.map τ.toRingHom
  have hXb : CutPat b ((glAut τ G : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_glAut]
    exact hGb.map τ.toRingHom
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  exact submatrix_conj_mul_eq_one hφ hrange hMa hMb hM'a hM'b hXa hXb hYb e hX
    (by rw [hτ c]; exact hYZφ)

end BlockFrob

section Conj

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {h : UnitaryFieldData 2 f K} {I : Finset ℕ}

theorem exists_pow_two_eq_one_conj_frob (hε : ε ≤ 1) (hI : IsTopCut I t)
    {M G : GL (HypIndex (t + s) ε) K} {μ ν : K} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hsM : ((M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * M = μ • hypGram (t + s) ε K)
    (hsG : ((G : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * G = ν • hypGram (t + s) ε K)
    (hfM : ∀ c ∈ I, M • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c)
    (hfG : ∀ c ∈ I, G • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c)
    (hbG : ∀ b : ↥I, ∃ c : K, blkE hI b
      (G : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1)
    (hrG : ∃ c : K, blkRes t (G : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1)
    (τ : K ≃+* K) {k : ℕ} (hτ : ∀ x : K, τ x = x ^ 2 ^ k) :
    ∃ j : ℕ, (M * glAut τ G * M⁻¹ * (G ^ 2 ^ k)⁻¹) ^ 2 ^ j = 1 := by
  set X : GL (HypIndex (t + s) ε) K := glAut τ G with hXdef
  set Z : GL (HypIndex (t + s) ε) K := G ^ 2 ^ k with hZdef
  have hν' : ν ^ 2 ^ k ≠ 0 := pow_ne_zero _ hν
  have hZmat : (Z : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      (G : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) ^ 2 ^ k :=
    Units.val_pow_eq_pow_val _ _
  have hsX : ((X : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * X = τ ν • hypGram (t + s) ε K := by
    rw [hXdef, coe_glAut]
    exact map_similitude h hsG τ
  have hsZ : ((Z : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * Z = ν ^ 2 ^ k • hypGram (t + s) ε K := by
    rw [hZmat]
    exact sim_pow hsG _
  have eM : (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      ((M⁻¹ : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eZ : (Z : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      ((Z⁻¹ : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsM' := inv_similitude h hμ hsM eM
  have hsZ' := inv_similitude h hν' hsZ eZ
  have hstab : ∀ c ∈ I, (M * X * M⁻¹ * Z⁻¹) • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c := by
    intro c hc
    have hcn : c ≤ 2 * (t + s) + ε := by
      have := (hI.le c hc).2
      omega
    have hMs : M ∈ MulAction.stabilizer (GL (HypIndex (t + s) ε) K)
        (hypFlag h (t + s) ε c) := MulAction.mem_stabilizer_iff.mpr (hfM c hc)
    have hGs : G ∈ MulAction.stabilizer (GL (HypIndex (t + s) ε) K)
        (hypFlag h (t + s) ε c) := MulAction.mem_stabilizer_iff.mpr (hfG c hc)
    have hXs : X ∈ MulAction.stabilizer (GL (HypIndex (t + s) ε) K)
        (hypFlag h (t + s) ε c) :=
      MulAction.mem_stabilizer_iff.mpr (glAut_smul_hypFlag hε τ hcn G (hfG c hc))
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hMs hXs) (Subgroup.inv_mem _ hMs))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ hGs _)))
  have hfZ : ∀ c ∈ I, Z • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c := fun c hc =>
    MulAction.mem_stabilizer_iff.mp (Subgroup.pow_mem (MulAction.stabilizer
      (GL (HypIndex (t + s) ε) K) (hypFlag h (t + s) ε c)) (MulAction.mem_stabilizer_iff.mpr
        (hfG c hc)) _)
  obtain ⟨hcM, hcM'⟩ := flagCuts_of_smul_hypFlag hε hI M hμ hsM hfM
  obtain ⟨hcG, -⟩ := flagCuts_of_smul_hypFlag hε hI G hν hsG hfG
  obtain ⟨-, hcZ'⟩ := flagCuts_of_smul_hypFlag hε hI Z hν' hsZ hfZ
  have hDmat : ((M * X * M⁻¹ * Z⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) * X *
        ((M⁻¹ : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
        ((Z⁻¹ : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) := by
    simp only [Units.val_mul]
  have hDsim : (((M * X * M⁻¹ * Z⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ * hypGram (t + s) ε K *
      (M * X * M⁻¹ * Z⁻¹ : GL (HypIndex (t + s) ε) K) = hypGram (t + s) ε K := by
    rw [hDmat, sim_mul (sim_mul (sim_mul hsM hsX) hsM') hsZ']
    have : μ * τ ν * μ⁻¹ * (ν ^ 2 ^ k)⁻¹ = 1 := by
      rw [hτ ν]
      field_simp
    rw [this, one_smul]
  have hdetX : Matrix.GeneralLinearGroup.det X = Matrix.GeneralLinearGroup.det Z := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hZmat,
      Matrix.det_pow, hXdef, coe_glAut, ← hτ]
    exact (RingHom.map_det τ.toRingHom _).symm
  have hdet : ((M * X * M⁻¹ * Z⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_mul, map_inv, map_inv,
      hdetX]
    simp [mul_comm, mul_left_comm]
  refine exists_pow_two_eq_one_of_blocks hε hI hDsim hdet hstab (fun b => ?_) ?_
  · have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
    obtain ⟨c, hc⟩ := hbG b
    exact block_conj_frob (eIdx_injective hbr) (mem_range_eIdx hbr) hτ
      (hcM.cut_predCut b.1) (hcM.1 b.1 b.2) (hcM'.cut_predCut b.1) (hcM'.1 b.1 b.2)
      (hcG.cut_predCut b.1) (hcG.1 b.1 b.2) (hcZ'.cut_predCut b.1) (hcZ'.1 b.1 b.2) hc
  · obtain ⟨c, hc⟩ := hrG
    exact block_conj_frob (resIdx_injective (s := s) (ε := ε) t) (mem_range_resIdx t) hτ
      (hcM.1 t hI.mem) hcM.2 (hcM'.1 t hI.mem) hcM'.2 (hcG.1 t hI.mem) hcG.2
      (hcZ'.1 t hI.mem) hcZ'.2 hc

end Conj

section Gamma

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {h : UnitaryFieldData 2 f K} {I : Finset ℕ}

theorem exists_pow_two_eq_one_conj_pow (hε : ε ≤ 1) (hI : IsTopCut I t)
    (γ β : semilinearSimilitudes h (t + s) ε)
    (hγf : ∀ c ∈ I, (γ : SemiGL (HypIndex (t + s) ε) K).left • hypFlag h (t + s) ε c =
      hypFlag h (t + s) ε c)
    {k : ℕ} (hγτ : ∀ x : K, (γ : SemiGL (HypIndex (t + s) ε) K).right x = x ^ 2 ^ k)
    (hβσ : (β : SemiGL (HypIndex (t + s) ε) K).right = 1)
    (hβf : ∀ c ∈ I, (β : SemiGL (HypIndex (t + s) ε) K).left • hypFlag h (t + s) ε c =
      hypFlag h (t + s) ε c)
    (hβb : ∀ b : ↥I, ∃ c : K, blkE hI b ((β : SemiGL (HypIndex (t + s) ε) K).left :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1)
    (hβr : ∃ c : K, blkRes t ((β : SemiGL (HypIndex (t + s) ε) K).left :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1) :
    ∃ j : ℕ, (γ * β * γ⁻¹ * (β ^ 2 ^ k)⁻¹) ^ 2 ^ j = 1 := by
  obtain ⟨μ, hμ0, -, hsM⟩ := γ.2
  obtain ⟨ν, hν0, -, hsG⟩ := β.2
  obtain ⟨j, hj⟩ := exists_pow_two_eq_one_conj_frob hε hI hμ0 hν0 hsM hsG hγf hβf hβb hβr
    (γ : SemiGL (HypIndex (t + s) ε) K).right hγτ
  refine ⟨j, Subtype.ext ?_⟩
  have hinl : (β : SemiGL (HypIndex (t + s) ε) K) =
      SemidirectProduct.inl (β : SemiGL (HypIndex (t + s) ε) K).left :=
    SemidirectProduct.ext rfl hβσ
  have h1 : ((γ * β * γ⁻¹ * (β ^ 2 ^ k)⁻¹ : semilinearSimilitudes h (t + s) ε) :
      SemiGL (HypIndex (t + s) ε) K) = SemidirectProduct.inl
        ((γ : SemiGL (HypIndex (t + s) ε) K).left *
          glAut (γ : SemiGL (HypIndex (t + s) ε) K).right
            (β : SemiGL (HypIndex (t + s) ε) K).left *
          (γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ *
          ((β : SemiGL (HypIndex (t + s) ε) K).left ^ 2 ^ k)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [hinl, semiGL_conj_inl, ← map_pow, ← map_inv, ← map_mul]
    rfl
  rw [Subgroup.coe_pow, h1, ← map_pow, hj, map_one]
  rfl

end Gamma

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Uni
