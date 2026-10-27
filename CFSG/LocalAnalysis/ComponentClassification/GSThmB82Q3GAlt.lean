module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Q3G

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 Blocks HBlocks StabL PSpL CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {F : Type} [Field F]

private theorem inv_isometry {n : Type*} [Fintype n] [DecidableEq n] {A u ui : Matrix n n F}
    {c : F} (hc : c * c = 1) (hu : u * A * uᵀ = c • A) (hui : ui * u = 1) :
    ui * A * uiᵀ = c • A := by
  have e1 : A = c • (u * A * uᵀ) := by rw [hu, smul_smul, hc, one_smul]
  calc ui * A * uiᵀ = ui * (c • (u * A * uᵀ)) * uiᵀ := by rw [← e1]
    _ = c • (ui * u * A * (ui * u)ᵀ) := by
        rw [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = c • A := by rw [hui, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

private theorem commutator_isometry {n : Type*} [Fintype n] [DecidableEq n]
    {A g h gi hi : Matrix n n F} {c d : F} (hc : c * c = 1) (hd : d * d = 1)
    (hg : g * A * gᵀ = c • A) (hh : h * A * hᵀ = d • A) (hgi : gi * g = 1) (hhi : hi * h = 1) :
    g * h * gi * hi * A * (g * h * gi * hi)ᵀ = A := by
  have hgi' := inv_isometry hc hg hgi
  have hhi' := inv_isometry hd hh hhi
  calc g * h * gi * hi * A * (g * h * gi * hi)ᵀ =
      g * (h * (gi * (hi * A * hiᵀ) * giᵀ) * hᵀ) * gᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (d * c * d * c) • A := by
        rw [hhi']
        simp only [Matrix.mul_smul, Matrix.smul_mul]
        rw [hgi']
        simp only [Matrix.mul_smul, Matrix.smul_mul]
        rw [hh]
        simp only [Matrix.mul_smul, Matrix.smul_mul]
        rw [hg, smul_smul, smul_smul, smul_smul]
    _ = A := by
        rw [show d * c * d * c = 1 by linear_combination (c * c) * hd + hc, one_smul]

variable [Fintype F]

private theorem exists_smul_of_fix (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    {g : SpecialLinearGroup (Fin 4) F}
    (h : (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F g) :
    ∃ c : F, c * c = 1 ∧ (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ =
      c • (A : Matrix (Fin 4) (Fin 4) F) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at h
  have hc := coe_slConjugation A ((g⁻¹).transpose)
  rw [Matrix.SpecialLinearGroup.coe_transpose] at hc
  have hgi : (g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (mul_inv_cancel g)
  have hAA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : (A : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A *
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ = A := by
    rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), hAA, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.transpose_mul, hgi, Matrix.transpose_one, Matrix.mul_one]
  rcases eq_of_proj_eq hF h with h1 | h1
  · refine ⟨1, one_mul 1, ?_⟩
    rw [one_smul]
    nth_rewrite 1 [h1]
    rw [hc]
    exact key
  · refine ⟨-1, by norm_num, ?_⟩
    nth_rewrite 1 [h1]
    rw [hc, Matrix.neg_mul, Matrix.neg_mul, key, neg_one_smul]

private theorem card_statedProj_two_of_card_three (hF3 : Fintype.card F = 3) :
    Nat.card (CFSG.Open.StatedProj (StatedSp 2 F)) = 25920 := by
  have hF : Fintype.card F % 4 = 3 := by rw [hF3]
  have h2 := two_ne_zero_of_card_mod_four hF
  have hSp : Nat.card (StatedSp 2 F) = 51840 := by
    rw [SymplecticFlag.card_statedSp_two, Nat.card_eq_fintype_card, hF3]
    norm_num
  set Z : Subgroup (StatedSp 2 F) :=
    (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F) with hZdef
  have hZ : Nat.card Z = 2 := by
    rw [hZdef]
    exact CFSG.ClassicalInvolution.card_scalars_subgroupOf_statedSp
      (K := F) (n := 2) h2 (by norm_num)
  have h := (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  rw [hSp, hZ] at h
  have h' : Nat.card (StatedSp 2 F ⧸ Z) * 2 = 25920 * 2 := by
    rw [h]
  have hq : Nat.card (StatedSp 2 F ⧸ Z) = 25920 :=
    Nat.mul_right_cancel (by norm_num : 0 < 2) h'
  change Nat.card (CFSG.Open.StatedProj (StatedSp 2 F)) = 25920
  exact hq

private theorem exists_psp (hF3 : Fintype.card F = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ (M : Subgroup (projectiveSL 4 F))
      (e : M ≃* CFSG.Open.StatedProj (StatedSp 2 F)),
      IsSimpleGroup M ∧ Nat.card M = 25920 ∧
      (∀ y ∈ M, (conjAut 4 F A * dualAut 4 F) y = y) ∧
      (∀ g : SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = A →
          proj 4 F g ∈ M) := by
  classical
  have hF : Fintype.card F % 4 = 3 := by rw [hF3]
  have h2 := two_ne_zero_of_card_mod_four hF
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRA : R * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hRdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAR, Matrix.transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin 4) (Fin 4) F) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  obtain ⟨P, hP⟩ := exists_transpose_mul_mul_eq_omg h2 hRt hRu
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let ι : StatedSp 2 F →* SpecialLinearGroup (Fin 4) F :=
    { toFun := fun M => ⟨((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
        by
          rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul,
            (spGL_spec F M).2, mul_one, ← det_mul, hPP, det_one]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun M N => by
        apply Subtype.ext
        show ((MulAut.conj P (spGL F (M * N)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((MulAut.conj P (spGL F N) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        rw [map_mul, map_mul, Units.val_mul] }
  have hι : ∀ M, (ι M : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := fun M => by
    change ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
  set φ := (proj 4 F).comp ι with hφ
  have hker : φ.ker = (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F) := by
    ext M
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, -, hc⟩
      apply mem_statedScalars_of_spGL (c := (c : F))
      have e1 : (P : Matrix (Fin 4) (Fin 4) F) *
          ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
        rw [← hι, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      calc ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * ((P : Matrix (Fin 4) (Fin 4) F) *
            ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) := by
            simp only [← Matrix.mul_assoc]
            rw [hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
        _ = (c : F) • 1 := by
            rw [e1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPiP]
    · intro hM
      obtain ⟨c, hc⟩ := spGL_of_mem_statedScalars hM
      refine ⟨c, ?_, ?_⟩
      · have hd := (spGL_spec F M).2
        rw [hc, det_smul, det_one, mul_one, Fintype.card_fin] at hd
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, hd, Units.val_one])
      · rw [hι, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
  let e : φ.range ≃* CFSG.Open.StatedProj (StatedSp 2 F) :=
    (QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hcard : Nat.card φ.range = 25920 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_two_of_card_three hF3
  refine ⟨φ.range, e, ?_, hcard, ?_, ?_⟩
  ·
    have hK : Nat.card F = 3 ^ 1 := by rw [Nat.card_eq_fintype_card, hF3, pow_one]
    exact ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 3 1
      ((lieModel_range_of_ker Nat.prime_three le_rfl hK (by norm_num) φ hker).statedClassicalModel
        (by decide))
  ·
    rintro _ ⟨M, rfl⟩
    rw [hφ, MonoidHom.comp_apply]
    apply conjAut_dualAut_proj_of_transpose_mul_mul A
    rw [hι]
    apply conj_transpose_mul_mul hPP
    rw [← hRdef, hP]
    exact (spGL_spec F M).1
  ·
    intro g hg
    set Gm := (g : Matrix (Fin 4) (Fin 4) F) with hGm
    set Gi := ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
    have hGiG : Gi * Gm = 1 :=
      congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
        (inv_mul_cancel g)
    have hgR : Gmᵀ * R * Gm = R := by
      have h1 : Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) * Gmᵀ = Gmᵀ := by
        calc Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) * Gmᵀ =
            Gmᵀ * R * (Gm * (A : Matrix (Fin 4) (Fin 4) F) * Gmᵀ) := by
              simp only [Matrix.mul_assoc]
          _ = Gmᵀ := by rw [hg, Matrix.mul_assoc, hRA, Matrix.mul_one]
      have h3 : Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
        calc Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) =
            Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) * (Gmᵀ * Giᵀ) := by
              rw [← Matrix.transpose_mul, hGiG, Matrix.transpose_one, Matrix.mul_one]
          _ = Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) * Gmᵀ * Giᵀ := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1, ← Matrix.transpose_mul, hGiG, Matrix.transpose_one]
      calc Gmᵀ * R * Gm = Gmᵀ * R * Gm * ((A : Matrix (Fin 4) (Fin 4) F) * R) := by
            rw [hAR, Matrix.mul_one]
        _ = Gmᵀ * R * Gm * (A : Matrix (Fin 4) (Fin 4) F) * R := by
            simp only [Matrix.mul_assoc]
        _ = R := by rw [h3, Matrix.one_mul]
    set Qm : Matrix (Fin 4) (Fin 4) F :=
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * Gm * (P : Matrix (Fin 4) (Fin 4) F) with hQm
    have hPt : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
    have hQ : Qmᵀ * omg * Qm = omg := by
      rw [← hP]
      calc Qmᵀ * ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * R * P) * Qm =
          (P : Matrix (Fin 4) (Fin 4) F)ᵀ * (Gmᵀ * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ *
            (P : Matrix (Fin 4) (Fin 4) F)ᵀ) * R * ((P : Matrix (Fin 4) (Fin 4) F) *
              (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * Gm) * P := by
            rw [hQm]
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (P : Matrix (Fin 4) (Fin 4) F)ᵀ * R * P := by
            rw [hPt, hPP, Matrix.mul_one, Matrix.mul_one, hgR, Matrix.mul_assoc]
    have hQdet : Qm.det = 1 := by
      rw [hQm, det_mul, det_mul, show Gm.det = 1 from g.2, mul_one, ← det_mul, hPiP, det_one]
    set Q' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
      reindex finSumFinEquiv.symm finSumFinEquiv.symm Qm with hQ'
    have hQ'det : Q'.det ≠ 0 := by
      rw [hQ', det_reindex_self, hQdet]
      exact one_ne_zero
    set N₀ : GL (Fin 2 ⊕ Fin 2) F := GeneralLinearGroup.mkOfDetNeZero Q' hQ'det with hN₀
    have hr : ∀ X Y : Matrix (Fin 4) (Fin 4) F,
        reindex (finSumFinEquiv (m := 2) (n := 2)).symm
            (finSumFinEquiv (m := 2) (n := 2)).symm X *
          reindex (finSumFinEquiv (m := 2) (n := 2)).symm
            (finSumFinEquiv (m := 2) (n := 2)).symm Y =
        reindex (finSumFinEquiv (m := 2) (n := 2)).symm (finSumFinEquiv (m := 2) (n := 2)).symm
          (X * Y) := fun X Y => by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv]
    have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        reindex finSumFinEquiv.symm finSumFinEquiv.symm omg := by
      rw [← reindex_gram, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    have hN₀mem : N₀ ∈ StatedSp 2 F := by
      rw [ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
      apply TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mpr
      rw [← ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup, hN₀,
        GeneralLinearGroup.val_mkOfDetNeZero, hJ, hQ', transpose_reindex, hr, hr, hQ]
    refine ⟨⟨N₀, hN₀mem⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    rw [hι, coe_spGL]
    change (P : Matrix (Fin 4) (Fin 4) F) * reindex finSumFinEquiv finSumFinEquiv
      ((N₀ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = Gm
    rw [hN₀, GeneralLinearGroup.val_mkOfDetNeZero, hQ', ← Matrix.reindex_symm,
      Equiv.apply_symm_apply, hQm]
    simp only [← Matrix.mul_assoc]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]

private theorem perfect_le_of_isometry_mem (hF3 : Fintype.card F = 3) (A : GL (Fin 4) F)
    {M : Subgroup (projectiveSL 4 F)}
    (hMmem : ∀ g : SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = A →
        proj 4 F g ∈ M)
    {T : Subgroup (projectiveSL 4 F)} (hTp : ⁅T, T⁆ = T)
    (hfix : ∀ y ∈ T, (conjAut 4 F A * dualAut 4 F) y = y) : T ≤ M := by
  classical
  have hF : Fintype.card F % 4 = 3 := by rw [hF3]
  rw [← hTp, Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨g₁, rfl⟩ := proj_surjective 4 F y₁
  obtain ⟨g₂, rfl⟩ := proj_surjective 4 F y₂
  obtain ⟨c, hc, h1⟩ := exists_smul_of_fix hF A (hfix _ hy₁)
  obtain ⟨d, hd, h1'⟩ := exists_smul_of_fix hF A (hfix _ hy₂)
  have hi : ∀ g : SpecialLinearGroup (Fin 4) F, ((g⁻¹ : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) * g = 1 := fun g =>
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (inv_mul_cancel g)
  rw [← map_commutatorElement]
  apply hMmem
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact commutator_isometry hc hd h1 h1' (hi g₁) (hi g₂)

theorem exists_psp_universal (hF3 : Fintype.card F = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ (M : Subgroup (projectiveSL 4 F))
      (e : M ≃* CFSG.Open.StatedProj (StatedSp 2 F)),
      IsSimpleGroup M ∧ Nat.card M = 25920 ∧
      (∀ y ∈ M, (conjAut 4 F A * dualAut 4 F) y = y) ∧
      (∀ g : SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = A →
          proj 4 F g ∈ M) ∧
      (∀ T : Subgroup (projectiveSL 4 F), ⁅T, T⁆ = T →
        (∀ y ∈ T, (conjAut 4 F A * dualAut 4 F) y = y) → T ≤ M) := by
  obtain ⟨M, e, hMs, hMcard, hMfix, hMmem⟩ := exists_psp hF3 A hA
  exact ⟨M, e, hMs, hMcard, hMfix, hMmem,
    fun T hTp hfix => perfect_le_of_isometry_mem hF3 A hMmem hTp hfix⟩

theorem exists_psp_not_le (hF3 : Fintype.card F = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) {T : Subgroup (projectiveSL 4 F)}
    (hTk : T ≤ centralizer {proj 4 F k₀}) (hU : HasUnipotents T) (hTp : ⁅T, T⁆ = T)
    (hfix : ∀ y ∈ T, (conjAut 4 F A * dualAut 4 F) y = y) :
    ∃ M : Subgroup (projectiveSL 4 F), IsSimpleGroup M ∧ T ≤ M ∧
      (∀ y ∈ M, (conjAut 4 F A * dualAut 4 F) y = y) ∧ ∃ x ∈ M, x ∉ T := by
  classical
  have hF : Fintype.card F % 4 = 3 := by rw [hF3]
  have h2 := two_ne_zero_of_card_mod_four hF
  obtain ⟨M, _e, hMs, _hMcard, hMfix, hMmem, huniv⟩ := exists_psp_universal hF3 A hA
  refine ⟨M, hMs, ?_, hMfix, ?_⟩
  · exact huniv T hTp hfix
  ·
    have hAu : IsUnit (A : Matrix (Fin 4) (Fin 4) F).det := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.isUnit _
    obtain ⟨h, hdet, hAh, hne1, hne2⟩ := exists_transvection h2 hA hAu
    set hS : SpecialLinearGroup (Fin 4) F := ⟨h, hdet⟩ with hSdef
    refine ⟨proj 4 F hS, hMmem hS hAh, fun hT => ?_⟩
    have hN : proj 4 F hS ∈ normalizer (T : Set (projectiveSL 4 F)) := le_normalizer hT
    have hhu : IsUnit h.det := by rw [hdet]; exact isUnit_one
    have hinv : ((hS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = h⁻¹ :=
      coe_inv_eq (Matrix.mul_nonsing_inv _ hhu)
    have hconj : ((hS * k₀ * hS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        h * stdJ * h⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv]
      rfl
    have hhi : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul _ hhu
    rcases conj_k₀_eq_or_neg hF hTk hU hN with h1 | h1
    · apply hne1
      rw [hconj] at h1
      calc h * stdJ = h * stdJ * h⁻¹ * h := by rw [Matrix.mul_assoc _ h⁻¹, hhi, Matrix.mul_one]
        _ = stdJ * h := by rw [h1]
    · apply hne2
      rw [hconj] at h1
      calc h * stdJ = h * stdJ * h⁻¹ * h := by rw [Matrix.mul_assoc _ h⁻¹, hhi, Matrix.mul_one]
        _ = -(stdJ * h) := by rw [h1, Matrix.neg_mul]

end Q3G

end CFSG.ComponentClassification.GSThmB
