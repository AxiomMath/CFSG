module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatFactsL4U4 PSpL HBlocks StabL

variable {F : Type} [Field F]

theorem exists_simple_of_alternating [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ S : Subgroup (projectiveSL 4 F), IsSimpleGroup S ∧ Nat.card S = Open.ordBC 2 (p ^ f) ∧
      (∀ y ∈ S, (conjAut 4 F A * dualAut 4 F) y = y) ∧
      ∀ M : Subgroup (projectiveSL 4 F), ⁅M, M⁆ = M →
        (∀ x ∈ M, (conjAut 4 F A * dualAut 4 F) x = x) → M ≤ S := by
  classical
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
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
  have hle1 : ι.range ≤ CatFactsSp4.fixOf (graphLift A) := by
    rintro _ ⟨M, rfl⟩
    rw [mem_fixOf_graphLift_iff, hι]
    apply conj_transpose_mul_mul hPP
    rw [← hRdef, hP]
    exact (spGL_spec F M).1
  have hle2 : CatFactsSp4.fixOf (graphLift A) ≤ ι.range := by
    intro g hg
    rw [mem_fixOf_graphLift_iff] at hg
    have hPPt : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
    have hht : ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        (P : Matrix (Fin 4) (Fin 4) F))ᵀ * omg * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) *
        (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) = omg := by
      rw [← hP]
      calc ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
            (P : Matrix (Fin 4) (Fin 4) F))ᵀ *
            ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * R * (P : Matrix (Fin 4) (Fin 4) F)) *
            ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
              (P : Matrix (Fin 4) (Fin 4) F)) =
          (P : Matrix (Fin 4) (Fin 4) F)ᵀ * (g : Matrix (Fin 4) (Fin 4) F)ᵀ *
            ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ) * R *
            ((P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) *
            (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (P : Matrix (Fin 4) (Fin 4) F)ᵀ * ((g : Matrix (Fin 4) (Fin 4) F)ᵀ * R *
            (g : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) := by
            rw [hPPt, hPP]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (P : Matrix (Fin 4) (Fin 4) F)ᵀ * R * (P : Matrix (Fin 4) (Fin 4) F) := by rw [hg]
    set h := (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
      (P : Matrix (Fin 4) (Fin 4) F) with hhdef
    set N := (reindex (finSumFinEquiv (m := 2) (n := 2)) (finSumFinEquiv (m := 2) (n := 2))).symm h
      with hN
    have hNh : reindex finSumFinEquiv finSumFinEquiv N = h := Equiv.apply_symm_apply _ _
    have hr : ∀ X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
        reindex finSumFinEquiv finSumFinEquiv (X * Y) =
          reindex finSumFinEquiv finSumFinEquiv X * reindex finSumFinEquiv finSumFinEquiv Y :=
      fun X Y => (Matrix.reindexAlgEquiv F F finSumFinEquiv).map_mul X Y
    have hJ : Nᵀ * fromBlocks 0 1 (-1) 0 * N = fromBlocks 0 1 (-1) 0 := by
      apply (reindex finSumFinEquiv finSumFinEquiv).injective
      rw [hr, hr, ← transpose_reindex, hNh, reindex_gram, hht]
    have hdeth : h.det = 1 := by
      have h1 : (P : Matrix (Fin 4) (Fin 4) F).det * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
        rw [← det_mul, hPP, det_one]
      rw [hhdef, det_mul, det_mul, Matrix.SpecialLinearGroup.det_coe]
      linear_combination h1
    have hdetN : N.det ≠ 0 := by
      have h1 : N.det = h.det := by rw [← hNh, det_reindex_self]
      rw [h1, hdeth]
      exact one_ne_zero
    set N' : GL (Fin 2 ⊕ Fin 2) F := GeneralLinearGroup.mkOfDetNeZero N hdetN with hN'
    have hN'mem : N' ∈ StatedSp 2 F := by
      refine Subgroup.subset_closure ?_
      show (N' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
        (N' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 0 1 (-1) 0
      rw [hN', GeneralLinearGroup.val_mkOfDetNeZero]
      exact hJ
    refine ⟨⟨N', hN'mem⟩, Subtype.ext ?_⟩
    rw [hι, coe_spGL]
    change (P : Matrix (Fin 4) (Fin 4) F) * reindex finSumFinEquiv finSumFinEquiv
      ((N' : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F)
    rw [hN', GeneralLinearGroup.val_mkOfDetNeZero, hNh, hhdef]
    calc (P : Matrix (Fin 4) (Fin 4) F) * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) *
          (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) =
        ((P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) *
          (g : Matrix (Fin 4) (Fin 4) F) *
          ((P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) := by
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix (Fin 4) (Fin 4) F) := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  have hfixeq : CatFactsSp4.fixOf (graphLift A) = ι.range := le_antisymm hle2 hle1
  set φ := (proj 4 F).comp ι with hφ
  have hSφ : (CatFactsSp4.fixOf (graphLift A)).map (proj 4 F) = φ.range := by
    rw [hfixeq, hφ, MonoidHom.range_comp]
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
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have hq2 : p ^ f ≠ 2 := by omega
  refine ⟨φ.range, ?_, ?_, ?_, ?_⟩
  · have hcond : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ 2) ∨
        (Nat.card F = 2 ∧ 3 ≤ 2) := by
      rcases Nat.lt_or_ge (p ^ f) 4 with h4 | h4
      · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
      · exact Or.inl (Or.inr (hF ▸ h4))
    have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num) hcond
    exact ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).isSimpleGroup
  · exact GH74.card_of_lieModel_PSp (by norm_num) hp2
      (lieModel_range_of_ker hp hf hF hq2 φ hker)
  · rintro _ ⟨M, rfl⟩
    rw [hφ, MonoidHom.comp_apply, graphLift_proj]
    congr 1
    exact CatFactsSp4.mem_fixOf.mp (hle1 ⟨M, rfl⟩)
  · intro M hM hfix
    rw [← hSφ]
    exact perfect_le_map_fixOf_proj _ (graphLift_proj A) hM hfix

end CFSG.ComponentClassification.GSThmB.P211
