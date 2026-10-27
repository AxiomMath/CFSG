module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Aut
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5 Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.Final.ModelSp
open CFSG.RankThree.PartTwo.KFacts

namespace CFSG.GH74.Ivk413


variable {F : Type} [Field F]

theorem glSigma_fieldSp (σ : F ≃+* F) (g : StatedSp 2 F) :
    glSigma F ((fieldSp 2 F σ g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      glAut σ (glSigma F (g : GL (Fin 2 ⊕ Fin 2) F)) := by
  apply Units.ext
  rw [coe_glSigma, coe_glAut, coe_glSigma, coe_fieldSp]
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem glSigma_conjSp (A : gsp 2 F) (g : StatedSp 2 F) :
    glSigma F ((conjSp 2 F A g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) * glSigma F (g : GL (Fin 2 ⊕ Fin 2) F) *
        (glSigma F (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ := by
  rw [coe_conjSp, map_mul, map_mul, map_inv]

theorem semiRep_sp_aux [Finite F] (h2 : (2 : F) ≠ 0) (β : MulAut (PG (ModelData.sp F))) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), ∀ g : ↥(ModelData.sp F).K4,
      ∃ hg : glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) * glAut σ (g : GL (Fin 4) F) *
          (glSigma F (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ ∈ (ModelData.sp F).K4,
        β (mkP (ModelData.sp F) g) = mkP (ModelData.sp F) ⟨_, hg⟩ := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have : CharP F 2 := ringChar.of_eq h
    exact CharTwo.two_eq_zero
  let β' : MulAut (StatedProj (StatedSp 2 F)) := MulAut.congr (spEquiv F).symm β
  have hβ' : ∀ x, spEquiv F (β' x) = β (spEquiv F x) := fun x => by
    simp [β', MulAut.congr_apply]
  obtain ⟨A, σ, hAσ⟩ := psp4_odd_automorphism_normal_form hchar β'
  refine ⟨A, σ, fun g => ?_⟩
  obtain ⟨g₀, rfl⟩ := (spMulEquiv (F := F)).surjective g
  have hmem : glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) * glAut σ (glSigma F (g₀ : GL (Fin 2 ⊕ Fin 2) F)) *
      (glSigma F (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ ∈ (ModelData.sp F).K4 := by
    have := (spMulEquiv (conjSp 2 F A (fieldSp 2 F σ g₀))).2
    rw [coe_spMulEquiv, glSigma_conjSp, glSigma_fieldSp] at this
    exact this
  refine ⟨by simpa only [coe_spMulEquiv] using hmem, ?_⟩
  have h1 : β (mkP (ModelData.sp F) (spMulEquiv g₀)) =
      mkP (ModelData.sp F) (spMulEquiv (conjSp 2 F A (fieldSp 2 F σ g₀))) := by
    have e1 : mkP (ModelData.sp F) (spMulEquiv g₀) = spEquiv F (QuotientGroup.mk g₀) := rfl
    rw [e1, ← hβ', hAσ, MulAut.mul_apply]
    rfl
  rw [h1]
  congr 1
  apply Subtype.ext
  show ((spMulEquiv (conjSp 2 F A (fieldSp 2 F σ g₀)) : ↥(ModelData.sp F).K4) : GL (Fin 4) F) =
    glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) * glAut σ ((spMulEquiv g₀ : ↥(ModelData.sp F).K4) : GL (Fin 4) F) *
      (glSigma F (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹
  simp only [coe_spMulEquiv, glSigma_conjSp, glSigma_fieldSp]


theorem blk4_smul' (μ : F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    μ • blk4 X Y = blk4 (μ • X) (μ • Y) := by
  rw [blk4_eq_reindex, blk4_eq_reindex, ← map_smul, fromBlocks_smul]
  simp

theorem exists_diagGL_of_comm_GL (h2 : (2 : F) ≠ 0) {g : GL (Fin 4) F}
    (hc : g * yGL F = yGL F * g) : ∃ a b : GL (Fin 2) F, g = diagGL a b := by
  have hy : ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 (-1) 1 := by
    rw [yGL, coe_diagGL]
    simp
  have hc' : g⁻¹ * yGL F = yGL F * g⁻¹ :=
    (Commute.inv_left (show Commute g (yGL F) from hc)).eq
  obtain ⟨A, B, hAB⟩ := exists_blk4_of_comm h2 (g := (g : Matrix (Fin 4) (Fin 4) F))
    (by
      have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hc
      simpa only [Units.val_mul, hy] using this)
  obtain ⟨A', B', hAB'⟩ := exists_blk4_of_comm h2
    (g := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (by
      have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hc'
      simpa only [Units.val_mul, hy] using this)
  have h1 : blk4 (A * A') (B * B') = blk4 1 1 := by
    rw [← blk4_mul, ← hAB, ← hAB', g.mul_inv, blk4_one]
  have h2' : blk4 (A' * A) (B' * B) = blk4 1 1 := by
    rw [← blk4_mul, ← hAB, ← hAB', g.inv_mul, blk4_one]
  obtain ⟨hA1, hB1⟩ := blk4_inj h1
  obtain ⟨hA2, hB2⟩ := blk4_inj h2'
  refine ⟨⟨A, A', hA1, hA2⟩, ⟨B, B', hB1, hB2⟩, ?_⟩
  apply Units.ext
  rw [coe_diagGL]
  exact hAB

theorem exists_scalar_of_comm_sl2 {a : GL (Fin 2) F}
    (h : ∀ x : GL (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F).det = 1 → a * x = x * a) :
    ∃ c : Fˣ, a = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have hscal : (a : Matrix (Fin 2) (Fin 2) F) ∈ Set.range (Matrix.scalar (Fin 2)) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    let x : SpecialLinearGroup (Fin 2) F :=
      ⟨t.toMatrix, by
        simpa [Matrix.TransvectionStruct.toMatrix] using
          Matrix.det_transvection_of_ne t.i t.j t.hij t.c⟩
    have hx : ((SpecialLinearGroup.toGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact x.2
    have h1 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F))
      (h (SpecialLinearGroup.toGL x) hx)
    simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] at h1
    exact (show (t.toMatrix * (a : Matrix (Fin 2) (Fin 2) F) = (a : Matrix (Fin 2) (Fin 2) F) * t.toMatrix) from
      h1.symm)
  obtain ⟨c', hc'⟩ := hscal
  have hne : c' ≠ 0 := by
    intro h0
    have h1 : ((a : Matrix (Fin 2) (Fin 2) F)) = 0 := by rw [← hc', h0]; simp
    have h2 := a.val_inv
    rw [h1] at h2
    simp at h2
  refine ⟨Units.mk0 c' hne, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  exact hc'.symm


theorem glSigma_sim (A : gsp 2 F) : ∃ μ : Fˣ,
    ((glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
        blk4 (J2m F) (J2m F) * ((glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (μ : F) • blk4 (J2m F) (J2m F) := by
  obtain ⟨μ, hμ⟩ := mem_gsp.1 A.2
  refine ⟨μ, ?_⟩
  have e : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      Matrix.reindex sigma sigma X = Matrix.reindexAlgEquiv F F sigma X := fun X =>
    (congrFun (Matrix.coe_reindexAlgEquiv F F sigma) X).symm
  rw [coe_glSigma, ← reindex_gram, Matrix.transpose_reindex, e, e, e, ← map_mul, ← map_mul, hμ,
    map_smul]

theorem phi_fix_sp (φ : F ≃+* F) (hφ : ∀ a ∈ (ModelData.sp F).H2,
    φ ((a : Matrix (Fin 2) (Fin 2) F).trace) = (a : Matrix (Fin 2) (Fin 2) F).trace) :
    ∀ t, φ t = t := by
  intro t
  let g : SpecialLinearGroup (Fin 2) F := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hg : (SpecialLinearGroup.toGL g : GL (Fin 2) F) ∈ (ModelData.sp F).H2 := by
    rw [(ModelData.sp F).mem_H2]
    refine ⟨mem_U2_sp.2 ?_, ?_⟩ <;> (rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact g.2)
  have := hφ _ hg
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at this
  simpa [g, Matrix.trace, Fin.sum_univ_two] using this


theorem det_of_sim {c : Fˣ} {b : GL (Fin 2) F} {μ : Fˣ}
    (h : ((diagGL (sc2 c) b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * blk4 (J2m F) (J2m F) *
      ((diagGL (sc2 c) b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (μ : F) • blk4 (J2m F) (J2m F)) :
    ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (c : F) ^ 2 := by
  rw [coe_diagGL, blk4_transpose, blk4_mul, blk4_mul, blk4_smul'] at h
  obtain ⟨h1, h2'⟩ := blk4_inj h
  rw [transpose_mul_J2m_mul] at h1 h2'
  have e1 := congrFun (congrFun h1 0) 1
  have e2 := congrFun (congrFun h2' 0) 1
  simp only [J2m, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at e1 e2
  rw [e2, ← e1, det_sc2]


theorem eq_diagGL_scalar_of_comm (h2 : (2 : F) ≠ 0) {B : GL (Fin 4) F}
    (hB : ∀ a : GL (Fin 2) F, (a : Matrix (Fin 2) (Fin 2) F).det = 1 →
      B * blkL F a = blkL F a * B) :
    ∃ (c : Fˣ) (b : GL (Fin 2) F), B = diagGL (sc2 c) b := by
  have hyc : B * yGL F = yGL F * B := by
    have hyb : yGL F = blkL F (-1) := rfl
    rw [hyb]
    exact hB (-1) (by simp [Matrix.det_neg])
  obtain ⟨a, b, rfl⟩ := exists_diagGL_of_comm_GL h2 hyc
  have hcomm : ∀ x : GL (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F).det = 1 → a * x = x * a := by
    intro x hx
    have := hB x hx
    rw [blkL_apply, diagGL_mul, diagGL_mul, mul_one, one_mul] at this
    exact (diagGL_inj this).1
  obtain ⟨c, hc⟩ := exists_scalar_of_comm_sl2 hcomm
  exact ⟨c, b, by rw [hc]⟩

theorem autInner_sp [Finite F] (h2 : (2 : F) ≠ 0) (hG : GoodModel (ModelData.sp F)) :
    AutInner (ModelData.sp F) := by
  intro β _ hfix
  obtain ⟨A, σ, hrep⟩ := semiRep_sp_aux h2 β
  set B : GL (Fin 4) F := glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) with hB
  have hcomm : ∀ a : ↥(ModelData.sp F).H2,
      B * glAut σ (blkL F (a : GL (Fin 2) F)) * B⁻¹ = blkL F a :=
    semiconj_fixes_blkL hG B σ β hrep hfix
  have hσ1 : ∀ t, σ t = t :=
    phi_fix_sp σ fun a ha => phi_fixes_trace B σ a (hcomm ⟨a, ha⟩)
  have hσ : σ = 1 := RingEquiv.ext hσ1
  have hgl : ∀ g : GL (Fin 4) F, glAut σ g = g := by
    intro g
    rw [hσ, map_one]
    rfl
  have hBc : ∀ a : GL (Fin 2) F, (a : Matrix (Fin 2) (Fin 2) F).det = 1 →
      B * blkL F a = blkL F a * B := by
    intro a ha
    have hH : a ∈ (ModelData.sp F).H2 := by
      rw [(ModelData.sp F).mem_H2]
      exact ⟨mem_U2_sp.2 ha, ha⟩
    have := hcomm ⟨a, hH⟩
    rw [hgl] at this
    exact (mul_inv_eq_iff_eq_mul.1 this)
  obtain ⟨c, b, hBb⟩ := eq_diagGL_scalar_of_comm h2 hBc
  obtain ⟨μ, hμ⟩ := glSigma_sim A
  have hdetb : (b : Matrix (Fin 2) (Fin 2) F).det = (c : F) ^ 2 :=
    det_of_sim (c := c) (b := b) (μ := μ) (by rw [← hBb]; exact hμ)
  let b' : GL (Fin 2) F := sc2 c⁻¹ * b
  have hb' : (b' : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    show ((sc2 c⁻¹ * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1
    rw [Units.val_mul, Matrix.det_mul, det_sc2, hdetb, Units.val_inv_eq_inv_val]
    have : (c : F) ≠ 0 := c.ne_zero
    field_simp
  let B' : GL (Fin 4) F := diagGL 1 b'
  have hB'K : B' ∈ (ModelData.sp F).K4 := by
    refine ((ModelData.sp F).diagGL_mem_K4_iff).2 ⟨?_, mem_U2_sp.2 hb', ?_⟩
    · exact mem_U2_sp.2 (by simp)
    · simp [hb']
  have hBeq : B = Matrix.GeneralLinearGroup.scalar (Fin 4) c * B' := by
    rw [hBb, scalar4_eq]
    show diagGL (sc2 c) b = diagGL (sc2 c) (sc2 c) * diagGL 1 (sc2 c⁻¹ * b)
    rw [diagGL_mul, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨mkP (ModelData.sp F) ⟨B', hB'K⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨hg, h1⟩ := hrep g
  have h1' : β (mkP (ModelData.sp F) g) = mkP (ModelData.sp F) ⟨B * (g : GL (Fin 4) F) * B⁻¹, by
      simpa only [hgl] using hg⟩ := by
    rw [h1]
    congr 1
    apply Subtype.ext
    show B * glAut σ (g : GL (Fin 4) F) * B⁻¹ = B * (g : GL (Fin 4) F) * B⁻¹
    rw [hgl]
  show β (mkP (ModelData.sp F) g) = (MulAut.conj (mkP (ModelData.sp F) ⟨B', hB'K⟩))
    (mkP (ModelData.sp F) g)
  rw [h1', MulAut.conj_apply, ← map_inv (mkP (ModelData.sp F)), ← map_mul (mkP (ModelData.sp F)),
    ← map_mul (mkP (ModelData.sp F))]
  congr 1
  apply Subtype.ext
  show B * (g : GL (Fin 4) F) * B⁻¹ = B' * (g : GL (Fin 4) F) * B'⁻¹
  have hcen := Subgroup.mem_center_iff.1 (scalar_mem_center (F := F) c)
  rw [hBeq, _root_.mul_inv_rev]
  calc Matrix.GeneralLinearGroup.scalar (Fin 4) c * B' * (g : GL (Fin 4) F) *
        (B'⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹)
      = Matrix.GeneralLinearGroup.scalar (Fin 4) c * (B' * (g : GL (Fin 4) F) * B'⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by group
    _ = B' * (g : GL (Fin 4) F) * B'⁻¹ := by
        rw [← hcen (B' * (g : GL (Fin 4) F) * B'⁻¹)]
        group

end CFSG.GH74.Ivk413
