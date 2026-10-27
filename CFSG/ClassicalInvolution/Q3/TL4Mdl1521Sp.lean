module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Sig
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.RankThree.PartOne.KC.SymplecticSemi

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.E1521

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def spIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 2] ![1, 3]
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

abbrev spMat (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindex spIdx spIdx M

theorem spMat_mul (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    spMat (M * N) = spMat M * spMat N := by
  simp only [spMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

omit [Field F] in
theorem spMat_injective : Function.Injective (spMat (F := F)) :=
  (Matrix.reindex spIdx spIdx).injective

theorem spMat_smul (c : F) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    spMat (c • M) = c • spMat M := by
  ext i j
  rfl

theorem spMat_one : spMat (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
  simp only [spMat, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

omit [Field F] in
theorem spMat_transpose (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    spMat Mᵀ = (spMat M)ᵀ := by
  simp only [spMat, Matrix.transpose_reindex]

theorem trace_spMat (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    (spMat M).trace = M.trace := by
  simp only [spMat, Matrix.reindex_apply, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp spIdx.symm (fun i => M i i)

theorem spMat_formJ : spMat (formJ 2 F) = blkJ 1 0 1 (-1) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spMat, spIdx, formJ]

theorem spMat_longBlock (X : SL(2, F)) :
    spMat (mat 2 F (longBlock F 2 0 X)) =
      !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
        (X : Matrix (Fin 2) (Fin 2) F) 1 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0;
        0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [mat_longBlock]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spMat, spIdx, CFSG.LieType.Steinberg.Sp.blockMat]

theorem spMat_longBlock_qI : spMat (mat 2 F (longBlock F 2 0 (qI F))) = mI F := by
  rw [spMat_longBlock]
  simp [qI]

theorem spMat_longBlock_qJ (h3 : (3 : F) = 0) :
    spMat (mat 2 F (longBlock F 2 0 (qJ h3))) = mJ F := by
  rw [spMat_longBlock]
  simp [qJ]

@[expose] noncomputable def blockQ0Sp (F : Type) [Field F] :
    Subgroup (StatedProj (StatedSp 2 F)) :=
  (commutator SL(2, F)).map ((proj 2 F).comp (longBlock F 2 0))

theorem mem_blockQ0Sp {c : SL(2, F)} (hc : c ∈ commutator SL(2, F)) :
    proj 2 F (longBlock F 2 0 c) ∈ blockQ0Sp F :=
  Subgroup.mem_map_of_mem _ hc

theorem sp_comm_of_fix (A : gsp 2 F) {r : StatedSp 2 F}
    (hr : conjAut 2 F A (proj 2 F r) = proj 2 F r) (htr : (mat 2 F r).trace ≠ 0) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mat 2 F r =
      mat 2 F r * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [conjAut_proj] at hr
  have h1 : (conjSp 2 F A r)⁻¹ * r ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hr, inv_mul_cancel]
  have h1' := Subgroup.mem_subgroupOf.mp h1
  rw [StatedScalars, MonoidHom.mem_range] at h1'
  obtain ⟨c, hc⟩ := h1'
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := ((A : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
  set Bm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ :
    GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hBm
  have hAB : Am * Bm = 1 := by rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrc : (r : GL (Fin 2 ⊕ Fin 2) F) =
      (A : GL (Fin 2 ⊕ Fin 2) F) * r * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ *
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSp]
    group
  have hm := congrArg (fun X : GL (Fin 2 ⊕ Fin 2) F =>
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hrc
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, ← hAm, ← hBm] at hm
  rw [← mat_apply] at hm
  have htrace := congrArg Matrix.trace hm
  rw [Matrix.trace_smul, Matrix.trace_mul_comm (Am * mat 2 F r), ← Matrix.mul_assoc, hBA,
    Matrix.one_mul, smul_eq_mul] at htrace
  have hc1 : (c : F) = 1 := by
    have h1 : (1 - (c : F)) * (mat 2 F r).trace = 0 := by linear_combination htrace
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right htr)).symm
  rw [hc1, one_smul] at hm
  calc Am * mat 2 F r = Am * mat 2 F r * (Bm * Am) := by rw [hBA, Matrix.mul_one]
    _ = mat 2 F r * Am := by rw [← Matrix.mul_assoc, ← hm]

theorem conjAut_statedSp (g : StatedSp 2 F) :
    conjAut 2 F ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩ = MulAut.conj (proj 2 F g) := by
  ext p
  obtain ⟨h, rfl⟩ := proj_surjective (r := 2) (K := F) p
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem sp_conjAut_proj_eq_of_comm (A : gsp 2 F) (g : StatedSp 2 F)
    (h : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mat 2 F g =
      mat 2 F g * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    conjAut 2 F A (proj 2 F g) = proj 2 F g := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  have h1 : (A : GL (Fin 2 ⊕ Fin 2) F) * g = g * (A : GL (Fin 2 ⊕ Fin 2) F) :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, ← mat_apply]; exact h)
  rw [coe_conjSp, h1, mul_inv_cancel_right]

theorem exists_blk_of_comm_sp [Finite F] (hF : Nat.card F = 3)
    {x : StatedProj (StatedSp 2 F)} (hx : ∀ y ∈ blockQ0Sp F, x * y = y * x) :
    ∃ g : StatedSp 2 F, proj 2 F g = x ∧ ∃ c p q r s : F, spMat (mat 2 F g) = blk c p q r s := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
  have key : ∀ c ∈ commutator SL(2, F),
      conjAut 2 F ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩
        (proj 2 F (longBlock F 2 0 c)) = proj 2 F (longBlock F 2 0 c) := fun c hc => by
    rw [conjAut_statedSp, MulAut.conj_apply, hx _ (mem_blockQ0Sp hc), mul_inv_cancel_right]
  have hI : mat 2 F g * mat 2 F (longBlock F 2 0 (qI F)) =
      mat 2 F (longBlock F 2 0 (qI F)) * mat 2 F g := sp_comm_of_fix _ (key _ (qI_mem hF))
    (by rw [← trace_spMat, spMat_longBlock_qI]; exact trace_mI h2)
  have hJ : mat 2 F g * mat 2 F (longBlock F 2 0 (qJ h3)) =
      mat 2 F (longBlock F 2 0 (qJ h3)) * mat 2 F g := sp_comm_of_fix _ (key _ (qJ_mem hF h3))
    (by rw [← trace_spMat, spMat_longBlock_qJ]; exact trace_mJ h2)
  have hI' := congrArg spMat hI
  have hJ' := congrArg spMat hJ
  rw [spMat_mul, spMat_mul, spMat_longBlock_qI] at hI'
  rw [spMat_mul, spMat_mul, spMat_longBlock_qJ] at hJ'
  exact ⟨g, rfl, _, _, _, _, _, eq_of_comm_IJ h2 hI' hJ'⟩

theorem sig_psp4_false [Finite F] (hF : Nat.card F = 3) (α : MulAut (StatedProj (StatedSp 2 F)))
    (hα2 : α * α = 1) (hfix : ∀ x ∈ blockQ0Sp F, α x = x)
    (hmov : ∃ x, (∀ y ∈ blockQ0Sp F, x * y = y * x) ∧ α x ≠ x) : False := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨A, σ, hαeq⟩ := ModelFacts.Orth15.OuterSp4.exists_conjAut_fieldAut_sp4 h2 α
  rw [card3_ringEquiv hF σ, show fieldAut 2 F (RingEquiv.refl F) = 1 from map_one _,
    mul_one] at hαeq
  subst hαeq
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := ((A : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
  have hI := sp_comm_of_fix A (hfix _ (mem_blockQ0Sp (qI_mem hF)))
    (by rw [← trace_spMat, spMat_longBlock_qI]; exact trace_mI h2)
  have hJ := sp_comm_of_fix A (hfix _ (mem_blockQ0Sp (qJ_mem hF h3)))
    (by rw [← trace_spMat, spMat_longBlock_qJ]; exact trace_mJ h2)
  have hI' := congrArg spMat hI
  have hJ' := congrArg spMat hJ
  rw [spMat_mul, spMat_mul, spMat_longBlock_qI] at hI'
  rw [spMat_mul, spMat_mul, spMat_longBlock_qJ] at hJ'
  obtain ⟨a, p, q, r, s, hA⟩ : ∃ a p q r s : F, spMat Am = blk a p q r s :=
    ⟨_, _, _, _, _, eq_of_comm_IJ h2 hI' hJ'⟩
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hμ' := congrArg spMat hμ
  rw [spMat_mul, spMat_mul, spMat_transpose, spMat_smul, spMat_formJ, ← hAm, hA] at hμ'
  have m01 := congrFun (congrFun hμ' 0) 1
  have m23 := congrFun (congrFun hμ' 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at m01 m23
  obtain ⟨c, hc⟩ := (RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (by norm_num) (A * A)).mp
    (by rw [map_mul]; exact hα2)
  have hAA : blk a p q r s * blk a p q r s = blk (c : F) c 0 0 c := by
    have h1 := congrArg (fun X : GL (Fin 2 ⊕ Fin 2) F =>
      spMat (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, spMat_mul, spMat_smul, spMat_one,
      ← hAm, hA] at h1
    rw [h1, smul_one_eq_blk]
  rw [blk_mul] at hAA
  obtain ⟨hc1, e00, e01, e10, e11⟩ := blk_inj hAA
  have ha : a ≠ 0 := by
    rintro rfl
    have := Units.ne_zero μ
    apply this
    linear_combination -m01
  have ha2 := card3_mul_self hF ha
  have hcc : (c : F) = 1 := by rw [← hc1, ha2]
  rw [hcc] at e00 e11
  have hns : q = 0 ∧ r = 0 ∧ p = s := by
    by_contra hns
    have hs := trace_eq_zero_of_inv e00 e01 e10 e11 hns
    rw [hs] at m23
    apply h2
    linear_combination -m23 + m01 - ha2 - e00
  obtain ⟨hq, hr, hps⟩ := hns
  obtain ⟨x, hxc, hxα⟩ := hmov
  obtain ⟨g, rfl, c₀, k00, k01, k10, k11, hg⟩ := exists_blk_of_comm_sp hF hxc
  apply hxα
  refine sp_conjAut_proj_eq_of_comm A g (spMat_injective ?_)
  rw [spMat_mul, spMat_mul, ← hAm, hA, hg, blk_mul, blk_mul, hq, hr, hps]
  exact blk_congr (by ring) (by ring) (by ring) (by ring) (by ring)

end CFSG.ClassicalInvolution.Q3.TL4.E1521
