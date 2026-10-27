module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK1
public import CFSG.Sporadic.Schreier.ONInvolution

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.F3.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier


@[expose] def wordJ (w : List ℤ) : J :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 7 => gJ h.val) (ptoLetters 7 w)

theorem toMat_wordRows {w : List ℤ} (hw : ValidW 7 w) :
    toMat 154 (wordRows sRows sIRows w) = mat (wordJ w) :=
  (wordRows_spec rowsFor_strong w hw).2.2

theorem phiV_wordJ (w : List ℤ) : phiV (wordJ w) = evalS w := by
  rw [wordJ, map_evalWord]
  simp only [phiV_gJ]
  rfl

theorem jEquivPv_wordJ (w : List ℤ) : jEquivPv (wordJ w) = ⟨evalS w, evalS_mem w⟩ :=
  Subtype.ext (by rw [jEquivPv_apply, phiV_wordJ])

theorem n0_facts :
    n0Rows.size = 154 ∧ RowsWF n0Rows ∧ n0InvRows.size = 154 ∧ RowsWF n0InvRows ∧
      toMat 154 n0Rows * toMat 154 n0InvRows = 1 := by
  have h := n0_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨size_of_okRows h1, rowsWF_of_okRows h1, size_of_okRows h2, rowsWF_of_okRows h2, ?_⟩
  have e := toMat_eq_of_eqM h3
  rwa [toMat_mul' (size_of_okRows h1) (rowsWF_of_okRows h1) (rowsWF_of_okRows h2),
    toMat_idM] at e

@[expose, irreducible] def n0GL : GL (Fin 154) (ZMod 3) :=
  ⟨toMat 154 n0Rows, toMat 154 n0InvRows, n0_facts.2.2.2.2,
    ONSchreier.mul_eq_one_symm n0_facts.2.2.2.2⟩

theorem n0GL_val :
    ((n0GL : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) = toMat 154 n0Rows := by
  unfold n0GL
  rfl

theorem n0GL_inv_val :
    ((n0GL⁻¹ : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) =
      toMat 154 n0InvRows := by
  unfold n0GL
  rfl

theorem toMat_conj {X : Array V} (hX : RowsWF X) :
    toMat 154 (mul 154 (mul 154 n0Rows X) n0InvRows) =
      toMat 154 n0Rows * toMat 154 X * toMat 154 n0InvRows := by
  obtain ⟨h1, h2, -, h4, -⟩ := n0_facts
  rw [toMat_mul' (by rw [size_mul, h1]) (RowsWF.mul _ 154 h2 hX) h4, toMat_mul' h1 h2 hX]

theorem conj_gA :
    n0GL * gA * n0GL⁻¹ = (wordJ wA : GL (Fin 154) (ZMod 3)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, n0GL_val, n0GL_inv_val]
  have e := toMat_eq_of_eqM conjA_check
  rw [toMat_conj rowsWF_rowsA, toMat_rowsA, toMat_wordRows (validW_of_validB (by decide +kernel))]
    at e
  exact e

theorem conj_gB :
    n0GL * gB * n0GL⁻¹ = (wordJ wB : GL (Fin 154) (ZMod 3)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, n0GL_val, n0GL_inv_val]
  have e := toMat_eq_of_eqM conjB_check
  rw [toMat_conj rowsWF_rowsB, toMat_rowsB, toMat_wordRows (validW_of_validB (by decide +kernel))]
    at e
  exact e


theorem map_J :
    J.map (MulAut.conj n0GL).toMonoidHom = J := by
  have hle : J.map (MulAut.conj n0GL).toMonoidHom ≤ J := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · show n0GL * gA * n0GL⁻¹ ∈ J
      rw [conj_gA]
      exact (wordJ wA).2
    · show n0GL * gB * n0GL⁻¹ ∈ J
      rw [conj_gB]
      exact (wordJ wB).2
  have : Finite (GL (Fin 154) (ZMod 3)) := Finite.of_injective _ Units.val_injective
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (f := (MulAut.conj n0GL).toMonoidHom)
      (MulAut.conj n0GL).injective).ge

@[expose] def sigmaJ : MulAut J :=
  ((MulAut.conj n0GL).subgroupMap J).trans (MulEquiv.subgroupCongr map_J)

theorem sigmaJ_coe (g : J) :
    ((sigmaJ g : J) : GL (Fin 154) (ZMod 3)) = n0GL * g * n0GL⁻¹ :=
  rfl

theorem mat_sigmaJ (g : J) :
    mat (sigmaJ g) = toMat 154 n0Rows * mat g * toMat 154 n0InvRows := by
  rw [mat, sigmaJ_coe, Units.val_mul, Units.val_mul, n0GL_val, n0GL_inv_val]

theorem sigmaJ_ga : sigmaJ ga = wordJ wA :=
  Subtype.ext conj_gA

theorem sigmaJ_gb : sigmaJ gb = wordJ wB :=
  Subtype.ext conj_gB

theorem n0sq_comm (g : J) :
    n0GL * n0GL * (g : GL (Fin 154) (ZMod 3)) = g * (n0GL * n0GL) := by
  obtain ⟨h1, h2, -, -, -⟩ := n0_facts
  have hsq : ((n0GL : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) *
      ((n0GL : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) =
      toMat 154 n0SqRows := by
    rw [n0GL_val, n0SqRows, toMat_mul' h1 h2 h2]
  have hsqw : RowsWF n0SqRows := RowsWF.mul _ 154 h2 h2
  have hsqs : n0SqRows.size = 154 := by rw [n0SqRows, size_mul, h1]
  have hc := sq_check
  simp only [Bool.and_eq_true] at hc
  have hle : J ≤ Subgroup.centralizer {n0GL * n0GL} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      have e := toMat_eq_of_eqM hc.1
      rw [toMat_mul' hsqs hsqw rowsWF_rowsA, toMat_mul' rowsA_size' rowsWF_rowsA hsqw,
        toMat_rowsA] at e
      have hgA : ((gA : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) = mA :=
        mat_ga
      simp only [Units.val_mul, hsq, hgA]
      exact e.symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      have e := toMat_eq_of_eqM hc.2
      rw [toMat_mul' hsqs hsqw rowsWF_rowsB, toMat_mul' rowsB_size' rowsWF_rowsB hsqw,
        toMat_rowsB] at e
      have hgB : ((gB : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3)) = mB :=
        mat_gb
      simp only [Units.val_mul, hsq, hgB]
      exact e.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)).symm

theorem sigmaJ_sq : sigmaJ * sigmaJ = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.one_apply, sigmaJ_coe, sigmaJ_coe]
  calc n0GL * (n0GL * ↑g * n0GL⁻¹) * n0GL⁻¹ = n0GL * n0GL * ↑g * (n0GL * n0GL)⁻¹ := by group
    _ = ↑g * (n0GL * n0GL) * (n0GL * n0GL)⁻¹ := by rw [n0sq_comm]
    _ = ↑g := by group

@[expose] def zJ : J := wordJ CFSG.ONSchreier.Data.zWord

theorem sigmaJ_zJ : sigmaJ zJ = zJ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := n0_facts
  have hzv : ValidW 7 CFSG.ONSchreier.Data.zWord := validW_of_validB (by decide +kernel)
  obtain ⟨z1, z2, z3⟩ := wordRows_spec rowsFor_strong _ hzv
  have e := toMat_eq_of_eqM z_check
  change toMat 154 (mul 154 n0Rows (wordRows sRows sIRows CFSG.ONSchreier.Data.zWord)) =
    toMat 154 (mul 154 (wordRows sRows sIRows CFSG.ONSchreier.Data.zWord) n0Rows) at e
  rw [toMat_mul' h1 h2 z2, toMat_mul' z1 z2 h2] at e
  have z3' : toMat 154 (wordRows sRows sIRows CFSG.ONSchreier.Data.zWord) =
      mat (wordJ CFSG.ONSchreier.Data.zWord) := z3
  apply mat_injective
  change mat (sigmaJ (wordJ CFSG.ONSchreier.Data.zWord)) = mat (wordJ CFSG.ONSchreier.Data.zWord)
  rw [mat_sigmaJ, ← z3', e, mul_assoc, h5, mul_one]

@[expose] def sigmaPv : MulAut Pv :=
  jEquivPv.symm.trans (sigmaJ.trans jEquivPv)

theorem sigmaPv_apply (x : Pv) :
    sigmaPv x = jEquivPv (sigmaJ (jEquivPv.symm x)) := rfl

theorem sigmaPv_sq : sigmaPv * sigmaPv = 1 := by
  ext x
  rw [MulAut.mul_apply, sigmaPv_apply, sigmaPv_apply, MulEquiv.symm_apply_apply,
    ← MulAut.mul_apply, sigmaJ_sq, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]

theorem jEquivPv_symm_a0 : jEquivPv.symm ⟨a0, a0_mem⟩ = ga := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [jEquivPv_apply, phiV_ga])

theorem jEquivPv_symm_a1 : jEquivPv.symm ⟨a1, a1_mem⟩ = gb := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [jEquivPv_apply, phiV_gb])

theorem sigmaPv_a0 :
    sigmaPv ⟨a0, a0_mem⟩ = ⟨evalS wA, evalS_mem wA⟩ := by
  rw [sigmaPv_apply, jEquivPv_symm_a0, sigmaJ_ga, jEquivPv_wordJ]

theorem sigmaPv_a1 :
    sigmaPv ⟨a1, a1_mem⟩ = ⟨evalS wB, evalS_mem wB⟩ := by
  rw [sigmaPv_apply, jEquivPv_symm_a1, sigmaJ_gb, jEquivPv_wordJ]

theorem jEquivPv_zJ : jEquivPv zJ = zP := by
  rw [zJ, jEquivPv_wordJ]
  rfl

theorem sigmaPv_zP : sigmaPv zP = zP := by
  rw [sigmaPv_apply, ← jEquivPv_zJ, MulEquiv.symm_apply_apply, sigmaJ_zJ]

end CFSG.ComponentClassification.SolMax.ONOut
