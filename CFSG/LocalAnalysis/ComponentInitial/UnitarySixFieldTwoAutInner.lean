module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutModel
public import CFSG.Monster.B.Classical.UnitarySixInvolutions

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary
open CFSG.Monster.B.Classical.UnitarySix (normalForm stdN stdSet rkOne isConj_normalForm
  invRank_le_three invRank_eq_one_or_two_or_three coe_invOf stdSet_one stdSet_two stdSet_three)

variable {F : Type} [Field F]

private def swapIdx : Fin 6 ≃ Fin 6 := Equiv.swap 3 5

private theorem swapIdx_swapIdx (a : Fin 6) : swapIdx (swapIdx a) = a :=
  Equiv.swap_apply_self _ _ _

section Transport

variable (φ : F4 ≃+* F)

private def toF (N : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F :=
  (N.map φ).submatrix swapIdx swapIdx

private def toF4 (M : Matrix (Fin 6) (Fin 6) F) : Matrix (Fin 6) (Fin 6) F4 :=
  (M.map φ.symm).submatrix swapIdx swapIdx

private theorem toF_apply (N : Matrix (Fin 6) (Fin 6) F4) (a b : Fin 6) :
    toF φ N a b = φ (N (swapIdx a) (swapIdx b)) :=
  rfl

private theorem toF4_apply (M : Matrix (Fin 6) (Fin 6) F) (a b : Fin 6) :
    toF4 φ M a b = φ.symm (M (swapIdx a) (swapIdx b)) :=
  rfl

private theorem toF_toF4 (M : Matrix (Fin 6) (Fin 6) F) : toF φ (toF4 φ M) = M := by
  ext a b
  rw [toF_apply, toF4_apply, swapIdx_swapIdx, swapIdx_swapIdx, RingEquiv.apply_symm_apply]

private theorem toF4_toF (N : Matrix (Fin 6) (Fin 6) F4) : toF4 φ (toF φ N) = N := by
  ext a b
  rw [toF4_apply, toF_apply, swapIdx_swapIdx, swapIdx_swapIdx, RingEquiv.symm_apply_apply]

private theorem toF_mul (N N' : Matrix (Fin 6) (Fin 6) F4) :
    toF φ (N * N') = toF φ N * toF φ N' := by
  rw [toF, toF, toF, Matrix.map_mul, submatrix_mul_equiv]

private theorem toF4_mul (M M' : Matrix (Fin 6) (Fin 6) F) :
    toF4 φ (M * M') = toF4 φ M * toF4 φ M' := by
  rw [toF4, toF4, toF4, Matrix.map_mul, submatrix_mul_equiv]

private theorem toF_one : toF φ (1 : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  rw [toF, Matrix.map_one _ (map_zero φ) (map_one φ), submatrix_one_equiv]

private theorem toF4_one : toF4 φ (1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
  rw [toF4, Matrix.map_one _ (map_zero φ.symm) (map_one φ.symm), submatrix_one_equiv]

private theorem toF_add (N N' : Matrix (Fin 6) (Fin 6) F4) :
    toF φ (N + N') = toF φ N + toF φ N' := by
  ext a b
  simp only [toF_apply, Matrix.add_apply, map_add]

private theorem det_toF (N : Matrix (Fin 6) (Fin 6) F4) : (toF φ N).det = φ N.det := by
  rw [toF, det_submatrix_equiv_self]
  exact (RingHom.map_det (φ : F4 →+* F) N).symm

private theorem det_toF4 (M : Matrix (Fin 6) (Fin 6) F) : (toF4 φ M).det = φ.symm M.det := by
  rw [toF4, det_submatrix_equiv_self]
  exact (RingHom.map_det (φ.symm : F →+* F4) M).symm

private theorem toF_transpose (N : Matrix (Fin 6) (Fin 6) F4) : toF φ Nᵀ = (toF φ N)ᵀ := by
  ext a b
  rfl

private theorem toF4_transpose (M : Matrix (Fin 6) (Fin 6) F) : toF4 φ Mᵀ = (toF4 φ M)ᵀ := by
  ext a b
  rfl

private theorem toF_map_frobenius (h : UnitaryFieldData 2 1 F) (N : Matrix (Fin 6) (Fin 6) F4) :
    toF φ (N.map frobeniusF4) = (toF φ N).map h.bar := by
  ext a b
  rw [toF_apply, map_apply, map_apply, toF_apply, frobeniusF4_apply, bar_eq_sq h, map_pow]

private theorem toF4_map_bar (h : UnitaryFieldData 2 1 F) (M : Matrix (Fin 6) (Fin 6) F) :
    toF4 φ (M.map h.bar) = (toF4 φ M).map frobeniusF4 := by
  ext a b
  rw [toF4_apply, map_apply, map_apply, toF4_apply, frobeniusF4_apply, bar_eq_sq h, map_pow]

private theorem toF_antidiag (h : UnitaryFieldData 2 1 F) :
    toF φ (antidiag 6) = (sixJ h : Matrix (Fin 6) (Fin 6) F) := by
  rw [coe_sixJ]
  ext a b
  rw [toF_apply]
  fin_cases a <;> fin_cases b <;>
    simp [antidiag, blockSwapJ, swapIdx, Equiv.swap_apply_def, Fin.rev]

private theorem toF4_sixJ (h : UnitaryFieldData 2 1 F) :
    toF4 φ (sixJ h : Matrix (Fin 6) (Fin 6) F) = antidiag 6 := by
  rw [← toF_antidiag φ h, toF4_toF]

private theorem toF_single (a b : Fin 6) :
    toF φ (single a b 1) = single (swapIdx a) (swapIdx b) 1 := by
  ext x y
  rw [toF_apply, single_apply, single_apply]
  have hx : a = swapIdx x ↔ swapIdx a = x := by
    constructor
    · rintro rfl
      exact swapIdx_swapIdx x
    · rintro rfl
      exact (swapIdx_swapIdx a).symm
  have hy : b = swapIdx y ↔ swapIdx b = y := by
    constructor
    · rintro rfl
      exact swapIdx_swapIdx y
    · rintro rfl
      exact (swapIdx_swapIdx b).symm
  split_ifs with h1 h2 h2
  · exact map_one φ
  · exact absurd ⟨hx.mp h1.1, hy.mp h1.2⟩ h2
  · exact absurd ⟨hx.mpr h2.1, hy.mpr h2.2⟩ h1
  · exact map_zero φ

private def toFHom : Matrix (Fin 6) (Fin 6) F4 →* Matrix (Fin 6) (Fin 6) F where
  toFun := toF φ
  map_one' := toF_one φ
  map_mul' := toF_mul φ

private def toF4Hom : Matrix (Fin 6) (Fin 6) F →* Matrix (Fin 6) (Fin 6) F4 where
  toFun := toF4 φ
  map_one' := toF4_one φ
  map_mul' := toF4_mul φ

private theorem toF_mem_sixS (h : UnitaryFieldData 2 1 F) {c : GL (Fin 6) F4}
    (hc : c ∈ SU frobeniusF4 6) : Units.map (toFHom φ) c ∈ sixS h := by
  obtain ⟨hdet, hiso⟩ := mem_SU.mp hc
  refine ⟨?_, ?_⟩
  · change ((toF φ (c : Matrix (Fin 6) (Fin 6) F4)).map h.bar)ᵀ *
      (sixJ h : Matrix (Fin 6) (Fin 6) F) * toF φ (c : Matrix (Fin 6) (Fin 6) F4) = sixJ h
    rw [← toF_map_frobenius φ h, ← toF_transpose, ← toF_antidiag φ h, ← toF_mul, ← toF_mul]
    exact congrArg (toF φ) hiso
  · change (toF φ (c : Matrix (Fin 6) (Fin 6) F4)).det = 1
    rw [det_toF, hdet, map_one]

private theorem toF4_mem_SU (h : UnitaryFieldData 2 1 F) {s : GL (Fin 6) F}
    (hs : s ∈ sixS h) : Units.map (toF4Hom φ) s ∈ SU frobeniusF4 6 := by
  refine mem_SU.mpr ⟨?_, ?_⟩
  · change (toF4 φ (s : Matrix (Fin 6) (Fin 6) F)).det = 1
    rw [det_toF4, hs.2, map_one]
  · change ((toF4 φ (s : Matrix (Fin 6) (Fin 6) F)).map frobeniusF4)ᵀ * antidiag 6 *
      toF4 φ (s : Matrix (Fin 6) (Fin 6) F) = antidiag 6
    rw [← toF4_map_bar φ h, ← toF4_transpose, ← toF4_sixJ φ h, ← toF4_mul, ← toF4_mul]
    exact congrArg (toF4 φ) hs.1

end Transport

private theorem rkOne_single (i : Fin 6) : rkOne (Pi.single i 1) = single i (Fin.rev i) 1 := by
  ext a b
  simp only [rkOne, vecMulVec_apply, Pi.single_apply, single_apply,
    CFSG.Monster.B.Classical.UnitarySix.bar]
  by_cases ha : a = i
  · subst ha
    by_cases hb : Fin.rev b = a
    · have hb' : Fin.rev a = b := by rw [← hb, Fin.rev_rev]
      simp [hb, hb']
    · have hb' : ¬Fin.rev a = b := fun h' => hb (by rw [← h', Fin.rev_rev])
      simp [hb, hb']
  · have ha' : ¬i = a := fun h' => ha h'.symm
    simp [ha, ha']

private theorem stdN_one : stdN 1 = single 0 5 1 := by
  rw [stdN, stdSet_one, Finset.sum_singleton, rkOne_single]
  rfl

private theorem stdN_two : stdN 2 = single 0 5 1 + single 1 4 1 := by
  rw [stdN, stdSet_two, Finset.sum_pair (by decide), rkOne_single, rkOne_single]
  rfl

private theorem stdN_three : stdN 3 = single 0 5 1 + single 1 4 1 + single 2 3 1 := by
  rw [stdN, stdSet_three, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    rkOne_single, rkOne_single, rkOne_single, add_assoc]
  rfl

private theorem nMat_dMat_two :
    nMat (dMat 2 : Matrix (Fin 3) (Fin 3) F) = 1 + single 0 3 1 + single 1 4 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nMat, dMat, reindex_apply, one_apply]

private theorem nMat_dMat_three :
    nMat (dMat 3 : Matrix (Fin 3) (Fin 3) F) =
      1 + single 0 3 1 + single 1 4 1 + single 2 5 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nMat, dMat, reindex_apply, one_apply]

private theorem toF_normalForm (φ : F4 ≃+* F) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    toF φ (1 + stdN k) = nMat (dMat k) := by
  rcases hk with rfl | rfl | rfl
  · rw [stdN_one, toF_add, toF_one, toF_single, nMat_dMat_one]
    rfl
  · rw [stdN_two, toF_add, toF_add, toF_one, toF_single, toF_single, nMat_dMat_two, add_assoc]
    rfl
  · rw [stdN_three, toF_add, toF_add, toF_add, toF_one, toF_single, toF_single, toF_single,
      nMat_dMat_three, add_assoc, add_assoc, add_assoc]
    rfl

theorem exists_conj_tElt_of_involution (h : UnitaryFieldData 2 1 F) (s : sixS h)
    (hs : s * s = 1) (hs1 : s ≠ 1) :
    ∃ (g : sixS h) (k : ℕ), (k = 1 ∨ k = 2 ∨ k = 3) ∧ g * tElt h k * g⁻¹ = s := by
  classical
  have := h.finite
  have := Fintype.ofFinite F
  obtain ⟨φ⟩ : Nonempty (F4 ≃+* F) := ⟨FiniteField.ringEquivOfCardEq (by
    rw [F4.card, ← Nat.card_eq_fintype_card, natCard_eq_four h])⟩
  set s' : SU frobeniusF4 6 := ⟨_, toF4_mem_SU φ h s.2⟩ with hs'
  have hmat : ∀ x : SU frobeniusF4 6, ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      toF4 φ ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) → x = s' := fun x hx =>
    Subtype.ext (Units.ext hx)
  have hs'2 : s' ^ 2 = 1 := by
    rw [pow_two]
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
    change toF4 φ ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      toF4 φ ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1
    rw [← toF4_mul, ← Units.val_mul, ← Subgroup.coe_mul, hs, Subgroup.coe_one, Units.val_one,
      toF4_one]
  have hs'1 : s' ≠ 1 := by
    intro h1
    refine hs1 (Subtype.ext (Units.ext ?_))
    have h2 := congrArg (fun x : SU frobeniusF4 6 =>
      toF φ ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) h1
    rw [show ((s' : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      toF4 φ ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) from rfl, toF_toF4] at h2
    rw [h2]
    exact toF_one φ
  have hk := invRank_le_three s' hs'2 hs'1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_normalForm s' hs'2 hs'1 hk)
  have hcmat : ((c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      (1 + stdN (CFSG.Monster.B.Classical.UnitarySix.invRank s')) *
        ((c⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) =
          toF4 φ ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    have := congrArg (fun x : SU frobeniusF4 6 =>
      ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) hc
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [normalForm, coe_invOf] at this
    exact this
  refine ⟨⟨_, toF_mem_sixS φ h c.2⟩, _, invRank_eq_one_or_two_or_three s' hs'2 hs'1, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_tElt,
    ← toF_normalForm φ (invRank_eq_one_or_two_or_three s' hs'2 hs'1)]
  have hinv : (((⟨_, toF_mem_sixS φ h c.2⟩ : sixS h)⁻¹ : sixS h) : GL (Fin 6) F) =
      Units.map (toFHom φ) ((c⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) := by
    rw [Subgroup.coe_inv, Subgroup.coe_inv, map_inv]
  rw [hinv]
  change toF φ ((c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      toF φ (1 + stdN (CFSG.Monster.B.Classical.UnitarySix.invRank s')) *
        toF φ (((c⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
  rw [← toF_mul, ← toF_mul, hcmat, toF_toF4]

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
