module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LPoints
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

theorem lead_smul {t : ZMod 3} (ht : t ≠ 0) (v : V) : lead (t • v) = t * lead v := by
  simp only [lead, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, ht, false_or]
  split_ifs <;> rfl

theorem sq_eq_one {t : ZMod 3} (ht : t ≠ 0) : t * t = 1 := by
  revert t
  decide

theorem normalize_smul {t : ZMod 3} (ht : t ≠ 0) (v : V) : normalize (t • v) = normalize v := by
  rw [normalize, normalize, lead_smul ht, smul_smul, mul_comm t, mul_assoc, sq_eq_one ht, mul_one]

theorem ptIndex_smul {t : ZMod 3} (ht : t ≠ 0) (v : V) : ptIndex (t • v) = ptIndex v := by
  rw [ptIndex, ptIndex, normalize_smul ht]

theorem rawIndex_lt (v : V) : rawIndex v < 40 := by
  have := ZMod.val_lt (v 1)
  have := ZMod.val_lt (v 2)
  have := ZMod.val_lt (v 3)
  unfold rawIndex
  split_ifs <;> omega

theorem ptIndex_lt (v : V) : ptIndex v < 40 := rawIndex_lt _

theorem decode_ne_zero (i : ℕ) : decode i ≠ 0 := by
  intro h
  unfold decode at h
  split_ifs at h
  · exact one_ne_zero (congrFun h 0)
  · exact one_ne_zero (congrFun h 1)
  · exact one_ne_zero (congrFun h 2)
  · exact one_ne_zero (congrFun h 3)

theorem decode_ptIndex_eq : ∀ w : V, w ≠ 0 → decode (ptIndex w) = lead w • w := by
  decide +kernel

theorem lead_ne_zero : ∀ w : V, w ≠ 0 → lead w ≠ 0 := by
  decide +kernel

theorem decode_ptIndex {w : V} (hw : w ≠ 0) : ∃ c : ZMod 3, c ≠ 0 ∧ decode (ptIndex w) = c • w :=
  ⟨lead w, lead_ne_zero w hw, decode_ptIndex_eq w hw⟩

theorem mulVec_ne_zero (A : GL (Fin 4) (ZMod 3)) {w : V} (hw : w ≠ 0) :
    Matrix.mulVec (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) w ≠ 0 := by
  intro h
  apply hw
  have h1 := congrArg
    (Matrix.mulVec ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3))) h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h1

@[expose] def ptMap (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (i : Fin 40) : Fin 40 :=
  ⟨ptIndex (Matrix.mulVec A (decode i)), ptIndex_lt _⟩

theorem ptMap_mul (A B : GL (Fin 4) (ZMod 3)) (i : Fin 40) :
    ptMap A (ptMap B i) =
      ptMap ((A * B : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) i := by
  obtain ⟨c, hc, hdec⟩ := decode_ptIndex (mulVec_ne_zero B (decode_ne_zero i))
  apply Fin.ext
  simp only [ptMap]
  rw [hdec, Matrix.mulVec_smul, ptIndex_smul hc, Matrix.mulVec_mulVec, Units.val_mul]

theorem ptMap_one (i : Fin 40) : ptMap 1 i = i := by
  apply Fin.ext
  simp only [ptMap, Matrix.one_mulVec]
  exact ptIndex_decode i

@[expose] def ptPerm (A : GL (Fin 4) (ZMod 3)) : Equiv.Perm (Fin 40) where
  toFun := ptMap A
  invFun := ptMap ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3))
  left_inv i := by
    rw [ptMap_mul, inv_mul_cancel, Units.val_one, ptMap_one]
  right_inv i := by
    rw [ptMap_mul, mul_inv_cancel, Units.val_one, ptMap_one]

@[expose] def rho : GL (Fin 4) (ZMod 3) →* Equiv.Perm (Fin 40) where
  toFun := ptPerm
  map_one' := by
    ext i
    exact congrArg Fin.val (ptMap_one i)
  map_mul' A B := by
    ext i
    exact congrArg Fin.val (ptMap_mul A B i).symm

theorem rho_apply (A : GL (Fin 4) (ZMod 3)) (i : Fin 40) :
    (rho A i : ℕ) = ptIndex (Matrix.mulVec (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (decode i)) :=
  rfl

@[expose] noncomputable def perm80 : GL (Fin 4) (ZMod 3) →* Equiv.Perm (Fin 80) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp ((Equiv.Perm.sumCongrHom _ _).comp
    (rho.prod (rho.comp Matrix.GeneralLinearGroup.inverseTranspose.toMonoidHom)))

@[expose] noncomputable def swap80 : Equiv.Perm (Fin 80) :=
  Equiv.permCongr finSumFinEquiv (Equiv.sumComm (Fin 40) (Fin 40))

theorem perm80_apply (A : GL (Fin 4) (ZMod 3)) (i : Fin 80) :
    perm80 A i = finSumFinEquiv (Equiv.Perm.sumCongr (rho A)
      (rho (Matrix.GeneralLinearGroup.inverseTranspose A)) (finSumFinEquiv.symm i)) := rfl

theorem swap80_apply (i : Fin 80) :
    swap80 i = finSumFinEquiv (Equiv.sumComm (Fin 40) (Fin 40) (finSumFinEquiv.symm i)) := rfl

theorem swap80_mul_self : swap80 * swap80 = 1 := by
  ext i
  simp only [Equiv.Perm.mul_apply, swap80_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply,
    Sum.swap_swap, Equiv.apply_symm_apply, Equiv.Perm.one_apply]

theorem swap80_inv : swap80⁻¹ = swap80 :=
  inv_eq_of_mul_eq_one_right swap80_mul_self

theorem swap80_conj (A : GL (Fin 4) (ZMod 3)) :
    swap80 * perm80 A * swap80⁻¹ = perm80 (Matrix.GeneralLinearGroup.inverseTranspose A) := by
  rw [swap80_inv]
  ext i
  simp only [Equiv.Perm.mul_apply, swap80_apply, perm80_apply, Equiv.symm_apply_apply,
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  rcases (finSumFinEquiv (m := 40) (n := 40)).symm i with p | p <;> rfl

theorem perm80_scalar (c : (ZMod 3)ˣ) :
    perm80 (Matrix.GeneralLinearGroup.scalar (Fin 4) c) = 1 := by
  have hρ : ∀ d : (ZMod 3)ˣ, rho (Matrix.GeneralLinearGroup.scalar (Fin 4) d) = 1 := by
    intro d
    ext i
    rw [rho_apply, Equiv.Perm.one_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, ptIndex_smul d.ne_zero, ptIndex_decode]
  have hit : Matrix.GeneralLinearGroup.inverseTranspose
      (Matrix.GeneralLinearGroup.scalar (Fin 4) c) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) c⁻¹ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_transpose]
  ext i
  rw [perm80_apply, hρ, hit, hρ, Equiv.Perm.sumCongr_one, Equiv.Perm.one_apply,
    Equiv.apply_symm_apply, Equiv.Perm.one_apply]

theorem perm80_apply_lt (A : GL (Fin 4) (ZMod 3)) (i : Fin 80) (hi : i.val < 40) :
    (perm80 A i : ℕ) =
      ptIndex (Matrix.mulVec (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (decode i)) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 40, i = Fin.castAdd 40 j := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  rw [perm80_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.val_castAdd, rho_apply, Fin.val_castAdd]

theorem perm80_apply_ge (A : GL (Fin 4) (ZMod 3)) (i : Fin 80) (hi : 40 ≤ i.val) :
    (perm80 A i : ℕ) = 40 + ptIndex (Matrix.mulVec
      ((Matrix.GeneralLinearGroup.inverseTranspose A : GL (Fin 4) (ZMod 3)) :
        Matrix (Fin 4) (Fin 4) (ZMod 3)) (decode (i.val - 40))) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 40, i = Fin.natAdd 40 j :=
    ⟨⟨i.val - 40, by omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩
  rw [perm80_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.val_natAdd, rho_apply, Fin.val_natAdd,
    Nat.add_sub_cancel_left]

theorem swap80_apply_lt (i : Fin 80) (hi : i.val < 40) : (swap80 i : ℕ) = i.val + 40 := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 40, i = Fin.castAdd 40 j := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  rw [swap80_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumComm_apply, Sum.swap_inl,
    finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.val_castAdd, add_comm]

theorem swap80_apply_ge (i : Fin 80) (hi : 40 ≤ i.val) : (swap80 i : ℕ) = i.val - 40 := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 40, i = Fin.natAdd 40 j :=
    ⟨⟨i.val - 40, by omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩
  rw [swap80_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply, Sum.swap_inr,
    finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.val_natAdd, Nat.add_sub_cancel_left]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def perm80SL :
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 3) →* Equiv.Perm (Fin 80) :=
  perm80.comp Matrix.SpecialLinearGroup.toGL

theorem scalars_le_ker : scalars 4 (ZMod 3) ≤ perm80SL.ker := by
  rintro A ⟨c, -, hA⟩
  rw [MonoidHom.mem_ker, perm80SL, MonoidHom.comp_apply]
  have h1 : Matrix.SpecialLinearGroup.toGL A = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA, Matrix.GeneralLinearGroup.coe_scalar]
  rw [h1, perm80_scalar]

@[expose] noncomputable def pi : projectiveSL 4 (ZMod 3) →* Equiv.Perm (Fin 80) :=
  QuotientGroup.lift _ perm80SL scalars_le_ker

theorem pi_proj (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    pi (proj 4 (ZMod 3) g) = perm80 (Matrix.SpecialLinearGroup.toGL g) := rfl

theorem perm80_conj_pi (A : GL (Fin 4) (ZMod 3)) (g : projectiveSL 4 (ZMod 3)) :
    perm80 A * pi g * (perm80 A)⁻¹ = pi (conjAut 4 (ZMod 3) A g) := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 3) g
  rw [conjAut_proj, pi_proj, pi_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation]

theorem swap80_conj_pi (g : projectiveSL 4 (ZMod 3)) :
    swap80 * pi g * swap80⁻¹ = pi (dualAut 4 (ZMod 3) g) := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 3) g
  have h1 : Matrix.SpecialLinearGroup.toGL ((g⁻¹).transpose) =
      Matrix.GeneralLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.toGL g) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_transpose]
  rw [dualAut_proj, pi_proj, pi_proj, swap80_conj, h1]

end CFSG.ComponentClassification.HarrisLit.P1.L43
