module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalar

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix

universe u

theorem pglGraphFieldAut_ne_one (n : ℕ) (K : Type u) [Field K]
    (hn : 2 ≤ n) (sigma : K ≃+* K) : pglGraphFieldAut n K sigma ≠ 1 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 at hval
    omega
  let t : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hij 1
  let g : GL (Fin n) K := SpecialLinearGroup.toGL t
  have hg : g.val = 1 + Matrix.single i j 1 := SpecialLinearGroup.transvection_coe hij 1
  have hginv : (g⁻¹).val = 1 + Matrix.single i j (-1) := by
    change ((SpecialLinearGroup.toGL t)⁻¹).val = _
    rw [← map_inv, SpecialLinearGroup.transvection_inv]
    exact SpecialLinearGroup.transvection_coe hij (-1)
  have hleft : (glGraphFieldAut n K sigma g).val i j = 0 := by
    rw [glGraphFieldAut_matrix, hginv]
    simp [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.add_apply, hij, hij.symm]
  have hright : g.val i j = 1 := by
    rw [hg]
    simp [Matrix.add_apply, hij]
  intro hidentity
  have hfixed := DFunLike.congr_fun hidentity (ProjGenLinGroup.mk g)
  change pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk g at hfixed
  rw [pglGraphFieldAut_mk, ProjGenLinGroup.mk_eq_mk_iff] at hfixed
  obtain ⟨c, hc⟩ := hfixed
  have hentry := congrArg (fun M : GL (Fin n) K => M i j) hc
  have hzero : (0 : K) = 1 := by
    simpa only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_diagonal, hleft, hright, zero_mul] using hentry
  exact zero_ne_one hzero

theorem scalarPGLGraphFieldAut_ne_one (n : ℕ) (K : Type u) [Field K]
    (hn : 2 ≤ n) (sigma : K ≃+* K) : scalarPGLGraphFieldAut n K sigma ≠ 1 := by
  intro h
  have h' := congrArg (MulAut.congr (scalarProjectiveGeneralLinearEquiv n K)) h
  rw [scalarPGLGraphFieldAut_congr, map_one] at h'
  exact pglGraphFieldAut_ne_one n K hn sigma h'

end

end CFSG.ComponentClassification.CatalogueBGraphField
