module

public import CFSG.LargeExtraspecial.PSL10Levi
public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open Matrix
open scoped MatrixGroups

variable {n : ℕ}

theorem isTransvection_of_eq_one_add_vecMulVec {t : SL(n, ZMod 2)} (ht1 : t ≠ 1)
    {w ψ : Fin n → ZMod 2} (hψw : ψ ⬝ᵥ w = 0)
    (h : (t : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + vecMulVec w ψ) :
    CFSG.CGT.Timmesfeld75.IsTransvection t := by
  have hfw : dotProductEquiv (ZMod 2) (Fin n) ψ w = 0 := by
    rw [dotProductEquiv_apply_apply, hψw]
  refine ⟨ht1, dotProductEquiv (ZMod 2) (Fin n) ψ, w, hfw, LinearEquiv.ext fun x => ?_⟩
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, h, add_mulVec, one_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, LinearEquiv.transvection.apply, dotProductEquiv_apply_apply]

theorem single_one_eq_vecMulVec {k : ℕ} (i j : Fin k) :
    single i j (1 : ZMod 2) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  ext a b
  rw [single_apply, vecMulVec_apply, Pi.single_apply, Pi.single_apply]
  rcases eq_or_ne a i with rfl | ha <;> rcases eq_or_ne b j with rfl | hb <;>
    simp [*, Ne.symm]

theorem coe_tZero_eq_one_add_vecMulVec {m : ℕ} :
    ((tZero m : SL(m + 1 + 1, ZMod 2)) : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) =
      1 + vecMulVec (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) := by
  rw [tZero, DW.coe_cornerTransvection, single_one_eq_vecMulVec]
  rfl

theorem isTransvection_tZero {m : ℕ} :
    CFSG.CGT.Timmesfeld75.IsTransvection (tZero m : SL(m + 1 + 1, ZMod 2)) := by
  have h0l : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
  refine isTransvection_of_eq_one_add_vecMulVec ?_ (by simp)
    coe_tZero_eq_one_add_vecMulVec
  intro h
  have h1 : ((tZero m : SL(m + 1 + 1, ZMod 2)) :
      Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) 0 (Fin.last (m + 1)) =
      (1 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) (ZMod 2)) 0 (Fin.last (m + 1)) := by
    rw [h]
    rfl
  rw [coe_tZero_eq_one_add_vecMulVec, Matrix.add_apply, vecMulVec_apply, Pi.single_eq_same,
    Pi.single_eq_same, one_apply_ne h0l] at h1
  simp at h1

theorem pslpsu10Input_psl (X : Type*) [Group X] (hX : Nonempty (X ≃* PSL(10, ZMod 2))) (t : X)
    (ht : orderOf t = 2) : Conclusion X t := by
  intro hext
  set e₀ : X ≃* SL(10, ZMod 2) := hX.some.trans (DW.slEquivPSL 10).symm
  have ht' : orderOf (e₀ t) = 2 := by rwa [MulEquiv.orderOf_eq]
  have htt : e₀ t * e₀ t = 1 := by
    have h := pow_orderOf_eq_one (e₀ t)
    rwa [ht', sq] at h
  have ht1 : e₀ t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hext' := timmesfeldIsExtraspecial_fstar_map e₀ t hext
  obtain ⟨w, ψ, -, -, hψw, hT⟩ := exists_eq_one_add_vecMulVec htt ht1 hext'.1 hext'.2.2.2
  obtain ⟨W, hW⟩ := CFSG.CGT.Timmesfeld75.exists_conj_of_isTransvection
    (isTransvection_of_eq_one_add_vecMulVec ht1 hψw hT)
    (isTransvection_tZero (m := 8) : CFSG.CGT.Timmesfeld75.IsTransvection (tZero 8))
  have het : (e₀.trans (MulAut.conj W)) t = tZero 8 := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
    exact hW
  have h0 : Conclusion (SL(10, ZMod 2)) (tZero 8) := conclusion_tZero
  exact Conclusion.of_mulEquiv (e₀.trans (MulAut.conj W)) (het ▸ h0) hext

end CFSG.LargeExtraspecial.S14.PSLPSU10
