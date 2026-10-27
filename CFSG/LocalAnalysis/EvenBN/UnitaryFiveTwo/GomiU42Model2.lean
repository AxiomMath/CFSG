module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KNine
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSUJ
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Open CFSG.Fischer CFSG.EvenSmallLie.UnitarySix
  CFSG.EvenSmallLie.UnitarySix.YamadaInputs SL44
open scoped MatrixGroups

theorem stabHom_surjective : Function.Surjective stabHom := by
  intro z
  set Z : Matrix (Fin 4) (Fin 4) F4 := (z.1 : Matrix (Fin 4) (Fin 4) F4)
  have hz : (Z.map bar)ᵀ * (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) * Z =
      (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) := mem_slUnitary.1 z.2
  have h1 : ((extMat Z).map bar)ᵀ * J5 * extMat Z = J5 := by
    rw [extMat_map_bar, extMat_transpose, J5_eq_extMat, ← extMat_mul, ← extMat_mul, hz]
  have h2 : (extMat Z).det = 1 := by
    rw [det_extMat]
    exact z.1.2
  refine ⟨⟨mkSU (extMat Z) h1 h2, ?_⟩, ?_⟩
  · rw [mem_StabSub, mat_mkSU, subMat_extMat]
  · apply Subtype.ext
    apply Subtype.ext
    change subMat (extMat Z) = Z
    exact subMat_extMat Z

@[expose] def Qm : Matrix (Fin 4) (Fin 4) F4 :=
  YamadaPar.f4m [[1, 0, 0, 2], [0, 1, 2, 0], [1, 0, 0, 3], [0, 1, 3, 0]]

@[expose] def Qim : Matrix (Fin 4) (Fin 4) F4 :=
  YamadaPar.f4m [[3, 0, 2, 0], [0, 3, 0, 2], [0, 1, 0, 1], [1, 0, 1, 0]]

theorem Qm_mul_Qim : Qm * Qim = 1 := YamadaPar.f4mat_ext (by decide)

theorem Qim_mul_Qm : Qim * Qm = 1 := YamadaPar.f4mat_ext (by decide)

theorem Qm_form : (Qm.map YamadaPar.frobF4)ᵀ * Qm = (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) := by
  ext i j
  rw [revGL_apply]
  revert i j
  decide

theorem bar_eq_frobF4 : (bar : F4 →+* F4) = YamadaPar.frobF4 :=
  RingHom.ext fun x => by rw [bar_apply, YamadaPar.frobF4_apply, sq]

@[expose] def Qunit : GL (Fin 4) F4 := ⟨Qm, Qim, Qm_mul_Qim, Qim_mul_Qm⟩

@[expose] noncomputable def conjQ : Matrix.SpecialLinearGroup (Fin 4) F4 →* GL (Fin 4) F4 where
  toFun g := Qunit * Matrix.SpecialLinearGroup.toGL g * Qunit⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem conjQ_val (g : Matrix.SpecialLinearGroup (Fin 4) F4) :
    ((conjQ g : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      Qm * (g : Matrix (Fin 4) (Fin 4) F4) * Qim := rfl

theorem conjQ_injective : Function.Injective conjQ := fun g h e => by
  have e2 : Qunit * Matrix.SpecialLinearGroup.toGL g * Qunit⁻¹ =
      Qunit * Matrix.SpecialLinearGroup.toGL h * Qunit⁻¹ := e
  exact Subtype.ext (congrArg Units.val (mul_left_cancel (mul_right_cancel e2)))

theorem conj_det_eq_one (g : Matrix.SpecialLinearGroup (Fin 4) F4) :
    ((conjQ g : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4).det = 1 := by
  rw [conjQ_val, Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul, Qm_mul_Qim,
    Matrix.det_one]

theorem conj_unitary_of_witt {Q Qi g R : Matrix (Fin 4) (Fin 4) F4} (hQQi : Q * Qi = 1)
    (hQ : (Q.map YamadaPar.frobF4)ᵀ * Q = R) (hg : (g.map YamadaPar.frobF4)ᵀ * R * g = R) :
    ((Q * g * Qi).map YamadaPar.frobF4)ᵀ * (Q * g * Qi) = 1 := by
  have hQQi' : Q.map YamadaPar.frobF4 * Qi.map YamadaPar.frobF4 = 1 := by
    rw [← Matrix.map_mul, hQQi, Matrix.map_one _ (map_zero YamadaPar.frobF4)
      (map_one YamadaPar.frobF4)]
  have e : ((Q * g * Qi).map YamadaPar.frobF4)ᵀ * (Q * g * Qi) =
      (Qi.map YamadaPar.frobF4)ᵀ * ((g.map YamadaPar.frobF4)ᵀ *
        ((Q.map YamadaPar.frobF4)ᵀ * Q) * g) * Qi := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e, hQ, hg, ← hQ]
  calc (Qi.map YamadaPar.frobF4)ᵀ * ((Q.map YamadaPar.frobF4)ᵀ * Q) * Qi
      = ((Q.map YamadaPar.frobF4) * Qi.map YamadaPar.frobF4)ᵀ * (Q * Qi) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQQi', hQQi, Matrix.transpose_one, Matrix.one_mul]

theorem conjQ_mem {g : Matrix.SpecialLinearGroup (Fin 4) F4}
    (hg : g ∈ slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4)) :
    conjQ g ∈ StatedSU 4 (2 ^ 1) F4 := by
  have hg' : ((g : Matrix (Fin 4) (Fin 4) F4).map YamadaPar.frobF4)ᵀ *
      (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) * (g : Matrix (Fin 4) (Fin 4) F4) =
        (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) := by
    have h := mem_slUnitary.1 hg
    rwa [bar_eq_frobF4] at h
  refine Subgroup.subset_closure ⟨conj_det_eq_one g, ?_⟩
  change (((conjQ g : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4).map (· ^ (2 ^ 1)))ᵀ *
    ((conjQ g : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1
  rw [conjQ_val, YamadaPar.pow_two_one_eq_frobF4]
  exact conj_unitary_of_witt Qm_mul_Qim Qm_form hg'

@[expose] noncomputable def psiHom :
    slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) →*
      StatedSU 4 (2 ^ 1) F4 where
  toFun g := ⟨conjQ g.1, conjQ_mem g.2⟩
  map_one' := Subtype.ext (map_one conjQ)
  map_mul' g h := Subtype.ext (map_mul conjQ g.1 h.1)

theorem psiHom_injective : Function.Injective psiHom := fun g h e => by
  have e' : conjQ g.1 = conjQ h.1 := congrArg Subtype.val e
  exact Subtype.ext (conjQ_injective e')

theorem psiHom_bijective : Function.Bijective psiHom := by
  have hF : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have hdom : Nat.card (slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4)) =
      25920 := card_slUnitary_four (F := F4) hF bar_apply
  have hcod : Nat.card (StatedSU 4 (2 ^ 1) F4) = 25920 := YamadaPar.card_statedSU_SU42
  haveI : Finite (StatedSU 4 (2 ^ 1) F4) :=
    Nat.finite_of_card_ne_zero (by rw [hcod]; norm_num)
  exact psiHom_injective.bijective_of_nat_card_le (le_of_eq (by rw [hcod, hdom]))

noncomputable def stabEquiv : StabSub ≃* StatedSU 4 (2 ^ 1) F4 :=
  (MulEquiv.ofBijective stabHom ⟨stabHom_injective, stabHom_surjective⟩).trans
    (MulEquiv.ofBijective psiHom psiHom_bijective)

theorem lieModel_StabSub : CFSG.Blueprint.LieModel StabSub .PSU 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F4, inferInstance,
    inferInstance, by rw [YamadaPar.card_F4]; norm_num,
    ⟨stabEquiv.trans YamadaPar.statedSUEquivProj⟩⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
