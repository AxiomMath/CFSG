module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParUType
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank

@[expose] noncomputable def fixSigma : Subgroup SL4 := MonoidHom.eqLocus sigmaSL (MonoidHom.id SL4)

theorem mem_fixSigma {g : SL4} : g ∈ fixSigma ↔ sigmaSL g = g := Iff.rfl

@[expose] def Cm : Matrix (Fin 4) (Fin 4) F4 :=
  f4m [[1, 0, 2, 0], [0, 1, 0, 2], [1, 0, 3, 0], [0, 1, 0, 3]]

@[expose] def CmInv : Matrix (Fin 4) (Fin 4) F4 :=
  f4m [[3, 0, 2, 0], [0, 3, 0, 2], [1, 0, 1, 0], [0, 1, 0, 1]]

theorem Cm_mul_CmInv : Cm * CmInv = 1 := f4mat_ext (by decide)

theorem CmInv_mul_Cm : CmInv * Cm = 1 := f4mat_ext (by decide)

theorem Cm_form : (Cm.map frobF4)ᵀ * Cm = Jm := f4mat_ext (by decide)

theorem det_Cm_mul_det_CmInv : Cm.det * CmInv.det = 1 := by
  rw [← det_mul, Cm_mul_CmInv, det_one]

theorem unitary_of_mem_fixSigma {g : SL4} (hg : g ∈ fixSigma) :
    ((g : Matrix (Fin 4) (Fin 4) F4).map frobF4)ᵀ * Jm * (g : Matrix (Fin 4) (Fin 4) F4) = Jm := by
  have hσ : sigmaM g = g := congrArg Subtype.val (mem_fixSigma.mp hg)
  set X := ((((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4))ᵀ).map frobF4
  set Y := ((g : Matrix (Fin 4) (Fin 4) F4).map frobF4)ᵀ
  have hYX : Y * X = 1 := by
    rw [show Y = (((g : Matrix (Fin 4) (Fin 4) F4))ᵀ).map frobF4 from Matrix.transpose_map.symm,
      ← Matrix.map_mul, ← transpose_mul, ← coe_SL4_mul, inv_mul_cancel, coe_SL4_one, transpose_one,
      Matrix.map_one _ (map_zero frobF4) (map_one frobF4)]
  have hX : X = Jm * (g : Matrix (Fin 4) (Fin 4) F4) * Jm := by
    rw [← hσ, sigmaM]
    calc X = (Jm * Jm) * X * (Jm * Jm) := by rw [Jm_mul_Jm, Matrix.one_mul, Matrix.mul_one]
      _ = Jm * (Jm * X * Jm) * Jm := by simp only [Matrix.mul_assoc]
  calc Y * Jm * (g : Matrix (Fin 4) (Fin 4) F4)
      = Y * (Jm * (g : Matrix (Fin 4) (Fin 4) F4) * Jm) * Jm := by
        rw [Matrix.mul_assoc Y, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]
    _ = Jm := by rw [← hX, hYX, Matrix.one_mul]

theorem pow_two_one_eq_frobF4 : (fun x : F4 => x ^ (2 ^ 1)) = ⇑frobF4 := by
  funext x; rw [pow_one, sq]; rfl

theorem conj_unitary {g : Matrix (Fin 4) (Fin 4) F4} (hg : (g.map frobF4)ᵀ * Jm * g = Jm) :
    ((Cm * g * CmInv).map frobF4)ᵀ * (Cm * g * CmInv) = 1 := by
  rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
  calc (CmInv.map frobF4)ᵀ * ((g.map frobF4)ᵀ * (Cm.map frobF4)ᵀ) * (Cm * g * CmInv)
      = (CmInv.map frobF4)ᵀ * ((g.map frobF4)ᵀ * ((Cm.map frobF4)ᵀ * Cm) * g) * CmInv := by
        simp only [Matrix.mul_assoc]
    _ = (CmInv.map frobF4)ᵀ * ((Cm.map frobF4)ᵀ * Cm) * CmInv := by
        rw [Cm_form, hg, ← Cm_form]
    _ = (((Cm * CmInv).map frobF4))ᵀ := by
        rw [Matrix.map_mul, transpose_mul]; simp only [Matrix.mul_assoc]
        rw [Cm_mul_CmInv, Matrix.mul_one]
    _ = 1 := by
        rw [Cm_mul_CmInv, Matrix.map_one _ (map_zero frobF4) (map_one frobF4), transpose_one]

theorem conj_det (g : SL4) : (Cm * (g : Matrix (Fin 4) (Fin 4) F4) * CmInv).det = 1 := by
  rw [det_mul, det_mul, det_SL4, mul_one, det_Cm_mul_det_CmInv]

@[expose] noncomputable def conjUnit (g : SL4) : GL (Fin 4) F4 :=
  ⟨Cm * g * CmInv, Cm * ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv, by
    calc Cm * (g : Matrix (Fin 4) (Fin 4) F4) * CmInv *
          (Cm * ((g⁻¹ : SL4) : Matrix _ _ F4) * CmInv)
        = Cm * ((g * g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv := by
          rw [coe_SL4_mul]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc CmInv Cm, CmInv_mul_Cm, Matrix.one_mul]
      _ = 1 := by rw [mul_inv_cancel, coe_SL4_one, Matrix.mul_one, Cm_mul_CmInv], by
    calc Cm * ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv *
          (Cm * (g : Matrix _ _ F4) * CmInv)
        = Cm * ((g⁻¹ * g : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv := by
          rw [coe_SL4_mul]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc CmInv Cm, CmInv_mul_Cm, Matrix.one_mul]
      _ = 1 := by rw [inv_mul_cancel, coe_SL4_one, Matrix.mul_one, Cm_mul_CmInv]⟩

theorem conjUnit_mem {g : SL4} (hg : g ∈ fixSigma) : conjUnit g ∈ StatedSU 4 (2 ^ 1) F4 := by
  refine Subgroup.subset_closure ⟨conj_det g, ?_⟩
  change ((Cm * (g : Matrix (Fin 4) (Fin 4) F4) * CmInv).map (· ^ (2 ^ 1)))ᵀ *
    (Cm * (g : Matrix (Fin 4) (Fin 4) F4) * CmInv) = 1
  rw [pow_two_one_eq_frobF4]
  exact conj_unitary (unitary_of_mem_fixSigma hg)

@[expose] noncomputable def toStatedSU : fixSigma →* StatedSU 4 (2 ^ 1) F4 where
  toFun g := ⟨conjUnit g, conjUnit_mem g.2⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change Cm * ((1 : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv = 1
    rw [coe_SL4_one, Matrix.mul_one, Cm_mul_CmInv]
  map_mul' g h := by
    apply Subtype.ext; apply Units.ext
    change Cm * (((g * h : fixSigma) : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv =
      (Cm * ((g : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv) *
        (Cm * ((h : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv)
    rw [Subgroup.coe_mul, coe_SL4_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc CmInv Cm, CmInv_mul_Cm, Matrix.one_mul]

theorem toStatedSU_injective : Function.Injective toStatedSU := by
  intro g h hgh
  have h1 : Cm * ((g : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv =
      Cm * ((h : SL4) : Matrix (Fin 4) (Fin 4) F4) * CmInv := by
    have := congrArg (fun x : StatedSU 4 (2 ^ 1) F4 =>
      (((x : GL (Fin 4) F4)) : Matrix (Fin 4) (Fin 4) F4)) hgh
    exact this
  have h2 := congrArg (fun X => CmInv * X * Cm) h1
  simp only [← Matrix.mul_assoc, CmInv_mul_Cm, Matrix.one_mul] at h2
  simp only [Matrix.mul_assoc, CmInv_mul_Cm, Matrix.mul_one] at h2
  exact Subtype.ext (Subtype.ext h2)

theorem card_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card]; rfl

theorem det_eq_one_of_mem_statedSU {A : GL (Fin 4) F4} (hA : A ∈ StatedSU 4 (2 ^ 1) F4) :
    (A : Matrix (Fin 4) (Fin 4) F4).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem f4_pow_four (c : F4) : c ^ 4 = c := f4_ext (by revert c; decide)

theorem scalars_statedSU_eq_bot :
    (StatedScalars (Fin 4) F4).subgroupOf (StatedSU 4 (2 ^ 1) F4) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨A, hA⟩ hs
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨c, hc⟩ := hs
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin 4) c = A := hc
  have hdet := det_eq_one_of_mem_statedSU hA
  rw [← hc', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, f4_pow_four] at hdet
  have hc1 : c = 1 := Units.ext hdet
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change A = 1
  rw [← hc', hc1, map_one]

theorem card_statedProj_SU42 : Nat.card (StatedProj (StatedSU 4 (2 ^ 1) F4)) = 25920 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
    (by rw [card_F4]; norm_num) (by norm_num)]
  decide

@[expose] noncomputable def statedSUEquivProj :
    StatedSU 4 (2 ^ 1) F4 ≃* StatedProj (StatedSU 4 (2 ^ 1) F4) :=
  (QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq scalars_statedSU_eq_bot.symm)

theorem card_statedSU_SU42 : Nat.card (StatedSU 4 (2 ^ 1) F4) = 25920 := by
  rw [Nat.card_congr statedSUEquivProj.toEquiv, card_statedProj_SU42]

theorem card_fixSigma_le : Nat.card fixSigma ≤ 25920 := by
  rw [← card_statedSU_SU42]
  exact Nat.card_le_card_of_injective _ toStatedSU_injective

@[expose] noncomputable def reHom : SL4 →* GL (Fin 8) (ZMod 2) where
  toFun g := ⟨reF4 g, reF4 ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4), by
    rw [← map_mul, ← coe_SL4_mul, mul_inv_cancel, coe_SL4_one, map_one], by
    rw [← map_mul, ← coe_SL4_mul, inv_mul_cancel, coe_SL4_one, map_one]⟩
  map_one' := Units.ext (by
    change reF4 ((1 : SL4) : Matrix (Fin 4) (Fin 4) F4) = 1
    rw [coe_SL4_one, map_one])
  map_mul' g h := Units.ext (by
    change reF4 ((g * h : SL4) : Matrix (Fin 4) (Fin 4) F4) = _
    rw [coe_SL4_mul, map_mul]; rfl)

theorem coe_reHom (g : SL4) :
    ((reHom g : GL (Fin 8) (ZMod 2)) : Mat8) = reF4 (g : Matrix (Fin 4) (Fin 4) F4) := rfl

theorem reHom_injective : Function.Injective reHom := fun _g _h hgh =>
  Subtype.ext (reF4_injective (congrArg Units.val hgh))

section Gen


noncomputable abbrev genSL (s : Fin 3) : SL4 := trProdSL (lKW s)

theorem lineM_one_eq_zero : lineM 1 = lineM 0 := rfl

theorem lineInvM_one_eq_zero : lineInvM 1 = lineInvM 0 := rfl

theorem genSL_spec (s : Fin 3) :
    reF4 ((genSL s : SL4) : Matrix (Fin 4) (Fin 4) F4) = genMat s ∧ sigmaSL (genSL s) = genSL s := by
  have h1 := rhoL_lKW (z := 1) (Or.inl rfl) s
  have h2 := rhoMHom_genSU_eq (z := 0) (Or.inl rfl) s
  have hd : diagSU (genSU s) = (genSU s, genSU s) := rfl
  rw [hd, rhoU_apply] at h2
  simp only [rhoMHom, MonoidHom.coe_mk, OneHom.coe_mk, genSU, coe_genGL] at h2
  rw [h2, rhoL_apply, lineM_one_eq_zero, lineInvM_one_eq_zero] at h1
  have h3 := congrArg (fun X => lineInvM 0 * X * lineM 0) h1
  simp only [← Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.one_mul] at h3
  simp only [Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.mul_one] at h3
  have ha := bdiag_injective_left h3
  have hb := bdiag_injective_right h3
  refine ⟨ha, Subtype.ext (reF4_injective ?_)⟩
  rw [hb, ha]

theorem reHom_genSL (s : Fin 3) : reHom (genSL s) = genGL s :=
  Units.ext (by rw [coe_reHom, (genSL_spec s).1, coe_genGL])

noncomputable def genSLGroup : Subgroup SL4 := Subgroup.closure {genSL 0, genSL 1}

theorem genSLGroup_le_fixSigma : genSLGroup ≤ fixSigma := by
  rw [genSLGroup, Subgroup.closure_le]
  rintro g (rfl | rfl)
  exacts [(genSL_spec 0).2, (genSL_spec 1).2]

theorem map_genSLGroup : genSLGroup.map reHom = SU42b := by
  rw [genSLGroup, MonoidHom.map_closure, SU42b]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, (rfl | rfl), rfl⟩
    exacts [Or.inl (reHom_genSL 0), Or.inr (reHom_genSL 1)]
  · rintro (rfl | rfl)
    exacts [⟨_, Or.inl rfl, reHom_genSL 0⟩, ⟨_, Or.inr rfl, reHom_genSL 1⟩]

@[expose] noncomputable def genSLEquiv : genSLGroup ≃* SU42b :=
  (genSLGroup.equivMapOfInjective reHom reHom_injective).trans
    (MulEquiv.subgroupCongr map_genSLGroup)

theorem coe_genSLEquiv (g : genSLGroup) :
    ((genSLEquiv g : SU42b) : GL (Fin 8) (ZMod 2)) = reHom g := rfl

theorem genSLGroup_eq_fixSigma : genSLGroup = fixSigma := by
  refine Subgroup.eq_of_le_of_card_ge genSLGroup_le_fixSigma ?_
  rw [Nat.card_congr genSLEquiv.toEquiv, card_SU42b]
  exact card_fixSigma_le

end Gen

section Lie


theorem card_fixSigma : Nat.card fixSigma = 25920 := by
  rw [← genSLGroup_eq_fixSigma, Nat.card_congr genSLEquiv.toEquiv, card_SU42b]

theorem toStatedSU_bijective : Function.Bijective toStatedSU := by
  have : Finite (StatedSU 4 (2 ^ 1) F4) := Nat.finite_of_card_ne_zero (by
    rw [card_statedSU_SU42]; norm_num)
  exact toStatedSU_injective.bijective_of_nat_card_le (by rw [card_fixSigma, card_statedSU_SU42])

noncomputable def SU42bEquivFix : SU42b ≃* fixSigma :=
  genSLEquiv.symm.trans (MulEquiv.subgroupCongr genSLGroup_eq_fixSigma)

noncomputable def SU42bEquivStated : SU42b ≃* StatedProj (StatedSU 4 (2 ^ 1) F4) :=
  (SU42bEquivFix.trans (MulEquiv.ofBijective toStatedSU toStatedSU_bijective)).trans
    statedSUEquivProj

theorem lieModel_SU42b : CFSG.Blueprint.LieModel SU42b .PSU 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F4, inferInstance,
    inferInstance, by rw [card_F4]; norm_num, ⟨SU42bEquivStated⟩⟩

end Lie

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
