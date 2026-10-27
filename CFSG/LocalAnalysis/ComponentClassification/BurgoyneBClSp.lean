module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieSBlocks
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCSpSkew

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv eigen_ne_bot)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.C (fixSubEquivOfProd leviDet)
open CFSG.ComponentClassification.CatLeafProof.EndOddSp (quatBlock_of_isometryEquiv
  quatBlock_leviSL)
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem fixOf_conjSp (A : gsp r K) : fixOf (conjSp r K A).toMonoidHom = spCent r K A := rfl

omit [Finite K] in
theorem conjAut_sp_lift (A : gsp r K) (g : StatedSp r K) :
    conjAut r K A (projH _ g) = projH _ ((conjSp r K A).toMonoidHom g) :=
  conjAut_proj A g

theorem noL2At_sp_split (hK : ringChar K ≠ 2) {Ag : gsp r K} {l : K} (hl0 : l ≠ 0)
    (hAA1 : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    (hAns : ∀ c : Kˣ, (Ag : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) :
    NoL2At (conjAut r K Ag) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hAA' := linA_mul_self hAA1
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA Ag :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨-, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv Ag).trans e with hΨ
  have hres : ∀ g : spCent r K Ag, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl Ag l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K Ag, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl Ag l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).1]
    simp only [spCentEquiv_apply]
  set N₁ := fixSub r K Ag (VMl Ag l) with hN₁
  set N₂ := fixSub r K Ag (VPl Ag l) with hN₂
  have hsplit : spCent r K Ag ≤ N₁ ⊔ N₂ := by
    intro g hg
    have h1 : (Ψ.symm ((Ψ ⟨g, hg⟩).1, 1) : StatedSp r K) ∈ N₁ :=
      ⟨(Ψ.symm ((Ψ ⟨g, hg⟩).1, 1)).2, (hres _).1 (by rw [MulEquiv.apply_symm_apply])⟩
    have h2' : (Ψ.symm (1, (Ψ ⟨g, hg⟩).2) : StatedSp r K) ∈ N₂ :=
      ⟨(Ψ.symm (1, (Ψ ⟨g, hg⟩).2)).2, (hres' _).1 (by
        change (Ψ (Ψ.symm (1, (Ψ ⟨g, hg⟩).2))).1 = 1
        rw [MulEquiv.apply_symm_apply])⟩
    have hgab : (⟨g, hg⟩ : spCent r K Ag) =
        Ψ.symm ((Ψ ⟨g, hg⟩).1, 1) * Ψ.symm (1, (Ψ ⟨g, hg⟩).2) := by
      apply Ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_one,
        one_mul]
    have := congrArg (fun u : spCent r K Ag => (u : StatedSp r K)) hgab
    simp only [Subgroup.coe_mul] at this
    rw [show g = _ from this]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h2')
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  have hW₁ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VMl Ag l,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VMl Ag l :=
    fun g hg v hv => mulVec_mem_VMl hl0 hg hv
  have hW₂ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VPl Ag l,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VPl Ag l :=
    fun g hg v hv => mulVec_mem_VPl hl0 hg hv
  have hinj : ∀ {W : Submodule K (Fin r ⊕ Fin r → K)}, W ≠ ⊥ →
      Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
        (StatedSp r K))).comp (fixSub r K Ag W).subtype) := by
    intro W hWne
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 hg
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hgv := g.2.2 v hv
    have hgm : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
      have e1 : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by rw [hc]; rfl
      rw [← e1, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hgm, smul_mulVec, one_mulVec] at hgv
    have hc1 : (c : K) = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext h)
      have := congrFun hgv i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have : ((c : K) - 1) * v i = 0 := by linear_combination this
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hi)
    apply Subtype.ext
    apply statedSp_ext
    rw [hgm, hc1, one_smul]
    rfl
  have hiso : ∀ {W : Submodule K (Fin r ⊕ Fin r → K)}, W ≠ ⊥ →
      (fixSub r K Ag W).map (QuotientGroup.mk' _) ≃* fixSub r K Ag W := fun hWne =>
    ((MonoidHom.ofInjective (hinj hWne)).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, range_subtype]))).symm
  have hB₁ : CatLeafProof.EndOddLin.QuatBlock (N₁.map (QuotientGroup.mk' _)) :=
    quatBlock_of_isometryEquiv hK haltP hndP
      (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP)
      (((hiso hMne).trans (fixSubEquivOfProd Ψ hres)).trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
  have hB₂ : CatLeafProof.EndOddLin.QuatBlock (N₂.map (QuotientGroup.mk' _)) :=
    quatBlock_of_isometryEquiv hK haltM hndM
      (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM)
      (((hiso hPne).trans (fixSubEquivOfProd (Ψ.trans MulEquiv.prodComm) hres')).trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
  exact noL2At_of_fix_blocks hZ (conjAut_sp_lift Ag) (fixSub_le Ag _) (fixSub_le Ag _)
    (fun B hB g hg => conj_mem_fixSub hW₁ hB hg) (fun B hB g hg => conj_mem_fixSub hW₂ hB hg)
    ((commutator_le_self' _).trans hsplit) hB₁ hB₂

theorem noL2At_stdSkew (hK : ringChar K ≠ 2) (hr : 3 ≤ r) :
    NoL2At (conjAut r K (stdSkewGsp r K)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  have hLF : (leviSL r K).range ≤ fixOf (conjSp r K (stdSkewGsp r K)).toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    exact leviSL_mem_spCent y
  have hcomm : ⁅fixOf (conjSp r K (stdSkewGsp r K)).toMonoidHom,
      fixOf (conjSp r K (stdSkewGsp r K)).toMonoidHom⁆ ≤ (leviSL r K).range := by
    rw [fixOf_conjSp, commutator_le]
    intro g hg h hh
    have hk := Abelianization.commutator_subset_ker (leviDet h2).toHomUnits
      (commutator_mem_commutator (mem_top (⟨g, hg⟩ : spCent r K (stdSkewGsp r K)))
        (mem_top (⟨h, hh⟩ : spCent r K (stdSkewGsp r K))))
    rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one] at hk
    obtain ⟨x, hx, -⟩ := eq_leviSL_of_blockDiag
      (fromBlocks_of_commute_stdSkew h2 (mem_spCent.1
        (⁅(⟨g, hg⟩ : spCent r K (stdSkewGsp r K)),
          (⟨h, hh⟩ : spCent r K (stdSkewGsp r K))⁆).2).symm) hk
    exact ⟨x, hx.symm⟩
  exact noL2At_of_fix_layer hZ (conjAut_sp_lift _) hLF hcomm (quatBlock_leviSL hK hr)

end CFSG.ComponentClassification.Burgoyne.Cl
