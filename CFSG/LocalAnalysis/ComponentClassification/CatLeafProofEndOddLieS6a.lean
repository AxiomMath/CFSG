module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCSpSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv eigen_ne_bot)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.CatLeafProof.EndOddCore CFSG.ComponentClassification.FooteLit

variable {r : ℕ} {K : Type} [Field K]

theorem false_of_config_block [Finite K] (hK : ringChar K ≠ 2) {A : StatedSp r K}
    {W W' : Submodule K (Fin r ⊕ Fin r → K)} (hW' : W' ≠ ⊥)
    (hinv : ∀ g ∈ spCent r K ⟨A, statedSp_le_gsp A.2⟩, ∀ v ∈ W',
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W')
    (hcent : centralizer ({A} : Set (StatedSp r K)) = spCent r K ⟨A, statedSp_le_gsp A.2⟩)
    {B : LinearMap.BilinForm K W} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (e : fixSub r K ⟨A, statedSp_le_gsp A.2⟩ W' ≃* CatalogueBAlternatingIsometry.isometryGroup B)
    (hq : IsQuasisimple (CatalogueBAlternatingIsometry.isometryGroup B))
    {L D : Subgroup (StatedProj (StatedSp r K))}
    (h : Config (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) A) L D) : False := by
  set Z := (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) with hZdef
  set Ag : gsp r K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  set N := fixSub r K Ag W' with hN
  have hZ : Z ≤ center (StatedSp r K) := scalars_subgroupOf_le_center
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have hinj : Function.Injective ((QuotientGroup.mk' Z).comp N.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 hg
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
    have hgv := g.2.2 v hv
    have hgm : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
      have e1 : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (((g : StatedSp r K) :
          GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by rw [hc]; rfl
      rw [← e1, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hgm, smul_mulVec, one_mulVec] at hgv
    have hc1 : (c : K) = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv0 (funext hcon)
      have h1 := congrFun hgv i
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      have h3 : ((c : K) - 1) * v i = 0 := by linear_combination h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hi)
    apply Subtype.ext
    apply statedSp_ext
    rw [hgm, hc1, one_smul]
    rfl
  set φ : N →* StatedProj (StatedSp r K) := (QuotientGroup.mk' Z).comp N.subtype with hφ
  have hrange : φ.range = N.map (QuotientGroup.mk' Z) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  set eN : N ≃* N.map (QuotientGroup.mk' Z) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange) with heN
  have hqN : IsQuasisimple (N.map (QuotientGroup.mk' Z)) :=
    LocalCores.isQuasisimple_of_mulEquiv (eN.symm.trans e).symm hq
  have hNT : N ≤ centralizer ({A} : Set (StatedSp r K)) := by
    rw [hcent]
    exact fixSub_le Ag W'
  have hnorm : ∀ c ∈ centralizer ({A} : Set (StatedSp r K)), ∀ f ∈ N, c * f * c⁻¹ ∈ N := by
    intro c hc f hf
    rw [hcent] at hc
    exact conj_mem_fixSub hinv hc hf
  obtain ⟨m, hm, ⟨e'⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  have hW0 : 0 < Module.finrank K W := by
    rcases Nat.eq_zero_or_pos (Module.finrank K W) with h0 | h0
    · exfalso
      have : Subsingleton W := Module.finrank_zero_iff.mp h0
      have : Subsingleton (CatalogueBAlternatingIsometry.isometryGroup B) := by
        constructor
        intro a b
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        exact Subsingleton.elim _ _
      exact (LocalCores.isQuasisimple_nontrivial hq).exists_pair_ne.elim
        fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
    · exact h0
  have hm1 : 0 < m := by omega
  set eS : N.map (QuotientGroup.mk' Z) ≃* StatedSp m K := ((eN.symm.trans e).trans e').trans
    (MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := K)).symm)
    with heS
  have hK2 : ringChar K ≠ 2 := hK
  have hquat : ∃ H : Subgroup (N.map (QuotientGroup.mk' Z)),
      Nonempty (H ≃* QuaternionGroup 2) := by
    obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_of_mulEquiv_SL hK2 (longRootEquiv K (⟨0, hm1⟩ : Fin m))
    let ι : longRoot K (⟨0, hm1⟩ : Fin m) →* N.map (QuotientGroup.mk' Z) :=
      eS.symm.toMonoidHom.comp (longRoot K (⟨0, hm1⟩ : Fin m)).subtype
    have hι : Function.Injective ι := eS.symm.injective.comp (Subgroup.subtype_injective _)
    exact ⟨H.map ι, ⟨(H.equivMapOfInjective ι hι).symm.trans eH⟩⟩
  have heven : Even (Nat.card (N.map (QuotientGroup.mk' Z))) := by
    obtain ⟨H, ⟨eH⟩⟩ := hquat
    have h8 : Nat.card H = 8 := by
      rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hdvd : Nat.card H ∣ Nat.card (N.map (QuotientGroup.mk' Z)) :=
      Subgroup.card_subgroup_dvd_card H
    rw [h8] at hdvd
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) hdvd)
  have hcomp := isTwoComponentAt_map_mk hZ h.twoComp.1 hNT hnorm hqN heven
  have hL := h.unique _ hcomp
  obtain ⟨H, ⟨eH⟩⟩ := hquat
  subst hL
  exact h.false_of_quat H eH

theorem false_of_config_split [Finite K] (hK : ringChar K ≠ 2) (hr : 3 ≤ r) {A : StatedSp r K}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {L D : Subgroup (StatedProj (StatedSp r K))}
    (h : Config (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) A) L D) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  set Ag : gsp r K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  have hl0 : (1 : K) ≠ 0 := one_ne_zero
  have hAA1 : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((1 : K) ^ 2) • 1 := by
    rw [one_pow, one_smul]
    exact hAA
  have hJ : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((1 : K) ^ 2) • formJ r K := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 A.2
  have hAA' := linA_mul_self hAA1
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp 1 ((linA Ag :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp 1 ((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
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
  have hres : ∀ g : spCent r K Ag, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl Ag 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K Ag, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl Ag 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).1]
    simp only [spCentEquiv_apply]
  have hcent : centralizer ({A} : Set (StatedSp r K)) = spCent r K Ag := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent]
    constructor
    · intro hg
      have := congrArg (fun u : StatedSp r K =>
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hg
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this.symm
    · intro hg
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      exact hg.symm
  have hW₁ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VMl Ag 1,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VMl Ag 1 :=
    fun g hg v hv => mulVec_mem_VMl hl0 hg hv
  have hW₂ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VPl Ag 1,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VPl Ag 1 :=
    fun g hg v hv => mulVec_mem_VPl hl0 hg hv
  by_cases hPx : Module.finrank K (VPl Ag 1) ≠ 2 ∨ Nat.card K ≠ 3
  · exact false_of_config_block hK hMne hW₁ hcent haltP hndP
      ((fixSubEquivOfProd Ψ hres).trans (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
      (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
        (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd hPx) h
  · push Not at hPx
    have hc := UnitaryHigher.isCompl_ker_sub_one_ker_add_one h2 (UnitaryHigher.invSMulOp_mul_self
      hl0 hAA')
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_standard] at hsum
    have hsum' : Module.finrank K (VPl Ag 1) + Module.finrank K (VMl Ag 1) = 2 * r := hsum
    have hMx : Module.finrank K (VMl Ag 1) ≠ 2 ∨ Nat.card K ≠ 3 := by
      left
      have : Module.finrank K (VPl Ag 1) = 2 := hPx.1
      omega
    exact false_of_config_block hK hPne hW₂ hcent haltM hndM
      ((fixSubEquivOfProd (Ψ.trans MulEquiv.prodComm) hres').trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
      (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltM hndM
        (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM) hodd hMx) h

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
