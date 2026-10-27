module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

import CFSG.LargeExtraspecial.BridgeForms
import CFSG.LargeExtraspecial.S10Conj
import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUComp
import CFSG.RankThree.Literature.FSmithOrthogonal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

noncomputable section

private abbrev ModelSpace : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2

private abbrev modelForm : QuadraticForm (ZMod 2) ModelSpace :=
  CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1

private theorem ncard_modelForm : {v : ModelSpace | modelForm v = 1}.ncard = 36 := by
  have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadMinus 2
  have h' : 2 * ({v : ModelSpace | modelForm v = 1}.ncard) = 72 := by
    simpa using h
  omega

private theorem finrank_modelSpace : Module.finrank (ZMod 2) ModelSpace = 6 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_sum, Fintype.card_fin]

private theorem natCard_modelSpace : Nat.card ModelSpace = 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ModelSpace),
    Nat.card_zmod, finrank_modelSpace]
  norm_num

private theorem nondegenerate_modelForm : modelForm.polarBilin.Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (ZMod 2)
    (by decide)

theorem nonempty_omegaGroup_equiv_statedOmega_minus (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (h6 : Module.finrank (ZMod 2) W = 6)
    (h36 : {v | Q v = 1}.ncard = 36) :
    Nonempty (↥(omegaGroup Q hQ) ≃* ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))) := by
  have hsep : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0 :=
    (CFSG.LargeExtraspecial.Bridge.polarBilin_nondegenerate_iff Q).mp hQ
  have hsep' : ∀ x, (∀ y, QuadraticMap.polar modelForm x y = 0) → x = 0 :=
    (CFSG.LargeExtraspecial.Bridge.polarBilin_nondegenerate_iff modelForm).mp
      nondegenerate_modelForm
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card W = Nat.card ModelSpace := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, h6,
      natCard_modelSpace]
    norm_num
  obtain ⟨L, hL⟩ : ∃ L : W ≃ₗ[ZMod 2] ModelSpace, ∀ v, modelForm (L v) = Q v :=
    CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq Q modelForm
      hsep hsep' hcard (h36.trans ncard_modelForm.symm)
  have hmap : (omegaGroup Q hQ).map (LinearEquiv.autCongr L).toMonoidHom =
      omegaGroup modelForm nondegenerate_modelForm := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (CFSG.LargeExtraspecial.S10.mem_omegaGroup_iff_autCongr' (κ := L) hL hQ
        nondegenerate_modelForm e).mp he
    · intro hg
      refine ⟨(LinearEquiv.autCongr L).symm g, ?_, by simp⟩
      rw [CFSG.LargeExtraspecial.S10.mem_omegaGroup_iff_autCongr' (κ := L) hL hQ
        nondegenerate_modelForm]
      simpa using hg
  let eΩ : ↥(omegaGroup Q hQ) ≃* ↥(omegaGroup modelForm nondegenerate_modelForm) :=
    (MulEquiv.subgroupMap (LinearEquiv.autCongr L) (omegaGroup Q hQ)).trans
      (MulEquiv.subgroupCongr hmap)
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup modelForm,
      TauCeti.QuadraticMap.orthogonalGroup modelForm⁆ = elementaryGroup modelForm :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (K := ZMod 2) (b := 1) (c := 1) (n := 3) (by norm_num) (by decide)
  have hΩE : omegaGroup modelForm nondegenerate_modelForm = elementaryGroup modelForm :=
    (CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup
      nondegenerate_modelForm (by rw [finrank_modelSpace])).symm.trans hE
  let eE : ↥(omegaGroup modelForm nondegenerate_modelForm) ≃* ↥(elementaryGroup modelForm) :=
    MulEquiv.subgroupCongr hΩE
  let eS : ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) ≃* ↥(elementaryGroup modelForm) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaMinusEquiv (K := ZMod 2) (b := 1) (c := 1)
      (m := 3) (by norm_num) (by decide)
  exact ⟨eΩ.trans (eE.trans eS.symm)⟩

theorem omegaGroup_minus_six_facts (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (h6 : Module.finrank (ZMod 2) W = 6)
    (h36 : {v | Q v = 1}.ncard = 36) :
    IsSimpleGroup ↥(omegaGroup Q hQ) ∧ Subgroup.center ↥(omegaGroup Q hQ) = ⊥ ∧
      catalogIs ↥(omegaGroup Q hQ) S9.isU4two := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hsmall :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := ZMod 2) (n := 3) (Or.inr rfl) (b := 1) (c := 1) hirr
  have hsimpleS : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := hsmall.1
  have hnaS : ¬ ∀ x y : ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)),
      x * y = y * x := hsmall.2.2
  obtain ⟨e⟩ := nonempty_omegaGroup_equiv_statedOmega_minus Q hQ h6 h36
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := hsimpleS
  have hsimpleΩ : IsSimpleGroup ↥(omegaGroup Q hQ) := e.isSimpleGroup
  have hnaΩ : ¬ ∀ x y : ↥(omegaGroup Q hQ), x * y = y * x := fun h =>
    hnaS fun x y => by
      have := congrArg e (h (e.symm x) (e.symm y))
      simpa using this
  have hcenΩ : Subgroup.center ↥(omegaGroup Q hQ) = ⊥ := by
    haveI : IsSimpleGroup ↥(omegaGroup Q hQ) := hsimpleΩ
    exact (CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_of_isSimpleGroup
      hnaΩ).2
  obtain ⟨E, hfield, hdata, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      (K := ZMod 2) (m := 1) (b := 1) (c := 1) (by simp) hirr
  haveI : Finite E := hdata.finite
  have hEcard : Nat.card E = 4 := by
    rw [hdata.card_eq_sq]
    norm_num
  haveI : Fintype E := Fintype.ofFinite E
  have hEfintype : Fintype.card E = 4 := by
    rw [← Nat.card_eq_fintype_card, hEcard]
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.statedProj_equiv_statedSU_four
    hEfintype
  let eAll : ↥(omegaGroup Q hQ) ≃* ↥(StatedSU 4 2 E) :=
    e.trans eSU
  have hcatE : catalogIs ↥(StatedSU 4 2 E) S9.isU4two :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj
      (X := ↥(StatedSU 4 2 E)) (K := E) hEcard eP.symm
  obtain ⟨i, hi, ⟨f⟩⟩ := hcatE
  exact ⟨hsimpleΩ, hcenΩ, ⟨i, hi, ⟨eAll.trans f⟩⟩⟩

theorem catalogIs_u4two_of_isComponentOf_of_equiv {G : Type} [Group G] {H K : Subgroup G}
    (Q : QuadraticForm (ZMod 2) W) (hQ : Q.polarBilin.Nondegenerate)
    (h6 : Module.finrank (ZMod 2) W = 6) (h36 : {v | Q v = 1}.ncard = 36)
    (e : ↥H ≃* ↥(omegaGroup Q hQ)) (hK : CFSG.Open.IsComponentOf K H) :
    catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two := by
  obtain ⟨hsimple, hcen, hcat⟩ := omegaGroup_minus_six_facts Q hQ h6 h36
  haveI : IsSimpleGroup ↥(omegaGroup Q hQ) := hsimple
  haveI : IsSimpleGroup ↥H := e.isSimpleGroup
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hK.2.1 inferInstance with
    hbot | htop
  · exfalso
    have hq := hK.2.2
    rw [hbot] at hq
    have hss : Subsingleton (↥(⊥ : Subgroup G) ⧸
        Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    haveI := hq.2
    exact not_subsingleton _ hss
  · have hKiso : ↥K ≃* ↥(omegaGroup Q hQ) :=
      (MulEquiv.subgroupCongr htop).trans e
    let eQ : ↥K ⧸ Subgroup.center ↥K ≃*
        ↥(omegaGroup Q hQ) ⧸ Subgroup.center ↥(omegaGroup Q hQ) :=
      QuotientGroup.congr _ _ hKiso (Subgroup.map_center_eq hKiso)
    let e0 : ↥(omegaGroup Q hQ) ⧸ Subgroup.center ↥(omegaGroup Q hQ) ≃*
        ↥(omegaGroup Q hQ) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    exact ⟨i, hi, ⟨(eQ.trans e0).trans f⟩⟩

end

end CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

end
