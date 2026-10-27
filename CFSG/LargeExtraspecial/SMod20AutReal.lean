module

public import CFSG.LargeExtraspecial.SMod20AutSemi
public import CFSG.LargeExtraspecial.AS35KAut
public import CFSG.Fischer.Classification.PSU6
import CFSG.Fischer.F4
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.AS35DFinal
public import CFSG.LargeExtraspecial.AS35ESixEleven
public import CFSG.LargeExtraspecial.AS35HInd
public import CFSG.LargeExtraspecial.AS35HQuotSet
public import CFSG.LargeExtraspecial.AS35HSixEightA
public import CFSG.LargeExtraspecial.AS35HSixEightB
public import CFSG.LargeExtraspecial.AS35IExtra
public import CFSG.LargeExtraspecial.AS35KBridge
public import CFSG.LargeExtraspecial.AS35KCo2
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Certificate10091Base

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.Blueprint.Fischer (K)

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

local notation "SUK" =>
  CFSG.LieType.Universal.Unitary.SUid CFSG.Fischer.Classification.Unitary.frob 6

theorem SUid_eq_map : SUK = SU0.map ψGL.toMonoidHom := by
  rw [← CFSG.Fischer.Classification.Unitary.SUm_eq 6, ← SU_eq_map]
  exact CFSG.Fischer.Classification.localSU_eq_SU_one

@[expose] noncomputable def suSUid : SU0 ≃* SUK :=
  (SU0.equivMapOfInjective ψGL.toMonoidHom ψGL.injective).trans
    (MulEquiv.subgroupCongr SUid_eq_map.symm)

theorem coe_suSUid (s : SU0) : ((suSUid s : SUK) : GL (Fin 6) K) = ψGL s := rfl

theorem coe_suSUid_symm (g : SUK) : ((suSUid.symm g : SU0) : GL (Fin 6) F4) = ψGL.symm g := by
  rw [MulEquiv.eq_symm_apply]
  conv_rhs => rw [← suSUid.apply_symm_apply g]
  rw [coe_suSUid]

@[expose] noncomputable def pgT46 :
    CFSG.Fischer.Classification.Unitary.PG 6 ≃* T46 :=
  (quotientCenterCongr suSUid).symm.trans suQuotEquiv

theorem pgT46_mk (s : SU0) :
    ((pgT46 (QuotientGroup.mk (suSUid s)) : T46) : Equiv.Perm (Fin 693)) = piSU s := by
  rw [pgT46, MulEquiv.trans_apply, ← quotientCenterCongr_mk, MulEquiv.symm_apply_apply,
    suQuotEquiv_mk]

theorem ψGL_symm_val (M : GL (Fin 6) K) :
    ((ψGL.symm M : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (M : Matrix (Fin 6) (Fin 6) K).map ψ.symm := by
  have h : ((ψGL (ψGL.symm M) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = M := by
    rw [MulEquiv.apply_symm_apply]
  rw [ψGL_val] at h
  rw [← h]
  ext i j
  simp

theorem herm_ψV (a b : W) :
    CFSG.ClassicalGroups.Unitary.herm CFSG.Fischer.Classification.Unitary.frob (ψV a) (ψV b) =
      ψ (hermStd b a) := by
  simp only [CFSG.ClassicalGroups.Unitary.herm_def, hermStd, ψV, map_sum, map_mul, map_pow,
    CFSG.Fischer.Classification.Unitary.frob_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem isIsom_ψGL_symm {B : GL (Fin 6) K}
    (hB : ∀ x y : Fin 6 → K,
      CFSG.ClassicalGroups.Unitary.herm CFSG.Fischer.Classification.Unitary.frob
        ((B : Matrix (Fin 6) (Fin 6) K) *ᵥ x) ((B : Matrix (Fin 6) (Fin 6) K) *ᵥ y) =
      CFSG.ClassicalGroups.Unitary.herm CFSG.Fischer.Classification.Unitary.frob x y) :
    IsIsom ((ψGL.symm B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  intro x y
  have key : ∀ v : W, (B : Matrix (Fin 6) (Fin 6) K) *ᵥ ψV v =
      ψV (((ψGL.symm B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) := by
    intro v
    conv_lhs => rw [← MulEquiv.apply_symm_apply ψGL B]
    rw [ψGL_val, mulVec_ψ]
  have h := hB (ψV y) (ψV x)
  rw [key, key, herm_ψV, herm_ψV] at h
  rw [herm_eq_std, herm_eq_std]
  exact ψ.injective h

@[expose] noncomputable def fieldOf (φ : K ≃+* K) : F4 ≃+* F4 := ψ.trans (φ.trans ψ.symm)

theorem ψGL_symm_glAut (φ : K ≃+* K) (s : GL (Fin 6) F4) :
    ψGL.symm (glAut φ (ψGL s)) = glAut (fieldOf φ) s := by
  apply Units.ext
  rw [ψGL_symm_val, coe_glAut, coe_glAut, ψGL_val]
  ext i j
  rfl

theorem exists_semiPerm
    (α : MulAut T46) : ∃ (A : GU0) (φ : F4 ≃+* F4), ∀ g : T46,
      ((α g : T46) : Equiv.Perm (Fin 693)) = semiPerm A φ * g * (semiPerm A φ)⁻¹ := by
  obtain ⟨AK, φK, hβ⟩ := AS35K.exists_realize (m := 6) (by norm_num)
    (pgT46.trans (α.trans pgT46.symm))
  set A : GU0 := ⟨ψGL.symm (AK : GL (Fin 6) K),
    isIsom_ψGL_symm (AS35K.herm_mulVec_of_unitary AK.2)⟩ with hA
  refine ⟨A, fieldOf φK, fun g => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : SU0, piSU s = g := by
    have hg : (g : Equiv.Perm (Fin 693)) ∈ piSU.range := by rw [range_piSU]; exact g.2
    obtain ⟨s, hs⟩ := hg
    exact ⟨s, hs⟩
  obtain ⟨g', hg', hβg⟩ := hβ (suSUid s)
  have h1 : pgT46 (QuotientGroup.mk (suSUid s)) = g := Subtype.ext (by rw [pgT46_mk, hs])
  have h2 : α g = pgT46 (QuotientGroup.mk g') := by
    have := congrArg pgT46 hβg
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, h1] at this
    exact this
  rw [h2, ← suSUid.apply_symm_apply g', pgT46_mk]
  have h3 : (Subgroup.inclusion SU0_le_GU0 (suSUid.symm g') : GU0) =
      semiConj A (fieldOf φK) (Subgroup.inclusion SU0_le_GU0 s) := by
    apply Subtype.ext
    change ((suSUid.symm g' : SU0) : GL (Fin 6) F4) = _
    rw [coe_suSUid_symm, hg', coe_semiConj, map_mul, map_mul, map_inv, coe_suSUid,
      ψGL_symm_glAut]
    rfl
  change piGU (Subgroup.inclusion SU0_le_GU0 (suSUid.symm g')) = _
  rw [h3, ← conj_semiPerm, ← hs]
  rfl

end CFSG.LargeExtraspecial.SMod20.Aut
