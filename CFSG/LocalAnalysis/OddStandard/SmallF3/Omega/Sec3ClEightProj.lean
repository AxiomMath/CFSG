module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermInner

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open scoped commutatorElement

open Subgroup CFSG.ComponentClassification.CatalogueBUnitaryIsometry
  CFSG.ClassicalInvolution.Phan

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma suToOrth_commutatorElement (A B : Uid σ9 4) :
    suToOrth (⟨(⁅A, B⁆ : Uid σ9 4), commutatorElement_mem_SUid A B⟩ : Su F9 3 1 4) =
      uidToOrth 4 ⁅A, B⁆ := rfl

theorem cl_inFStar_of_isComponentIn_fix_proj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = 1) {y : OGroup Q}
    (hy : y * y = piOrth Q) {K : Subgroup (omegaProj hQ)}
    (hK : IsComponentIn K (fixSub (projAut hQ y))) : InFStar K := by
  obtain ⟨E, hEy, hEΩ⟩ := exists_frame_iso hQ hdim hs hy
  have hπ := frame_iso_piOrth E hEy hy
  have hker0 : (suToProj hQ E hEΩ).ker = Subgroup.zpowers hermNegSU := by
    ext s
    rw [MonoidHom.mem_ker, suToProj_eq_one_iff hQ E hEΩ hπ, mem_zpowers_hermNegSU]
  have hkerR : (suToProj hQ E hEΩ).rangeRestrict.ker = Subgroup.zpowers hermNegSU := by
    rw [MonoidHom.ker_rangeRestrict, hker0]
  obtain ⟨hq, h2⟩ := isQuasisimple_isTwoU43_of_cover _
    (suToProj hQ E hEΩ).rangeRestrict_surjective hkerR
  have hEs : E.symm y = omegaOrth 4 := by rw [← hEy, MulEquiv.symm_apply_apply]
  have hXC : (suToProj hQ E hEΩ).range ≤ fixSub (projAut hQ y) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_fixSub_projAut_iff]
    have hsval : ((suToProj hQ E hEΩ s : omegaProj hQ) : ProjOrth Q) =
        toProj Q (E (suToOrth s)) := by
      rw [suToProj, MonoidHom.comp_apply, coe_omegaToProj, coe_suToOmega]
    rw [hsval]
    have hcomm : E (suToOrth s) * y = y * E (suToOrth s) := by
      rw [← hEy, ← map_mul, ← map_mul, suToOrth_comm_omega]
    rw [← map_mul, ← map_mul, hcomm]
  have hle : ⁅cOmega hQ y, cOmega hQ y⁆ ≤ (suToOmega hQ E hEΩ).range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hcomm_a : E.symm (a : OGroup Q) * omegaOrth 4 =
        omegaOrth 4 * E.symm (a : OGroup Q) := by
      rw [← hEs, ← map_mul, ← map_mul, (mem_cOmega_iff hQ y a).mp ha]
    have hcomm_b : E.symm (b : OGroup Q) * omegaOrth 4 =
        omegaOrth 4 * E.symm (b : OGroup Q) := by
      rw [← hEs, ← map_mul, ← map_mul, (mem_cOmega_iff hQ y b).mp hb]
    obtain ⟨A, hA⟩ := exists_uid_of_comm hcomm_a
    obtain ⟨B, hB⟩ := exists_uid_of_comm hcomm_b
    refine ⟨⟨(⁅A, B⁆ : Uid σ9 4), commutatorElement_mem_SUid A B⟩, ?_⟩
    apply Subtype.ext
    rw [coe_suToOmega, suToOrth_commutatorElement]
    have hcoe : ((⁅a, b⁆ : omegaGroup hQ) : OGroup Q) =
        ⁅(a : OGroup Q), (b : OGroup Q)⁆ :=
      map_commutatorElement (Subgroup.subtype (omegaGroup hQ)) a b
    rw [hcoe]
    have hAa : E (uidToOrth 4 A) = (a : OGroup Q) := by rw [hA, MulEquiv.apply_symm_apply]
    have hBb : E (uidToOrth 4 B) = (b : OGroup Q) := by rw [hB, MulEquiv.apply_symm_apply]
    rw [← hAa, ← hBb, map_commutatorElement (f := uidToOrth 4),
      map_commutatorElement (f := E)]
  have hKX : K ≤ (suToProj hQ E hEΩ).range := by
    have hKH : K ≤ (cOmega hQ y).map (omegaToProj hQ) :=
      (IsComponentIn.le_commutator hK hK.le).trans (cl_commutator_fixSub_projAut_le hQ y)
    have hKcomm : K ≤ ⁅(cOmega hQ y).map (omegaToProj hQ),
        (cOmega hQ y).map (omegaToProj hQ)⁆ :=
      IsComponentIn.le_commutator hK hKH
    rw [← Subgroup.map_commutator] at hKcomm
    calc K ≤ (⁅cOmega hQ y, cOmega hQ y⁆).map (omegaToProj hQ) := hKcomm
      _ ≤ ((suToOmega hQ E hEΩ).range).map (omegaToProj hQ) := Subgroup.map_mono hle
      _ = (suToProj hQ E hEΩ).range := by rw [suToProj, MonoidHom.range_comp]
  have hKXeq : K = (suToProj hQ E hEΩ).range :=
    IsComponentIn.eq_of_isQuasisimple (hK.mono hKX hXC) hq
  rw [show InFStar K = IsFStarGroup ↥K from rfl, hKXeq]
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaProj hQ) := inferInstance
  have hodd : oddCore ((suToProj hQ E hEΩ).range) = ⊥ := oddCore_eq_bot_of_isTwoU43 hq h2
  refine Or.inl ⟨hq, Or.inr ?_⟩
  exact isTwoU43_of_mulEquiv
    ((QuotientGroup.quotientBot (G := (suToProj hQ E hEΩ).range)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hodd.symm)) h2

end CFSG.OddStandard.SmallF3.Omega
