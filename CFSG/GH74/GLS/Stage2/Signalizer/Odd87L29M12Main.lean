module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29First
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12Bridge
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnSL23
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnUT3B
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm4.Core98
public import CFSG.GH74.GLS.Stage1.Thm4.Statements
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpQ8
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12

theorem l29M12NoConj_proved : L29M12NoConj := by
  intro G _ _ z S ctx U hU hno
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 := hU.2
    rw [this, Subgroup.card_bot] at h4
    omega
  have hx2' : x * x = 1 := four_sq_eq_one hU hxU
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2') hx1
  obtain ⟨u, huU, hux⟩ := exists_mem_not_zpowers hU hxU
  have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
  have hu2' : u * u = 1 := four_sq_eq_one hU huU
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2') hu1
  have huN : u ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU huU hxU
  obtain ⟨K, y, q, hKc, hKL, hq8, hyC, hy2, hPGL, -, hRO, -⟩ :=
    ctx.detail.m12 rfl x hx2 (hno x hxU)
  have hTN := L29M12.twoNilp_centralizer_pair_of_m12 hx2 hKc hKL hq8 hyC hy2 hPGL hRO huN hu2 hux
  have hUeq : zpowers x ⊔ zpowers u = U := eq_zpowers_sup_of_mem hU hxU huU hx1 hux
  have hC : centralizer (U : Set G) = centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) := by
    ext g
    constructor
    · intro hg
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hg x hxU).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg u huU).symm⟩
    · rintro ⟨hgx, hgu⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hle : zpowers x ⊔ zpowers u ≤ centralizer ({g} : Set G) :=
        sup_le ((zpowers_le).mpr (by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_singleton_iff.mp hgx).symm))
          ((zpowers_le).mpr (by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_singleton_iff.mp hgu).symm))
      have := hle (hUeq ▸ hw)
      exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [hC]
  exact (hasNormal2Compl_iff_twoNilp _).mpr hTN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
