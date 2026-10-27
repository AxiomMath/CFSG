module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.PieceDel
open scoped commutatorElement

theorem delGenProp : DelGenProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hloc
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hbase := hloc.base
  have hres := hloc.res
  have hR2 : IsPGroup 2 R := hS.sylow.2.1
  have hLn : (oddOrderSubgroup (⊤ : Subgroup G)).Normal := natL_normal
  have hQn : (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal :=
    normal_Q hcore.normal
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hBL : oddOrderSubgroup P ≤ oddOrderSubgroup (⊤ : Subgroup G) :=
    oddOrderSubgroup_mono le_top
  have hDL : conjJoin R (oddOrderSubgroup P) ≤ oddOrderSubgroup (⊤ : Subgroup G) := by
    refine iSup_le fun s => ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hLn.conj_mem y (hBL hy) (s : G)
  have hLD : oddOrderSubgroup (⊤ : Subgroup G) ≤ conjJoin R (oddOrderSubgroup P) := by
    have htop : (⊤ : Subgroup G) ≤ conjJoin R (oddOrderSubgroup P) ⊔ R :=
      hres.gen.symm.le.trans (sup_le_sup_right (self_le_conjJoin R _) R)
    exact oddOrderSubgroup_le_of_pow_mem fun g _ =>
      C1.exists_pow_mem_of_mem_sup hR2 (le_normalizer_conjJoin_self R _) (htop (Subgroup.mem_top g))
  have hBV : oddOrderSubgroup P ≤ Subgroup.normalizer (V : Set G) := le_top.trans hX
  have hWB : modComm V Fs = ⁅oddOrderSubgroup P, V⁆ := modComm_eq_commutator hBV hres.image
  have hQB : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ ≤
      ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ := by
    rw [hloc.q.comm, hWB, Subgroup.commutator_comm (oddOrderSubgroup P) V]
    exact Subgroup.commutator_mono le_rfl hBL
  have hQL : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
      oddOrderSubgroup (⊤ : Subgroup G)⁆ ≤ ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ :=
    commutator_le_of_le_conjJoin hQB hLD
  have hVL : ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ≤ V := Subgroup.commutator_le_left _ _
  have hVQ : V ≤ pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) := hbase.base.V_le_Q
  have hVΩ : V ≤ omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)) := by
    refine le_omegaOneCenterOf_of_le hVQ ?_ fun v hv => hS.reduced.2.2.1.2 v hv
    intro q hq
    have hq' : q ∈ baum R ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← hbase.Q_eq]
      exact hq
    exact hq'.2
  refine ⟨le_antisymm hLD hDL, ?_, ?_, ?_, hQL.trans (hVL.trans hVΩ)⟩
  ·
    intro h
    have hW : modComm V Fs ≤ ⊥ := by
      rw [← hloc.q.comm]
      exact (Subgroup.commutator_mono le_rfl hBL).trans h.le
    have hcard := hloc.W.card
    rw [eq_bot_iff.2 hW, Subgroup.card_bot] at hcard
    omega
  · exact isElemAbelian_of_le (hQL.trans hVL) hS.reduced.2.2.1
  · have := hQn
    have := hLn
    exact Subgroup.commutator_normal _ _

end CFSG.QuasithinUnique.Setup.Lift
