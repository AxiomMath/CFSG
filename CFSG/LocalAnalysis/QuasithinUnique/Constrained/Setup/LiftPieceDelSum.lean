module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatSum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece CFSG.QuasithinUnique.Setup.Lift.PieceDel
open scoped commutatorElement

theorem delSumProp
    : DelSumProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hloc hgen
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hbase := hloc.base
  have hres := hloc.res
  have hq := hloc.q
  have hLn : (oddOrderSubgroup (⊤ : Subgroup G)).Normal := natL_normal
  have hQn : (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal :=
    normal_Q hcore.normal
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set B : Subgroup G := oddOrderSubgroup P with hB
  set Q : Subgroup G := pCoreOf 2 (L ⊔ baum R) with hQ
  have hQt : ∀ t : G, t ∈ Subgroup.normalizer (Q : Set G) := fun t => by
    have := hQn
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top t
  have hQc : ∀ t : G, Q.map (MulAut.conj t).toMonoidHom = Q := fun t =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQt t)
  have hOB : ⁅pCoreOf 2 B, B⁆ = modComm V Fs := by
    have h : pCoreOf 2 B = ⁅pCoreOf 2 B, B⁆ :=
      (hloc.ad.chi0.1.1.alt3_structure hloc.ad.alt3).1
    exact h.symm.trans hloc.ad.core.1
  have hI : modComm V Fs = ⁅B, V⁆ := modComm_eq_commutator (hnormV B) hres.image
  have hLV : ⁅V, L⁆ = ⁅L, V⁆ := Subgroup.commutator_comm _ _
  have hIW : modComm V Fs ≤ ⁅V, L⁆ := by
    rw [hI, hLV]
    exact Subgroup.commutator_mono (oddOrderSubgroup_mono le_top) le_rfl
  have hWn : (⁅V, L⁆ : Subgroup G).Normal := inferInstance
  refine ⟨fun t _ => ?_, fun t _ => ⟨?_, ?_⟩, ?_⟩
  ·
    exact le_normalizer_map_conj_of_mem hq.normalizes (hQt t)
  · rw [← hq.comm, Subgroup.map_commutator, hQc]
  · rw [pCoreOf_map_equiv 2 (MulAut.conj t) B, ← Subgroup.map_commutator, hOB]
  ·
    have hQL : ⁅Q, L⁆ = ⁅V, L⁆ := by
      refine le_antisymm ?_ (Subgroup.commutator_mono hbase.base.V_le_Q le_rfl)
      exact commutator_le_of_le_conjJoin (hq.comm.le.trans hIW) hgen.gen.le
    have hVL : ⁅V, L⁆ = ⨆ j, modComm V (Lc j) := by
      calc ⁅V, L⁆ = ⁅L, V⁆ := hLV
        _ = modComm V (autOn L V) := (modComm_autOn (hnormV L)).symm
        _ = modComm V (⨆ j, Lc j) := by rw [hbridge.K_eq, hbridge.K_prod]
        _ = ⨆ j, modComm V (Lc j) := modComm_iSup V Lc
    refine ⟨hQL, hVL, ?_⟩
    rw [← hVL, ← hQL]
    exact hgen.central

end CFSG.QuasithinUnique.Setup.Lift
