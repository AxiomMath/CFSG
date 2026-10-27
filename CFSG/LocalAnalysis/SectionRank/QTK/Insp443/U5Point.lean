module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.Quasithin.H13.U5ParPointQuot

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

theorem KConfig.not_u5PtP {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K)
    {L V : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1)}
    (hc : KConfig (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1) L V
      (CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h)) : False := by
  haveI := h.finite
  haveI := CFSG.Quasithin.H13.Sec53F.Unit.finite_hypPSU_five h
  have hLne : L ≠ ⊥ := fun hL =>
    hc.ne_bot (by rw [hc.eq_commutator, hL, Subgroup.commutator_bot_right])
  have hLeq : L = perfectCore (CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h) :=
    hc.eq_perfectCore_of_simple
      (CFSG.Quasithin.H13.U5Par.isSimpleGroup_modO2_perfectCore_u5PtP h)
  have hVZ : V ≤ centerOf (pCoreOf 2 (perfectCore
      (CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h))) := by
    rw [← hLeq, CFSG.Quasithin.centerOf]
    exact le_inf hc.le_pCoreOf (Subgroup.le_centralizer_iff.mpr hc.pCoreOf_le)
  have hLV' : perfectCore (CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h) ≤
      Subgroup.centralizer (V : Set
        (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1)) := by
    rw [Subgroup.le_centralizer_iff]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.H13.U5Par.perfectCore_u5PtP_le_centralizer h (by norm_num) hl)
      v (hVZ hv)).symm
  have hLV : L ≤ Subgroup.centralizer (V : Set
      (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1)) := hLeq.symm ▸ hLV'
  have hcomm : ⁅V, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := L) (H₂ := V)).mpr hLV
  exact hc.ne_bot (by rw [hc.eq_commutator, hcomm])

end CFSG.SectionRank.QTK.Insp443

end
