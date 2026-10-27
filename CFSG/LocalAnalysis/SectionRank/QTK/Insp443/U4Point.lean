module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.Quasithin.H13.U4ParPointQuot
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU4Model

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

theorem KConfig.not_parP {m : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K)
    {L V : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0)}
    (hc : KConfig (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0) L V
      (CFSG.Quasithin.H13.U4Par.parP h)) : False := by
  haveI := h.finite
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hLne : L ≠ ⊥ := fun hL =>
    hc.ne_bot (by rw [hc.eq_commutator, hL, Subgroup.commutator_bot_right])
  have hLle : L ≤ perfectCore (CFSG.Quasithin.H13.U4Par.parP h) :=
    le_perfectCore_of_perfect hc.le_MK hc.perfect
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by
      have := h.one_le
      omega
    rw [CFSG.Quasithin.H13.U4Par.perfectCore_parP_eq_bot h hm1] at hLle
    exact hLne (le_bot_iff.mp hLle)
  ·
    have hLeq : L = perfectCore (CFSG.Quasithin.H13.U4Par.parP h) :=
      hc.eq_perfectCore_of_simple
        (CFSG.Quasithin.H13.U4Par.isSimpleGroup_modO2_perfectCore_parP h hm2)
    have hVZ : V ≤ centerOf (pCoreOf 2 (perfectCore
        (CFSG.Quasithin.H13.U4Par.parP h))) := by
      rw [← hLeq, CFSG.Quasithin.centerOf]
      exact le_inf hc.le_pCoreOf (Subgroup.le_centralizer_iff.mpr hc.pCoreOf_le)
    have hLV' : perfectCore (CFSG.Quasithin.H13.U4Par.parP h) ≤
        Subgroup.centralizer (V : Set
          (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0)) := by
      rw [Subgroup.le_centralizer_iff]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (Subgroup.mem_centralizer_iff.mp
        (CFSG.Quasithin.H13.Ch4.U4A.point_core_centralizes_center_pCore h hm2 hl)
        v (hVZ hv)).symm
    have hLV : L ≤ Subgroup.centralizer (V : Set
        (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0)) := hLeq.symm ▸ hLV'
    have hcomm : ⁅V, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := L) (H₂ := V)).mpr hLV
    exact hc.ne_bot (by rw [hc.eq_commutator, hcomm])

end CFSG.SectionRank.QTK.Insp443

end
