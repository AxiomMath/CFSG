module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.HardMathSupport.Dickson.BMRows.NotSqDvd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator

section Rows


theorem kd264SporAt_M {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KD264SporAt p .M := by
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) := by
    have : IsSimpleGroup CFSG.Open.MonsterY443Derived := CFSG.Milestones.fam_m_simplicity
    exact CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.isSimpleGroup
  haveI : Finite (NativeSporadic.Carrier .M) :=
    CFSG.Sporadic.finite_carrier_M_of_card CFSG.Milestones.fam_m_finiteness
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M
  have hc : Nat.card (NativeSporadic.Carrier .M) = sporOrd .M :=
    (Nat.card_congr b.toEquiv).trans (sporadicOrdersTable_holds .M)
  have hnp : ¬ (sporOrd .M).Prime := by norm_num [sporOrd, orderMonster]
  have hnc := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
    (S := NativeSporadic.Carrier .M) (by rw [hc]; exact hnp)
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  refine kd264SporAt_of_model hOut hp hp2 hnc b fun hk2 _ hsq => ?_
  exfalso
  rw [hc] at hsq
  by_cases h17 : 17 ≤ p
  · exact CFSG.HardMathSupport.Dickson.BMRows.not_sq_dvd_orderMonster_of_seventeen_le hp h17 hsq
  · apply hk2
    interval_cases p <;> first | exact absurd rfl hp2 | (simp [k2Spor]; done) | (exfalso; norm_num at hp)

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
