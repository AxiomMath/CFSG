module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Heis
public import CFSG.RankThree.Native.LyFiveSpec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint CFSG.RankThree.Native
open scoped commutatorElement

theorem ly_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Ly := by
  have h := lyFiveQRelJ
  have hJ : HasNonabelianFiveSubgroup CFSG.Sporadic.Ly.J := by
    refine ⟨fiveQ lyFiveXJ lyFiveVJ, fun g => ⟨1, ?_⟩, fun hc => ?_⟩
    · apply Subtype.ext
      rw [pow_one, Subgroup.coe_pow]
      exact h.pow_five_of_mem g.2
    · have h01 := congrArg Subtype.val
        (mul_comm' (⟨lyFiveVJ 0, FiveQRel.v_mem 0⟩ : fiveQ lyFiveXJ lyFiveVJ)
          ⟨lyFiveVJ 1, FiveQRel.v_mem 1⟩)
      simp only [Subgroup.coe_mul] at h01
      have hc01 := commutatorElement_eq_one_iff_mul_comm.2 h01
      rw [h.comm, show (lyFiveOmega 0 1).val = 4 from rfl, h.x_pow_eq_one_iff] at hc01
      exact absurd hc01 (by decide)
  exact @HasNonabelianFiveSubgroup.of_mulEquiv CFSG.Sporadic.Ly.J NativeSporadic.Ly inferInstance
    inferInstance CFSG.Sporadic.Ly.lyEquivJ.symm hJ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
