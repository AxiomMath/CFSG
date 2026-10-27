
module


public import CFSG.LocalAnalysis.OddStandard.ONanCMCard
public import Certificates.Certificate6146

public section

namespace CFSG.OddStandard.ONanRec

set_option maxRecDepth 100000 in
theorem centFacts_CModel :
    CentFacts CModel := by
  classical
  have hB := CM.cmBoundCheck_cert
  have hM := CM.cmModelCheck_cert
  have h1 := CM.lettersOK_of hM
  set e := CM.equivM480 hB hM with he
  refine ⟨CM.card_CModel hB hM, Certificates.certificate6146, ?_⟩
  ·
    have hra := CM.rep_letter h1 (c := 2 * ((0 : Fin 6) : ℕ)) (by norm_num)
    have hrb := CM.rep_letter h1 (c := 2 * ((1 : Fin 6) : ℕ)) (by norm_num)
    refine ⟨PresentedGroup.of (0 : Fin 6), ?_, ?_⟩
    · have ha2 : CM.genPerm 0 * CM.genPerm 0 = 1 := by
        have h0 := CM.letterPerm_odd h1 (i := 0) (by norm_num)
        have hl : CM.letterPerm (2 * 0 + 1) = CM.letterPerm (2 * 0) := rfl
        rw [hl] at h0
        have e0 : ((0 : Fin 6) : ℕ) = 0 := rfl
        rw [CM.genPerm, e0]
        nth_rewrite 2 [h0]
        exact mul_inv_cancel _
      have hne : CM.genPerm 0 ≠ 1 := by
        intro h0
        have h3 := hra ⟨0, by norm_num⟩
        rw [← CM.genPerm, h0] at h3
        exact absurd h3 (by decide)
      refine orderOf_eq_prime ?_ ?_
      · apply e.injective
        apply Subtype.ext
        rw [map_pow, Subgroup.coe_pow, CM.equivM480_of, map_one, Subgroup.coe_one, pow_two, ha2]
      · intro h0
        apply hne
        have h3 := congrArg (fun x => ((e x : CM.M480) : Equiv.Perm (Fin 480))) h0
        simp only [map_one, Subgroup.coe_one] at h3
        rw [CM.equivM480_of] at h3
        exact h3
    · intro hc
      have hcomm := Subgroup.mem_center_iff.1 hc (PresentedGroup.of (1 : Fin 6))
      have h2 := congrArg (fun x => ((e x : CM.M480) : Equiv.Perm (Fin 480))) hcomm
      simp only [map_mul, Subgroup.coe_mul] at h2
      rw [CM.equivM480_of, CM.equivM480_of] at h2
      have hp := congrArg (fun g : Equiv.Perm (Fin 480) => ((g ⟨2, by norm_num⟩ : Fin 480) : ℕ)) h2
      simp only [Equiv.Perm.mul_apply] at hp
      rw [CM.genPerm, CM.genPerm, ← hrb, ← hra, ← hra, ← hrb] at hp
      exact absurd hp (by decide)

end CFSG.OddStandard.ONanRec
