module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bCubic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bSyl3
import CFSG.Quasithin.Vol2.Ch11SecBL2UKp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bEightProof

open Matrix

theorem center_eq_bot (F : Type) [Field F] [Finite F] (hF : Nat.card F = 8)
    {z : SpecialLinearGroup (Fin 3) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) : z = 1 := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  haveI := Fintype.ofFinite F
  rw [Fintype.card_fin] at hr3
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr3
    simp at hr3
  have h7 : r ^ 7 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [← Nat.card_eq_fintype_card, hF] at h
    simpa using h
  have hr1 : r = 1 :=
    calc r = r * (r ^ 3) ^ 2 := by rw [hr3]; ring
      _ = r ^ 7 := by ring
      _ = 1 := h7
  refine Subtype.ext ?_
  rw [← hr, hr1]
  simp

theorem no_elemAbelian_psl_eight (F : Type) [Field F] [Finite F] (hF : Nat.card F = 8)
    (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) : False := by
  obtain ⟨h2, t, ht⟩ := exists_root_cubic_of_card_eight F hF
  obtain ⟨g, hg⟩ := exists_orderOf_nine_sl3 F h2 ht
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F))) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact center_eq_bot F hF ((QuotientGroup.eq_one_iff x).mp hx)
  have hord : orderOf (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F)) g) =
      9 := by
    rw [orderOf_injective _ hinj g]
    exact hg
  have hcard : ∃ k : ℕ, ¬ 3 ∣ k ∧
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 9 * k := by
    refine ⟨1831424, by norm_num, ?_⟩
    rw [CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA (K := F) (n := 3) (by norm_num), hF]
    decide
  exact K21bSyl3Proof.no_elemAbelian_of_orderOf_nine hcard ⟨_, hord⟩ E hE hc

end K21bEightProof

end CFSG.LocalAnalysis.RankThreeUC.S15
