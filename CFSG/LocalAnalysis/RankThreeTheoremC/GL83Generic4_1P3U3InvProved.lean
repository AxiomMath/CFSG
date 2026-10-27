module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowActionKFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem u3SylowInversion_proved : KFactU3SylowInversion := by
  intro K _ _ hK T
  obtain ⟨d, hd, -, he⟩ := u3_index hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, -, hrange, htor⟩ := CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus K 3 d hd he T
  obtain ⟨c, hcN, hc⟩ := htor (-1)
  refine ⟨c, hcN, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  have hzr : (T : Subgroup K).subtype w ∈ ψ.range := by
    rw [hrange]
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.mp hw ⟨t, ht⟩
    exact congrArg Subtype.val this
  obtain ⟨a, ha⟩ := hzr
  rw [← ha, hc a]
  have : Multiplicative.ofAdd (((-1 : (GaloisField 3 d.1.fieldExponent)ˣ) :
      GaloisField 3 d.1.fieldExponent) * Multiplicative.toAdd a) = a⁻¹ := by
    simp
  rw [this, map_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC
