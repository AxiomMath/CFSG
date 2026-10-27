module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Core

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
  in
theorem false_of_altSq_split_g2_field (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* AdjointQuotient .G2 K)
    (hpf : p ∣ Nat.card K - 1) : False := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  have hB := borelQuotient_g2 e
  rw [hcard] at hpf
  refine false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi => ?_
  obtain ⟨φ, hφ, hU, hL⟩ := hasSL2Node_g2 (K := K) i
  exact exists_quasisimple_of_sl2_hom hZ hB hker hi hφ (range_le_rankOne_of_hasSL2Node hU hL)
    hp57 (by rw [hcard]; exact sixteen_or_eight hp57 hf hpf)
    (by rw [hcard]; exact dvd_sq_sub_one_of_dvd hpf)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
