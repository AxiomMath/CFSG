module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Core

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}

theorem false_of_altSq_split_psl (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f)
    (hpf : p ∣ 2 ^ f - 1) : False := by
  exact false_of_quasisimple_of_altSq hp57 hAlt
    (exists_quasisimple_of_model_psl hp57 hmodel hpf h.parab h.ne_borel)

theorem false_of_altSq_split_psp (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f)
    (hpf : p ∣ 2 ^ f - 1) : False := by
  obtain ⟨⟨-, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hB := borelQuotient_sp e
  refine false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi => ?_
  obtain ⟨φ, hφ, hU, hL⟩ := hasSL2Node_sp (F := F) i
  exact exists_quasisimple_of_sl2_hom hZ hB hker hi hφ (range_le_rankOne_of_hasSL2Node hU hL)
    hp57 (by rw [hcard]; exact sixteen_or_eight hp57 hf hpf)
    (by rw [hcard]; exact dvd_sq_sub_one_of_dvd hpf)

open CFSG.LieType.Universal.Spin in
theorem false_of_altSq_split_pomegaPlus (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f)
    (hpf : p ∣ 2 ^ f - 1) : False := by
  obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hB := borelQuotient_spinPlus hn3 e
  refine false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi => ?_
  obtain ⟨φ, hφ, hU, hL⟩ := hasSL2Node_spinPlus (F := F) hn3 i
  exact exists_quasisimple_of_sl2_hom hZ hB hker hi hφ (range_le_rankOne_of_hasSL2Node hU hL)
    hp57 (by rw [hcard]; exact sixteen_or_eight hp57 hf hpf)
    (by rw [hcard]; exact dvd_sq_sub_one_of_dvd hpf)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
