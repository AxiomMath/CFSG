module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Core
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg.CentralExt

theorem sl2_injective_of_upper_ne_one {k : Type} [Field k] [CharP k 2] (h4 : 4 ≤ Nat.card k)
    {K : Type*} [Group K] (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (h : φ (sl2Upper (1 : k)) ≠ 1) : Function.Injective φ := by
  have := sl2_isSimpleGroup h4
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
  · exact hb
  · exact absurd (MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top (sl2Upper (1 : k)))) h

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}

theorem false_of_altSq_split_pomegaMinus (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f)
    (hpf : p ∣ 2 ^ f - 1) : False := by
  obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hn4 : 4 ≤ n := by omega
  have hB := borelQuotient_spinMinus hirr hn4 e
  obtain ⟨hf3, -⟩ := split_exponent hp57 hf hpf
  refine false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi => ?_
  by_cases hk : i.val + 1 < n - 1
  · obtain ⟨φ, hφ, hU, hL⟩ := hasSL2Node_spinMinus_long hirr hk
    exact exists_quasisimple_of_sl2_hom hZ hB hker hi hφ (range_le_rankOne_of_hasSL2Node hU hL)
      hp57 (by rw [hcard]; exact sixteen_or_eight hp57 hf hpf)
      (by rw [hcard]; exact dvd_sq_sub_one_of_dvd hpf)
  · have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    have : CharP (ShortField b c) 2 :=
      charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
    have hkcard : Nat.card (ShortField b c) = (2 ^ f) ^ 2 := by
      rw [SpinMinusClosed.card_shortField, hcard]
    have hk4 : 4 ≤ Nat.card (ShortField b c) := by
      rw [hkcard]
      have : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 4 ≤ 2 ^ f := this
        _ ≤ (2 ^ f) ^ 2 := Nat.le_self_pow two_ne_zero _
    obtain ⟨Θ, hU, hL⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr i)
    have hinj : Function.Injective Θ := by
      refine sl2_injective_of_upper_ne_one hk4 Θ ?_
      rw [hU, ← (shortRels n hirr i).x_zero]
      intro h1
      exact one_ne_zero (shortRels_x_injective hirr i h1)
    exact exists_quasisimple_of_sl2_hom hZ hB hker hi hinj
      (range_le_rankOne_of_hasSL2Node (fun t => by
        rw [hU]; exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, rfl⟩)
        (fun t => by
        rw [hL]; exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨t, rfl⟩))
      hp57 (Or.inl (by rw [hkcard]; exact sixteen_dvd_two_pow_sq hf3))
      (by rw [hkcard]; exact dvd_sq_sub_one_of_dvd (dvd_sq_sub_one_of_dvd hpf))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
