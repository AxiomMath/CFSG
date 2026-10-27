module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.SpinMinus

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg.CentralExt

theorem dvd_sq_sub_one_of_dvd_add_one {p c : ℕ} (h : p ∣ c + 1) : p ∣ c ^ 2 - 1 :=
  h.trans ⟨c - 1, by rw [← Nat.sq_sub_sq c 1, one_pow]⟩

theorem eq_five_of_dvd_two_pow_add_one {p f : ℕ} (hp57 : p = 5 ∨ p = 7) (hf : 1 ≤ f)
    (h : p ∣ 2 ^ f + 1) : p = 5 ∧ 2 ≤ f := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have key : ∀ g : ℕ, (2 ^ (g + 1) + 1) % 7 ≠ 0 := by
    intro g
    have h3 : ∀ g : ℕ, 2 ^ g % 7 = 1 ∨ 2 ^ g % 7 = 2 ∨ 2 ^ g % 7 = 4 := by
      intro g
      induction g with
      | zero => simp
      | succ g ih => rw [pow_succ]; omega
    have := h3 (g + 1)
    omega
  rcases hp57 with rfl | rfl
  · refine ⟨rfl, ?_⟩
    by_contra hlt
    obtain rfl : g = 0 := by omega
    norm_num at h
  · exact absurd (Nat.mod_eq_zero_of_dvd h) (key g)

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}

theorem false_of_altPlus_pomegaMinus_of_four_le (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f)
    (hpf : p ∣ 2 ^ f + 1) (hf4 : 4 ≤ f) : False := by
  obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hn4 : 4 ≤ n := by omega
  have hB := borelQuotient_spinMinus hirr hn4 e
  have hp1 : p ∣ (2 ^ f) ^ 2 - 1 := dvd_sq_sub_one_of_dvd_add_one hpf
  refine false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi => ?_
  by_cases hk : i.val + 1 < n - 1
  · obtain ⟨φ, hφ, hU, hL⟩ := hasSL2Node_spinMinus_long hirr hk
    exact exists_quasisimple_of_sl2_hom hZ hB hker hi hφ (range_le_rankOne_of_hasSL2Node hU hL)
      hp57 (Or.inl (by rw [hcard]; exact sixteen_dvd_two_pow hf4)) (by rw [hcard]; exact hp1)
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
      hp57 (Or.inl (by rw [hkcard]; exact sixteen_dvd_two_pow_sq (by omega)))
      (by rw [hkcard]; exact dvd_sq_sub_one_of_dvd hp1)

theorem false_of_altPlus_shortNode (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {n f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n)
    (hcard : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (π' : spinGroup (quadMinus n F b c) →* ↥L ⧸ Subgroup.center ↥L)
    (hker : π'.ker = (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn4 hirr))).ker)
    (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1)
    (hle : (rankOne (minusDatum n hirr).rootGroup k).map π' ≤ quotImage L J) : False := by
  have hB := borelQuotient_spinMinus hirr hn4 e
  obtain ⟨hJL, T, hT, hNT⟩ := h.parab
  have hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J :=
    fun z hz => center_le_of_normalizer_le hT hNT hz
  have hp1 : p ∣ (2 ^ f) ^ 2 - 1 := dvd_sq_sub_one_of_dvd_add_one hpf
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hkcard : Nat.card (ShortField b c) = (2 ^ f) ^ 2 := by
    rw [SpinMinusClosed.card_shortField, hcard]
  have hk4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [hkcard]
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 4 ≤ 2 ^ f := this
      _ ≤ (2 ^ f) ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨Θ, hU, hL⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr k)
  have hinj : Function.Injective Θ := by
    refine sl2_injective_of_upper_ne_one hk4 Θ ?_
    rw [hU, ← (shortRels n hirr k).x_zero]
    intro h1
    exact one_ne_zero (shortRels_x_injective hirr k h1)
  have h16 : 16 ∣ (2 ^ f) ^ 2 := by
    rw [← pow_mul]
    calc 16 = 2 ^ 4 := by norm_num
      _ ∣ 2 ^ (f * 2) := pow_dvd_pow 2 (by omega)
  exact false_of_quasisimple_of_altSq hp57 hAlt
    (exists_quasisimple_of_sl2_hom hZ hB hker hle hinj
      (range_le_rankOne_of_hasSL2Node (fun t => by
        rw [hU]; exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, rfl⟩)
        (fun t => by
        rw [hL]; exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨t, rfl⟩))
      hp57 (Or.inl (by rw [hkcard]; exact h16)) (by rw [hkcard]; exact dvd_sq_sub_one_of_dvd hp1))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
