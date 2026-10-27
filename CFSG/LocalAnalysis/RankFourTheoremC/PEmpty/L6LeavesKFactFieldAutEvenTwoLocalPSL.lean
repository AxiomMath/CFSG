module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenZsig
public import CFSG.GH74.Generic.S1.KL5Ord

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedSL)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

theorem prime_dvd_pow_sub_one {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    p ∣ a ^ (p - 1) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).1 h)
  have h2 := ZMod.pow_card_sub_one_eq_one h1
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero p))
  have h3 : ((a ^ (p - 1) - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ ha0), Nat.cast_pow, h2]
    simp
  exact (ZMod.natCast_eq_zero_iff _ p).1 h3

theorem twoLocalWhen_PSL : TwoLocalWhen .PSL (fun n f₀ => ¬ IsExcRow .PSL n f₀) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  have hcl0 : StatedClassicalModel K .PSL n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp2 : p ≠ 2 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn : ¬ p ∣ n := by
    intro hpn
    have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have hp2f : ¬ p ∣ 2 ^ f := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow h))
    have hferm := prime_dvd_pow_sub_one hp hp2f
    have hmem : p - 1 ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hprod : p ∣ ∏ j ∈ Finset.Icc 2 n, ((2 ^ f) ^ j - 1) :=
      hferm.trans (Finset.dvd_prod_of_mem (fun j => (2 ^ f) ^ j - 1) hmem)
    have hkl5 := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psl hn2 hcl0
    have hdvd : p ∣ Nat.card K * Nat.gcd n (2 ^ f - 1) := by
      rw [hkl5]
      exact Dvd.dvd.mul_left hprod _
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact hpK h
    · exact hdiv h
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ hn2
    (fun h => hP ⟨h.1, Or.inl ⟨rfl, h.2⟩⟩)
  have hppd := fun k => ppd_dvd_iff hrm hm hcorr hp hpn k
  have hr : r.Prime := hrm.1
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
    intro hrN
    set R' : Subgroup (StatedProj (StatedSL n F)) := R.map e.toMonoidHom with hR'
    have hR'2 : IsPGroup 2 R' := hR2.map e.toMonoidHom
    have hR'1 : R' ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)
    have hcardF : Nat.card F = 2 ^ f := hFcard
    have hfin : Fintype.card (Fin n) = n := Fintype.card_fin n
    refine not_dvd_card_normalizer_statedProj (StatedSL n F) hr (by rw [hfin]; exact hn2)
      (by rw [hfin, hcardF, hf]; exact (hppd n).2.2 (dvd_refl n)) (fun k hk hk' => ?_) R' hR'2 hR'1
      (hrN.trans (card_normalizer_dvd_of_mulEquiv e R))
    rw [hfin] at hk'
    rw [hcardF, hf]
    intro h
    exact absurd (Nat.le_of_dvd hk ((hppd k).2.1 h)) (not_le.mpr hk')
  haveI : Fact r.Prime := ⟨hr⟩
  have hv0 : padicValNat r (Nat.card (Subgroup.normalizer (R : Set K))) = 0 :=
    padicValNat.eq_zero_of_not_dvd hRn
  have hq1 : ¬ r ∣ 2 ^ f₀ - 1 := by
    intro h
    have h1 := (hppd 1).1
    rw [pow_one] at h1
    have h2 := h1.1 h
    exact absurd (Nat.le_of_dvd one_pos h2) (by omega)
  have hdr : padicValNat r (lieOrderDivisor .PSL n (2 ^ f₀)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hq1 (h.trans (Nat.gcd_dvd_right n (2 ^ f₀ - 1))))
  have hrn : r ∣ lieOrderNumerator .PSL n (2 ^ f₀) := by
    have hmem : n ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨hn2, le_rfl⟩
    have h1 : r ∣ (2 ^ f₀) ^ n - 1 := ((hppd n).1).2 (dvd_refl n)
    exact Dvd.dvd.mul_left (h1.trans (Finset.dvd_prod_of_mem (fun j => (2 ^ f₀) ^ j - 1) hmem)) _
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hnum0 : lieOrderNumerator .PSL n (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) ?_
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hj2 : j ≠ 0 := by
      have := (Finset.mem_Icc.1 hj).1
      omega
    have := Nat.one_lt_pow hj2 hq2
    omega
  rw [hv0, hdr, zero_add]
  exact one_le_padicValNat_of_dvd hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
