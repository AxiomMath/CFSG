module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.Open

section Twisted


variable {K : Type} [Field K] [Finite K]

theorem card_graphFixedRootGroup_E6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.E6 K σ) = ordTwistedE6 (ℓ ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField (t := TwistTag.E6) hℓ hf hK hσ
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6] at hC
  have hT := card_compatTorus_mul (t := TwistTag.E6) (K := K) σ
  rw [CFSG.ClassicalInvolution.card_compat_inf_ker_E6_of_card hK hσ, card_compatSubgroup] at hT
  simp only [hq] at hT
  rw [prod_orbit_E6] at hT
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  rw [ordTwistedE6, ← ordTwistedE6_mul _ hq1, ← hT, hC]
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_).symm
  ring

theorem card_graphFixedRootMonomial_E6 (σ : K →+* K) :
    Nat.card (graphFixedRootMonomial TwistTag.E6 K σ) =
      Nat.card (graphFixedRootTorus TwistTag.E6 K σ) * 1152 := by
  have e := graphFixedRootMonomialQuotientEquiv TwistTag.E6 K σ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf (graphFixedRootMonomial TwistTag.E6 K σ))
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (CFSG.RankThree.Chevalley.graphFixedRootTorus_le_graphFixedRootMonomial (t := TwistTag.E6) (K := K) (σ := σ))).toEquiv] at h1
  have hW : Nat.card (relWeylTwist TwistTag.E6) = 1152 :=
    (Nat.card_congr (foldedWeylEquiv TwistTag.E6).toEquiv).trans
      CFSG.RankThree.PartOne.K133H.card_weylGroup_F4
  rw [hW] at h1
  rw [h1, mul_comm]

open CFSG.HardMathSupport.Curtis.UnitaryLevi in
theorem padicValNat_three_ordTwistedE6 {q : ℕ} (hq : 1 < q) (hq3 : q % 3 = 1) :
    padicValNat 3 (ordTwistedE6 q) = 4 * padicValNat 3 (q - 1) + 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ q - 1 := by omega
  have hgcd : Nat.gcd 3 (q + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have hnz : ∀ n, n ≠ 0 → q ^ n - 1 ≠ 0 := fun n hn =>
    (Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)).ne'
  have hplus : ∀ n, padicValNat 3 (q ^ n + 1) = 0 := fun n =>
    padicValNat.eq_zero_of_not_dvd (by
      have : q ^ n % 3 = 1 := by rw [Nat.pow_mod, hq3]; simp
      omega)
  have hne : ∀ n, q ^ n + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hmin : q - 1 ≠ 0 := by omega
  have e12 : padicValNat 3 12 = 1 := by
    rw [show (12 : ℕ) = 3 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have e6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have e8 : padicValNat 3 8 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have e2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hnq : ¬ 3 ∣ q := by omega
  have hq0 : q ≠ 0 := by omega
  have h12 := hnz 12 (by norm_num)
  have h8 := hnz 8 (by norm_num)
  have h6 := hnz 6 (by norm_num)
  have h2' := hnz 2 (by norm_num)
  have h9 := hne 9
  have h5 := hne 5
  have h36 : q ^ 36 ≠ 0 := pow_ne_zero _ hq0
  unfold ordTwistedE6
  rw [hgcd, Nat.div_one]
  have A1 := mul_ne_zero h36 h12
  have A2 := mul_ne_zero A1 h9
  have A3 := mul_ne_zero A2 h8
  have A4 := mul_ne_zero A3 h6
  have A5 := mul_ne_zero A4 h5
  rw [padicValNat.mul A5 h2', padicValNat.mul A4 h5, padicValNat.mul A3 h6,
    padicValNat.mul A2 h8, padicValNat.mul A1 h9, padicValNat.mul h36 h12,
    padicValNat.pow q 36, padicValNat.eq_zero_of_not_dvd hnq, hplus, hplus,
    padicValNat_three_pow_sub_one hq h3 (by norm_num),
    padicValNat_three_pow_sub_one hq h3 (by norm_num),
    padicValNat_three_pow_sub_one hq h3 (by norm_num),
    padicValNat_three_pow_sub_one hq h3 (by norm_num),
    e12, e6, e8, e2]
  omega

open CFSG.HardMathSupport.Curtis.UnitaryLevi in
theorem exists_sylow_three_le_graphFixedRootMonomial_E6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hq3 : (ℓ ^ f) % 3 = 1) :
    ∃ P : Sylow 3 ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (P : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)) ≤
        (graphFixedRootMonomial TwistTag.E6 K σ).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  set q := ℓ ^ f with hqdef
  have hq : 1 < q := Nat.one_lt_pow (by omega) hℓ.one_lt
  have h3 : 3 ∣ q - 1 := by omega
  have hgcd : Nat.gcd 3 (q + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedRootMonomial_le TwistTag.E6 K σ)).toEquiv,
    card_graphFixedRootMonomial_E6, card_graphFixedRootGroup_E6 hℓ hf hK σ hσ,
    padicValNat_three_ordTwistedE6 hq hq3]
  have hT := CFSG.RankThree.Classical2.natCard_compatTorus_E6_mul hℓ hf hK hσ
  rw [← graphFixedRootTorus_eq_compatTorus hsurj, hgcd, mul_one] at hT
  rw [← hqdef] at hT
  rw [hT]
  have hv2 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q - 1) := by
    rw [padicValNat_three_pow_sub_one hq h3 (by norm_num),
      padicValNat.eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num), add_zero]
  have hz2 : q ^ 2 - 1 ≠ 0 := (Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)).ne'
  have hz1 : q - 1 ≠ 0 := by omega
  have e1152 : padicValNat 3 1152 = 2 := by
    rw [show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero 2 hz2) (pow_ne_zero 2 hz1)) (by norm_num), e1152,
    padicValNat.mul (pow_ne_zero 2 hz2) (pow_ne_zero 2 hz1),
    padicValNat.pow (q ^ 2 - 1) 2, padicValNat.pow (q - 1) 2, hv2]
  omega

end Twisted

end CFSG.HardMathSupport.Malle.E27Lie

end
