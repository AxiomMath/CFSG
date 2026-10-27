module

public import CFSG.LocalAnalysis.OddStandard.ResidualOddLie
public import CFSG.ClassicalInvolution.Orders.OddLieType
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.OddStandard.ChildOddLie

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace OddLieNotL28

theorem lt_of_div_eq_five_hundred_four {a d D : ℕ} (hd : 0 < d) (hD : d ≤ D)
    (h : a / d = 504) : a < 505 * D := by
  have h1 := Nat.lt_mul_div_succ a hd
  rw [h] at h1
  nlinarith

theorem pow_sub_one_pos {q i : ℕ} (hq : 3 ≤ q) (hi : i ≠ 0) : 0 < q ^ i - 1 := by
  have := Nat.le_self_pow hi q
  omega

theorem le_prod_of_mem {s : Finset ℕ} {f : ℕ → ℕ} (hpos : ∀ i ∈ s, 0 < f i) {j : ℕ}
    (hj : j ∈ s) : f j ≤ ∏ i ∈ s, f i :=
  Nat.le_of_dvd (Finset.prod_pos hpos) (Finset.dvd_prod_of_mem f hj)

theorem le_mul_of_pos_of_le {a b c : ℕ} (hb : 0 < b) (h : c ≤ a) : c ≤ a * b :=
  h.trans (Nat.le_mul_of_pos_right a hb)

theorem sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  simpa using Nat.sq_sub_sq q 1

theorem three_pow_six_le_pow_triangle {q n : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n) :
    3 ^ 6 ≤ q ^ (n * (n + 1) / 2) := by
  have h : 12 ≤ n * (n + 1) := by nlinarith
  exact (Nat.pow_le_pow_left hq 6).trans (Nat.pow_le_pow_right (by omega) (by omega))

theorem false_of_pow_le {q e N d D : ℕ} (hq : 3 ≤ q) (he : 505 * D ≤ 3 ^ e) (hd : 0 < d)
    (hD : d ≤ D) (key : q ^ e ≤ N) (h : N / d = 504) : False := by
  have h1 := lt_of_div_eq_five_hundred_four hd hD h
  have h2 : 3 ^ e ≤ q ^ e := Nat.pow_le_pow_left hq e
  omega

theorem false_of_pow_le_self {q e N : ℕ} (hq : 3 ≤ q) (he : 505 ≤ 3 ^ e) (key : q ^ e ≤ N)
    (h : N = 504) : False := by
  have h2 : 3 ^ e ≤ q ^ e := Nat.pow_le_pow_left hq e
  omega

theorem ordA_ne {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (hn : 1 ≤ n) : ordA n q ≠ 504 := by
  intro h
  unfold ordA at h
  have hgcd : 0 < Nat.gcd (n + 1) (q - 1) := Nat.gcd_pos_of_pos_right _ (by omega)
  have hle : Nat.gcd (n + 1) (q - 1) ≤ q - 1 := Nat.gcd_le_right _ (by omega)
  have hlt := lt_of_div_eq_five_hundred_four hgcd hle h
  have hpos : ∀ i ∈ Finset.Icc 2 (n + 1), 0 < q ^ i - 1 := fun i hi =>
    pow_sub_one_pos hq (by have := (Finset.mem_Icc.1 hi).1; omega)
  have hP : q ^ 2 - 1 ≤ ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) :=
    le_prod_of_mem hpos (j := 2) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hnum := Nat.mul_le_mul_left (q ^ (n * (n + 1) / 2)) hP
  rw [sq_sub_one] at hnum
  have hlt' : q ^ (n * (n + 1) / 2) * (q + 1) < 505 := by
    have h2 : (q ^ (n * (n + 1) / 2) * (q + 1)) * (q - 1) < 505 * (q - 1) := by
      calc (q ^ (n * (n + 1) / 2) * (q + 1)) * (q - 1)
          = q ^ (n * (n + 1) / 2) * ((q + 1) * (q - 1)) := by ring
        _ < 505 * (q - 1) := lt_of_le_of_lt hnum hlt
    exact Nat.lt_of_mul_lt_mul_right h2
  have hqpow : q ≤ q ^ (n * (n + 1) / 2) := by
    apply Nat.le_self_pow
    have : 2 ≤ n * (n + 1) := by nlinarith
    omega
  by_cases hn3 : 3 ≤ n
  · exfalso
    have h1 := three_pow_six_le_pow_triangle hq hn3
    have h2 : q ^ (n * (n + 1) / 2) ≤ q ^ (n * (n + 1) / 2) * (q + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have h4 : q * (q + 1) ≤ q ^ (n * (n + 1) / 2) * (q + 1) :=
      Nat.mul_le_mul_right (q + 1) hqpow
    have hq21 : q ≤ 21 := by nlinarith
    have hn2 : n ≤ 2 := by omega
    clear hlt hnum hP hpos hlt' hqpow h4 hle hgcd
    interval_cases n <;> interval_cases q <;>
      first | (revert h; decide) | exact absurd hodd (by decide)

theorem ordTwistedA_ne {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) : ordTwistedA n q ≠ 504 := by
  intro h
  unfold ordTwistedA at h
  have hgcd : 0 < Nat.gcd (n + 1) (q + 1) := Nat.gcd_pos_of_pos_right _ (by omega)
  have hle : Nat.gcd (n + 1) (q + 1) ≤ q + 1 := Nat.gcd_le_right _ (by omega)
  have hlt := lt_of_div_eq_five_hundred_four hgcd hle h
  have hpos : ∀ i ∈ Finset.Icc 2 (n + 1), 0 < ((q : ℤ) ^ i - (-1) ^ i).toNat := fun i hi => by
    have hi2 := (Finset.mem_Icc.1 hi).1
    have h1 : 3 ≤ q ^ i := hq.trans (Nat.le_self_pow (by omega) q)
    have h2 : (3 : ℤ) ≤ (q : ℤ) ^ i := by exact_mod_cast h1
    rcases neg_one_pow_eq_or ℤ i with h3 | h3 <;> rw [h3] <;> omega
  have e2 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  have hP : q ^ 2 - 1 ≤ ∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat := by
    rw [← e2]
    exact le_prod_of_mem hpos (j := 2) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hnum := Nat.mul_le_mul_left (q ^ (n * (n + 1) / 2)) hP
  rw [sq_sub_one] at hnum
  have hlt' : q ^ (n * (n + 1) / 2) * (q - 1) < 505 := by
    have h2 : (q ^ (n * (n + 1) / 2) * (q - 1)) * (q + 1) < 505 * (q + 1) := by
      calc (q ^ (n * (n + 1) / 2) * (q - 1)) * (q + 1)
          = q ^ (n * (n + 1) / 2) * ((q + 1) * (q - 1)) := by ring
        _ < 505 * (q + 1) := lt_of_le_of_lt hnum hlt
    exact Nat.lt_of_mul_lt_mul_right h2
  by_cases hn3 : 3 ≤ n
  · exfalso
    have h1 := three_pow_six_le_pow_triangle hq hn3
    have h2 : q ^ (n * (n + 1) / 2) ≤ q ^ (n * (n + 1) / 2) * (q - 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hn2 : n = 2 := by omega
    subst hn2
    have h4 : q ^ 3 * (q - 1) < 505 := by simpa using hlt'
    have hq5 : q ≤ 5 := by
      by_contra hcon
      have h5 : 6 ≤ q := by omega
      have h6 : 6 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h5 3
      have h7 : 5 ≤ q - 1 := by omega
      have h8 := Nat.mul_le_mul h6 h7
      omega
    clear hlt hnum hP hpos e2 hlt' h4 hle hgcd
    interval_cases q <;> revert h <;> decide

theorem ordBC_ne {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) : ordBC n q ≠ 504 := by
  intro h
  unfold ordBC at h
  have hlt := lt_of_div_eq_five_hundred_four (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 2))
    (Nat.gcd_le_left _ (by norm_num : 0 < 2)) h
  have hpos : ∀ i ∈ Finset.Icc 1 n, 0 < q ^ (2 * i) - 1 := fun i hi =>
    pow_sub_one_pos hq (by have := (Finset.mem_Icc.1 hi).1; omega)
  have hP : q ^ (2 * n) - 1 ≤ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    le_prod_of_mem hpos (j := n) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  have h1 := Nat.mul_le_mul_left (q ^ (n * n)) hP
  have h2 : 4 ≤ n * n := by nlinarith
  have h3 : q ^ 4 ≤ q ^ (n * n) := Nat.pow_le_pow_right (by omega) h2
  have h4 : q ^ 4 ≤ q ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h6 : (3 ^ 4) * (3 ^ 4 - 1) ≤ q ^ (n * n) * (q ^ (2 * n) - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem false_of_orthogonal {q n X d : ℕ} (hq : 3 ≤ q) (hn : 4 ≤ n) (hX : 0 < X) (hd : 0 < d)
    (hD : d ≤ 4)
    (h : q ^ (n * (n - 1)) * X * (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) / d = 504) :
    False := by
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    Finset.prod_pos fun i hi => pow_sub_one_pos hq (by have := (Finset.mem_Icc.1 hi).1; omega)
  have h3 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have h4 : q ^ 12 ≤ q ^ (n * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  exact false_of_pow_le hq (D := 4) (e := 12) (by norm_num) hd hD
    (h4.trans (le_mul_of_pos_of_le hP (le_mul_of_pos_of_le hX le_rfl))) h

theorem ordD_ne {q n : ℕ} (hq : 3 ≤ q) (hn : 4 ≤ n) : ordD n q ≠ 504 := fun h =>
  false_of_orthogonal hq hn (pow_sub_one_pos hq (by omega))
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num)) h

theorem ordTwistedD_ne {q n : ℕ} (hq : 3 ≤ q) (hn : 4 ≤ n) : ordTwistedD n q ≠ 504 := fun h =>
  false_of_orthogonal hq hn (Nat.succ_pos _)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num)) h

theorem ordE6_ne {q : ℕ} (hq : 3 ≤ q) : ordE6 q ≠ 504 := by
  intro h
  unfold ordE6 at h
  refine false_of_pow_le hq (D := 3) (e := 36) (by norm_num)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num)) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
    (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ le_rfl)))))
  all_goals exact pow_sub_one_pos hq (by norm_num)

theorem ordTwistedE6_ne {q : ℕ} (hq : 3 ≤ q) : ordTwistedE6 q ≠ 504 := by
  intro h
  unfold ordTwistedE6 at h
  refine false_of_pow_le hq (D := 3) (e := 36) (by norm_num)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num)) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
    (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ le_rfl)))))
  all_goals first | exact pow_sub_one_pos hq (by norm_num) | positivity

theorem ordE7_ne {q : ℕ} (hq : 3 ≤ q) : ordE7 q ≠ 504 := by
  intro h
  unfold ordE7 at h
  refine false_of_pow_le hq (D := 2) (e := 63) (by norm_num)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num)) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
    (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
      (le_mul_of_pos_of_le ?_ le_rfl))))))
  all_goals exact pow_sub_one_pos hq (by norm_num)

theorem ordE8_ne {q : ℕ} (hq : 3 ≤ q) : ordE8 q ≠ 504 := by
  intro h
  unfold ordE8 at h
  refine false_of_pow_le_self hq (e := 120) (by norm_num) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
    (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
      (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ le_rfl)))))))
  all_goals exact pow_sub_one_pos hq (by norm_num)

theorem ordF4_ne {q : ℕ} (hq : 3 ≤ q) : ordF4 q ≠ 504 := by
  intro h
  unfold ordF4 at h
  refine false_of_pow_le_self hq (e := 24) (by norm_num) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_
    (le_mul_of_pos_of_le ?_ le_rfl)))
  all_goals exact pow_sub_one_pos hq (by norm_num)

theorem ordG2_ne {q : ℕ} (hq : 3 ≤ q) : ordG2 q ≠ 504 := by
  intro h
  unfold ordG2 at h
  refine false_of_pow_le_self hq (e := 6) (by norm_num) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ le_rfl)
  all_goals exact pow_sub_one_pos hq (by norm_num)

theorem ordTrialityD4_ne {q : ℕ} (hq : 3 ≤ q) : ordTrialityD4 q ≠ 504 := by
  intro h
  unfold ordTrialityD4 at h
  refine false_of_pow_le_self hq (e := 12) (by norm_num) ?_ h
  refine le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ (le_mul_of_pos_of_le ?_ le_rfl))
  all_goals first | exact pow_sub_one_pos hq (by norm_num) | positivity

theorem ordRee_ne {q : ℕ} (hq : 27 ≤ q) : ordRee q ≠ 504 := by
  intro h
  unfold ordRee at h
  have h1 : 0 < q - 1 := by omega
  have h2 : 3 ^ 9 ≤ q ^ 3 := by
    calc 3 ^ 9 = 27 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h3 : q ^ 3 ≤ q ^ 3 * (q ^ 3 + 1) * (q - 1) :=
    le_mul_of_pos_of_le h1 (le_mul_of_pos_of_le (Nat.succ_pos _) le_rfl)
  omega

theorem five_hundred_four_not_mem_lieOrdersOver {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    504 ∉ lieOrdersOver q := by
  rintro (((((⟨n, hn, h⟩ | ⟨n, hn, h⟩) | ⟨n, hn, h⟩) | ⟨n, hn, h⟩) | ⟨n, hn, h⟩) | h)
  · exact ordA_ne hq hodd hn h.symm
  · exact ordTwistedA_ne hq hn h.symm
  · exact ordBC_ne hq hn h.symm
  · exact ordD_ne hq hn h.symm
  · exact ordTwistedD_ne hq hn h.symm
  · rcases h with h | h | h | h | h | h | h
    · exact ordE6_ne hq h.symm
    · exact ordTwistedE6_ne hq h.symm
    · exact ordE7_ne hq h.symm
    · exact ordE8_ne hq h.symm
    · exact ordF4_ne hq h.symm
    · exact ordG2_ne hq h.symm
    · exact ordTrialityD4_ne hq h.symm

end OddLieNotL28

theorem five_hundred_four_not_mem_lieOrdersChar (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    504 ∉ lieOrdersChar p := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rintro (((⟨k, hk, h⟩ | ⟨hp', -⟩) | ⟨hp', k, hk, h⟩) | ⟨hp', -⟩)
  · refine OddLieNotL28.five_hundred_four_not_mem_lieOrdersOver (q := p ^ k)
      (hp3.trans (Nat.le_self_pow (by omega) p)) ((hp.odd_of_ne_two hp2).pow) h
  · exact hp2 hp'
  · subst hp'
    refine OddLieNotL28.ordRee_ne (q := 3 ^ (2 * k + 1)) ?_ h.symm
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact hp2 hp'

section Consumers


theorem not_statedPSL_two_eight_of_oddLieType {Q : Type} [Group Q] (h : OddLieType Q) :
    ¬ Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 2 3 := by
  intro h8
  obtain ⟨p, hp, hp2, hmem⟩ := ClassicalInvolution.card_mem_lieOrdersChar_of_oddLieType h
  rw [Residual.card_eq_of_statedPSL_two_eight h8] at hmem
  exact five_hundred_four_not_mem_lieOrdersChar p hp hp2 hmem

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem oddLie_rankTwo_noL28
    (hOdd : ComponentClassification.RankTwoStandard.RankTwoOddLieStandard)
    (hS : StandardSetting G L) (hlie : OddLieType (L ⧸ center L))
    (h5 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)))
    (h6 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)))
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))) : False := by
  have hH : ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
    ⟨hS.kProper, hS.standard, hS.not_normal, hrank⟩
  have hO : Open.standardComponentOddCore G = ⊥ := hS.oddCore_eq_bot
  exact hOdd G L hH hO ⟨hlie, h5, h6, not_statedPSL_two_eight_of_oddLieType hlie⟩

end Branches

theorem oddLieResidual_of_cyclic_noL28
    (hOdd : ComponentClassification.RankTwoStandard.RankTwoOddLieStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : OddLieCyclicResidual) : OddLieResidual := by
  intro G _ _ L hS hlie h5 h6
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with hrank | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exact (oddLie_rankTwo_noL28 hOdd hS hlie h5 h6 hrank).elim
  · exact hCyc G L hS hlie h5 h6 S hcyc
  · rcases quaternion_oddLie_or_M12 hCIT hS S hr hq with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem oddLieResidual_of_inputs_noL28
    (hOdd : ComponentClassification.RankTwoStandard.RankTwoOddLieStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    (hCyc : OddLieCyclicBeyondHSF) : OddLieResidual :=
  oddLieResidual_of_cyclic_noL28 hOdd hCIT (oddLieCyclicResidual_of_beyondHSF hHSF hCyc)

end Consumers

end CFSG.OddStandard
