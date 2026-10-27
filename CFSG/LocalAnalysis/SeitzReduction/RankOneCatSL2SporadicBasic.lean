module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem two_pow_le_ordA_one {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ≤ Open.ordA 1 (2 ^ n) := by
  rw [RankThree.PartOne.S12K.ordA_one_eq hn]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 2 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem ordA_dvd_card_fixedSubgroup {J : Type} [Group J] [Finite J] {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : Open.ordA 1 (2 ^ n) ∣ Nat.card (fixedSubgroup τ) := by
  obtain ⟨-, D, -, hDm, -⟩ := h
  rw [← card_of_lieModel_PSL_two_two hDm]
  exact (card_quotient_dvd_card _).trans (card_subgroup_dvd_card D)

theorem two_le_of_catSL2Hyp {J : Type} [Group J] {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : 2 ≤ n := by
  obtain ⟨-, D, -, hDm, -⟩ := h
  exact two_le_of_lieModel_PSL_two_two hDm

theorem two_pow_le_of_catSL2Hyp {J : Type} [Group J] [Finite J] {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) {k : ℕ} (hk : 2 ^ k ∣ Nat.card (fixedSubgroup τ)) :
    2 ^ k ≤ 2 * (2 ^ n * n) := by
  have hn := two_le_of_catSL2Hyp h
  obtain ⟨-, D, hD, hDm, h2⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 hk
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQ
  have h1 := card_le_of_isPGroup_fixedSubgroup hD hDm h2 hQp
  have h3 : 2 ^ padicValNat 2 n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  rw [hQ] at h1
  calc 2 ^ k ≤ 2 * (2 ^ n * 2 ^ padicValNat 2 n) := h1
    _ ≤ 2 * (2 ^ n * n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h3)

theorem false_of_card_fixedSubgroup {J : Type} [Group J] [Finite J] {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) {c k B : ℕ} (hc : Nat.card (fixedSubgroup τ) = c) (hk : 2 ^ k ∣ c)
    (hB : c < 2 ^ B)
    (hcheck : ∀ m ∈ Finset.range B, 2 ≤ m → Open.ordA 1 (2 ^ m) ∣ c → 2 * (2 ^ m * m) < 2 ^ k) :
    False := by
  have hn := two_le_of_catSL2Hyp h
  have hdvd := ordA_dvd_card_fixedSubgroup h
  have hle := two_pow_le_of_catSL2Hyp h (k := k) (by rw [hc]; exact hk)
  rw [hc] at hdvd
  have hcpos : 0 < c := hc ▸ Nat.card_pos
  have hnB : n < B := by
    have h1 := Nat.le_of_dvd hcpos hdvd
    have h2 := two_pow_le_ordA_one (n := n) (by omega)
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (show 2 ^ n < 2 ^ B by omega)
  have := hcheck n (Finset.mem_range.mpr hnB) hn hdvd
  omega

theorem ordA_one_ne_of_check {x B n : ℕ} (hn : 2 ≤ n) (hB : x < 2 ^ B)
    (hcheck : ∀ m ∈ Finset.range B, 2 ≤ m → Open.ordA 1 (2 ^ m) ≠ x) :
    Open.ordA 1 (2 ^ n) ≠ x := by
  intro hx
  have h2 := two_pow_le_ordA_one (n := n) (by omega)
  have hnB : n < B :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (show 2 ^ n < 2 ^ B by omega)
  exact hcheck n (Finset.mem_range.mpr hnB) hn hx

theorem not_ordA_one_dvd_of_check {x B n : ℕ} (hn : 2 ≤ n) (hx : 0 < x) (hB : x < 2 ^ B)
    (hcheck : ∀ m ∈ Finset.range B, 2 ≤ m → ¬ Open.ordA 1 (2 ^ m) ∣ x) :
    ¬ Open.ordA 1 (2 ^ n) ∣ x := by
  intro hdvd
  have h1 := Nat.le_of_dvd hx hdvd
  have h2 := two_pow_le_ordA_one (n := n) (by omega)
  have hnB : n < B :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (show 2 ^ n < 2 ^ B by omega)
  exact hcheck n (Finset.mem_range.mpr hnB) hn hdvd

theorem autTwoBound_of_card {J : Type} [Group J] [Finite J] (hZ : center J = ⊥) {n a u k : ℕ}
    (hu : Odd u) (hJ : Nat.card J ∣ 2 ^ a * u) (hO : Nat.card (Outer J) ≤ k)
    (hlt : 2 ^ a * k < 2 * (2 ^ n) ^ 4) : AutTwoBound J n := by
  intro P hP
  have : Finite (MulAut J) :=
    Finite.of_injective (fun β : MulAut J => (β : J → J)) DFunLike.coe_injective
  have hcard := card_mulAut_of_center_eq_bot hZ
  have hOpos : 0 < Nat.card (Outer J) := Nat.card_pos
  have hdvd : Nat.card (MulAut J) ∣ 2 ^ a * Nat.card (Outer J) * u := by
    rw [hcard, mul_right_comm]
    exact Nat.mul_dvd_mul_right hJ _
  have h1 := card_le_of_isPGroup_of_card_dvd hP hu (by positivity) hdvd
  have h2 : 2 ^ a * Nat.card (Outer J) ≤ 2 ^ a * k := Nat.mul_le_mul_left _ hO
  omega

theorem autTwoBound_of_mulEquiv {J H : Type} [Group J] [Finite J] [Group H]
    (hJ : IsSimpleGroup J) (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* H) {n a u k : ℕ}
    (hu : Odd u) (hH : Nat.card H = 2 ^ a * u) (hO : Nat.card (Outer H) ≤ k)
    (hlt : 2 ^ a * k < 2 * (2 ^ n) ^ 4) : AutTwoBound J n :=
  autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna) hu
    (by rw [Nat.card_congr e.toEquiv, hH]) (Sporadic.Schreier.outer_card_le_of_equiv hO e) hlt

theorem lt_two_mul_pow_four_of_le {x m n : ℕ} (hmn : m ≤ n) (h : x < 2 * (2 ^ m) ^ 4) :
    x < 2 * (2 ^ n) ^ 4 :=
  lt_of_lt_of_le h (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hmn) 4))

theorem three_dvd_ordA_one {n : ℕ} (hn : 1 ≤ n) : 3 ∣ Open.ordA 1 (2 ^ n) := by
  rw [RankThree.PartOne.S12K.ordA_one_eq hn]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.pow_mod]
  norm_num

theorem three_dvd_card_of_lieModel {X : Type} [Group X] {D : Subgroup X} {n : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 n) : 3 ∣ Nat.card D := by
  have hn := two_le_of_lieModel_PSL_two_two hDm
  have h := three_dvd_ordA_one (n := n) (by omega)
  rw [← card_of_lieModel_PSL_two_two hDm] at h
  exact h.trans (card_quotient_dvd_card _)

end CFSG.SeitzReduction.RankOne
