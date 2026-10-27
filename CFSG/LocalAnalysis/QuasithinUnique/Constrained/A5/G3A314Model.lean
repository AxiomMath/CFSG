module

public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSmall
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem exists_noncomm_of_simple_of_not_prime {X : Type} [Group X] (hs : IsSimpleGroup X)
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc a b }
  exact h IsSimpleGroup.prime_card

theorem not_prime_mul_of_two_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬ (a * b).Prime :=
  Nat.not_prime_mul (by omega) (by omega)

theorem modelFacts_part1
    {X : Type} [Group X] [Finite X]
    (h : IsPSL 3 2 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 3 2 2 X ∨ IsSporadic .M22 X ∨ IsSporadic .M24 X ∨
      ∃ f, IsSz f X) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X ≠ 60 := by
  suffices H : IsSimpleGroup X ∧ ¬ (Nat.card X).Prime ∧ Nat.card X ≠ 60 from
    ⟨H.1, exists_noncomm_of_simple_of_not_prime H.1 H.2.1, H.2.2⟩
  rcases h with h | h | h | h | h | ⟨f, hf⟩
  · refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 h).2, ?_⟩
    rw [Id2519.card_of_psl_three_two h]
    norm_num
  · refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2, ?_⟩
    rw [Lin2.OddRank.card_L42 h]
    norm_num
  · refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 2 h).2, ?_⟩
    rw [Id2519.card_of_psl_three_four h]
    norm_num
  · obtain ⟨e⟩ := h
    have hM : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, hc]
    norm_num
  · obtain ⟨e⟩ := h
    have hM : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
      CFSG.Sporadic.Mathieu.card_M24
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, hc]
    norm_num
  · obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hf
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
    obtain ⟨-, -, hs⟩ := CFSG.LieType.Ree.suzuki_simple ha hK'
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
    have hq : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * a + 1) = q at hq
    have h1 : 2 ≤ q ^ 2 := by nlinarith
    have h2 : 2 ≤ (q - 1) * (q ^ 2 + 1) := by
      have : 7 ≤ q - 1 := by omega
      nlinarith
    have hN : q ^ 2 * (q - 1) * (q ^ 2 + 1) = q ^ 2 * ((q - 1) * (q ^ 2 + 1)) := by ring
    rw [hN]
    refine ⟨not_prime_mul_of_two_le h1 h2, ?_⟩
    have h3 : 64 ≤ q ^ 2 := by nlinarith
    have h4 : 64 * 2 ≤ q ^ 2 * ((q - 1) * (q ^ 2 + 1)) := Nat.mul_le_mul h3 h2
    omega

theorem modelFacts_part2 {n : ℕ} {X : Type} [Group X] [Finite X] (h : IsPSL 2 2 n X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h).2
  refine ⟨hs, exists_noncomm_of_simple_of_not_prime hs ?_⟩
  have hn2 : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, h22, -⟩, -⟩ := h
    by_contra hlt
    have hn1' : n = 1 := by omega
    subst hn1'
    exact h22 rfl
  have hcard := Lin2.OddRank.card_of_openPSL (n := 2) (p := 2) (f := n) (by norm_num) h
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
  rw [hgcd, Nat.div_one, show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton] at hcard
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hcard
  rw [hcard]
  refine not_prime_mul_of_two_le (by omega) ?_
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  omega

theorem modelFacts_part3 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {X : Type} [Group X] [Finite X]
    (h : IsPSL 2 p 1 X) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X = p * (p ^ 2 - 1) / 2 := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  have hcard := Lin2.OddRank.card_of_openPSL (n := 2) (p := p) (f := 1) (by norm_num) h
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (Nat.Odd.sub_odd hodd odd_one).two_dvd
  rw [hgcd, show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton] at hcard
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hcard
  refine ⟨hs, ?_, hcard⟩
  refine exists_noncomm_of_simple_of_not_prime hs ?_
  rw [hcard]
  have h2 : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨2 * k * k + 2 * k, by subst hk; ring_nf; omega⟩
  obtain ⟨m, hm⟩ := h2
  have hp2' : 16 ≤ p ^ 2 := by nlinarith
  have hm2 : 2 ≤ m := by omega
  have hdiv : p * (p ^ 2 - 1) / 2 = p * m := by
    rw [hm, show p * (2 * m) = 2 * (p * m) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hdiv]
  exact not_prime_mul_of_two_le (by omega) hm2

theorem a314ModelFacts :
    A314ModelFacts :=
  ⟨fun _ _ _ h => modelFacts_part1 h, fun _ _ _ _ h => modelFacts_part2 h,
    fun _ hp hp3 _ _ _ h => modelFacts_part3 hp hp3 h⟩

end CFSG.QuasithinUnique.A5.G3
