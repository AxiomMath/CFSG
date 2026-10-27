module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UMult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UDerive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct

theorem twP_five_mod_four {m : ℕ} (hm : 1 ≤ m) : twP 5 (2 ^ m) % 4 = 3 := by
  have hd : ∀ j, 2 ≤ j → (2 ^ m) ^ j % 4 = 0 := fun j hj =>
    Nat.mod_eq_zero_of_dvd (four_dvd_pow_two_mul hm hj)
  have p : ∀ j, 2 ≤ j → 1 ≤ (2 ^ m) ^ j := fun j _ => Nat.one_le_pow _ _ (by positivity)
  have e0 : ∀ j, 2 ≤ j → ((2 ^ m) ^ j - 1) ≡ 3 [MOD 4] := fun j hj => by
    have := hd j hj; have := p j hj; unfold Nat.ModEq; omega
  have e1 : ∀ j, 2 ≤ j → ((2 ^ m) ^ j + 1) ≡ 1 [MOD 4] := fun j hj => by
    have := hd j hj; unfold Nat.ModEq; omega
  have hexp : twP 5 (2 ^ m) = ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1) *
      ((2 ^ m) ^ 5 + 1) * ((2 ^ m) ^ 6 - 1) := by
    unfold twP
    simp [Finset.prod_Icc_succ_top, Nat.even_iff]
  rw [hexp]
  have := ((((e0 2 (by norm_num)).mul (e1 3 (by norm_num))).mul (e0 4 (by norm_num))).mul
    (e1 5 (by norm_num))).mul (e0 6 (by norm_num))
  unfold Nat.ModEq at this
  rw [this]

theorem g2_ne_U6_all {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    orderG2 (2 ^ n) ≠ orderTwistedA 5 (2 ^ m) := by
  intro hh
  have hO₁ : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
    (odd_pow_two_pow_sub_one hn (by norm_num)).mul (odd_pow_two_pow_sub_one hn (by norm_num))
  have e₁ : orderG2 (2 ^ n) = 2 ^ (n * 6) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
    simp only [orderG2]
    rw [pow_mul 2 n 6, mul_assoc]
  have hg := orderTwistedA_mul_gcd (r := 5) (m := m) (by norm_num) hm
  rw [← hh, e₁] at hg
  have hg' : 2 ^ (n * 6) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) * Nat.gcd (5 + 1) (2 ^ m + 1)) =
      2 ^ (m * (5 * (5 + 1) / 2)) * twP 5 (2 ^ m) := by rw [← mul_assoc, hg]
  obtain ⟨h6, hO⟩ := two_pow_mul_odd_inj (hO₁.mul (odd_gcd_twisted hm)) (odd_twP hm) hg'
  norm_num at h6
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have h3 : ¬ 3 ∣ 2 ^ m + 1 := by
    rw [hk, pow_mul]
    intro h
    have h1 : (2 ^ 2) ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  have hgcd : Nat.gcd (5 + 1) (2 ^ m + 1) = 1 := by
    have hodd := odd_gcd_twisted (r := 5) hm
    have hd6 : Nat.gcd (5 + 1) (2 ^ m + 1) ∣ 3 * 2 := Nat.gcd_dvd_left _ _
    have h2 : Nat.Coprime (Nat.gcd (5 + 1) (2 ^ m + 1)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h))
    have hd3 : Nat.gcd (5 + 1) (2 ^ m + 1) ∣ 3 := h2.dvd_of_dvd_mul_right hd6
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
    · exact h
    · exfalso
      apply h3
      rw [← h]
      exact Nat.gcd_dvd_right _ _
  rw [hgcd, mul_one] at hO
  have hd : ∀ j, 2 ≤ j → (2 ^ n) ^ j % 4 = 0 := fun j hj =>
    Nat.mod_eq_zero_of_dvd (four_dvd_pow_two_mul hn hj)
  have p : ∀ j, 2 ≤ j → 1 ≤ (2 ^ n) ^ j := fun j _ => Nat.one_le_pow _ _ (by positivity)
  have h61 : ((2 ^ n) ^ 6 - 1) ≡ 3 [MOD 4] := by
    have := hd 6 (by norm_num); have := p 6 (by norm_num); unfold Nat.ModEq; omega
  have h21 : ((2 ^ n) ^ 2 - 1) ≡ 3 [MOD 4] := by
    have := hd 2 (by norm_num); have := p 2 (by norm_num); unfold Nat.ModEq; omega
  have hmod := h61.mul h21
  unfold Nat.ModEq at hmod
  have hmodT := twP_five_mod_four hm
  rw [← hO] at hmodT
  rw [hmodT] at hmod
  norm_num at hmod


theorem t266G2NotU6_of_bridge (hb : CatDistinct.OrderBridge)
    (hfin : ∀ idx : TauCeti.ValidLieTypeIndex, Finite idx.Group) : T266G2NotU6 := by
  intro S _ n m h1 h2
  obtain ⟨q, hv, hq2, hqn, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1.lieIndex_isG2n h1
  obtain ⟨q', hv', hq2', hqn', ⟨e'⟩⟩ := lieIndex_isU6n h2
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  have hn : 1 ≤ n := by have := q.exponent_pos; omega
  have hm : 1 ≤ m := by have := q'.exponent_pos; omega
  have hc1 : Nat.card S = orderG2 (2 ^ n) := by
    rw [hb ⟨.G2 q, hv⟩ S ⟨e⟩]
    show orderG2 q.card = _
    rw [TauCeti.PrimePower.card_def, hq2, hqn]
  have hc2 : Nat.card S = orderTwistedA 5 (2 ^ m) := by
    rw [hb ⟨.twistedA 5 q', hv'⟩ S ⟨e'⟩]
    show orderTwistedA 5 q'.card = _
    rw [TauCeti.PrimePower.card_def, hq2', hqn']
  exact g2_ne_U6_all hn hm (hc1.symm.trans hc2)

section Holds


theorem t266G2NotU6_holds : T266G2NotU6 :=
  t266G2NotU6_of_bridge CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    (fun idx => (CFSG.Assembly.lie_finite_simple idx).1)

theorem i266R_of_facts_holds (G : Type) [Group G] [Finite G]
    (hInn : ∀ n, T266G2Inn n) (hOdd : ∀ n, T266G2Odd n) (hLayer : ∀ n, T266G2Layer n)
    (hKey : ∀ n, T266G2Key n) (hU6 : ∀ n, T266U6Fact n) : I266AtR G :=
  i266R_of_facts G hInn hOdd hLayer hKey t266G2NotU6_holds hU6

end Holds

end CFSG.LocalAnalysis.GLTheoremA.T266

end
