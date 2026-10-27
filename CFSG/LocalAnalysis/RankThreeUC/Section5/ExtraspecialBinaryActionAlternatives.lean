module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialDimensionBoundLeTwoMulModuleRank
public import CFSG.LocalAnalysis.RankThreeUC.Section5.HalfExponentBoundLeExtraspecialWidth
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

private theorem uc58_bern (j : ℕ) : 2 * j + 1 ≤ 3 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; omega

private theorem uc58_arith (p n m M dO : ℕ) (hp : 3 ≤ p) (hd : 2 ≤ dO) (hm : 2 ≤ m)
    (hn : 2 ^ (m - 1) ≤ n) (h1 : p ^ (n - 1) * (p - 1) * dO ≤ 2 * M) (h2 : M ≤ 2 * m + 1) :
    False := by
  have hmn : m ≤ n := by
    have := Nat.lt_two_pow_self (n := m - 1)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hj : m - 1 ≤ j := by omega
  have hpj : 3 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp j
  have hb := uc58_bern j
  have h3 : 2 ≤ p - 1 := by omega
  have hA : 2 * 3 ^ j ≤ p ^ j * (p - 1) := by
    calc 2 * 3 ^ j = 3 ^ j * 2 := by ring
      _ ≤ p ^ j * (p - 1) := Nat.mul_le_mul hpj h3
  have hB : p ^ j * (p - 1) * 2 ≤ p ^ j * (p - 1) * dO := Nat.mul_le_mul_left _ hd
  generalize p ^ j * (p - 1) * dO = X at *
  generalize p ^ j * (p - 1) = A at *
  omega

theorem extraspecialBinaryActionAlternatives {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hP : CFSG.IsExtraspecialPGroup p ↥P) :
    ExtraspecialBinaryActionAlternatives G p P B e ρ := by
  by_contra hc
  have hcx : ExtraspecialBinaryActionCounterexample G p P T B e ρ := ⟨h51, h53, hP, hc⟩
  obtain ⟨-, k, hk⟩ := special_commutator_center_eq_centralizer_and_exponent_power_two hcx
  obtain ⟨hcent, hcyc, -⟩ := centralizer_eq_center_and_actor_cyclic_and_primeCore_cyclic hcx
  have hM : moduleM ρ ≤ e + 1 := by
    by_contra hlt
    push Not at hlt
    apply hc
    unfold ExtraspecialBinaryActionAlternatives
    exact ⟨⟨k, hk⟩, Or.inr ⟨hcyc, hcent, hlt⟩⟩
  have hS := h51.setting
  have hp := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨r, hr⟩ := hS.odd
    omega
  have he4 : 4 ≤ e ∧ e % 2 = 0 := by
    have h2 := h51.two_lt
    rcases k with _ | _ | k
    · simp [hk] at h2
    · simp [hk] at h2
    · rw [hk, pow_succ, pow_succ]
      have := Nat.one_le_two_pow (n := k)
      omega
  obtain ⟨n, hn⟩ := CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder.exists_width P p
    hS.exponent hS.class_le_two hP
  have h1 := extraspecial_dimension_bound_le_two_mul_moduleRank hcx n hn
  have h14 := half_exponent_bound_le_extraspecial_width hcx n hn
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m := ⟨e / 2, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have e1 : ((2 * m : ℕ) : ℝ) / 2 - 1 = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e1, Real.rpow_natCast] at h14
  have h15 : 2 ^ (m - 1) ≤ n := by exact_mod_cast h14
  have hd2 : 2 ≤ binaryMultiplicativeOrder p := by
    unfold binaryMultiplicativeOrder
    have hne1 : (2 : ZMod p) ≠ 1 := by
      intro h
      have h' : ((1 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) := by
        push_cast; exact h.symm
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h'
      omega
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'
      omega
    have hpos : orderOf (2 : ZMod p) ≠ 0 := by
      intro h
      rw [orderOf_eq_zero_iff'] at h
      exact h (p - 1) (by omega) (ZMod.pow_card_sub_one_eq_one h2ne)
    have hne : orderOf (2 : ZMod p) ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
    omega
  exact uc58_arith p n m (moduleM ρ) (binaryMultiplicativeOrder p) hp3 hd2 hm2 h15 h1 hM

end Section5
end CFSG.LocalAnalysis.RankThreeUC
