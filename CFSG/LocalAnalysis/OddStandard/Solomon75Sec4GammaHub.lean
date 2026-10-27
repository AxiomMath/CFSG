module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Order

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

theorem padicValNat_two_choose_top {n a : ℕ} (h1 : 2 ^ a ≤ n) (h2 : n < 2 ^ (a + 1)) :
    padicValNat 2 (n.choose (2 ^ a)) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 ^ a := ⟨n - 2 ^ a, by omega⟩
  have hr : r < 2 ^ a := by
    have : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by ring
    omega
  have hb : Nat.log 2 (r + 2 ^ a) < a + 2 := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    have : 2 ^ (a + 2) = 2 ^ (a + 1) + 2 ^ (a + 1) := by ring
    omega
  rw [padicValNat_choose' hb]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  rw [Finset.mem_Ico] at hi
  have hpos : 0 < 2 ^ i := by positivity
  rcases Nat.lt_or_ge a i with hai | hai
  · have hlt : 2 ^ a < 2 ^ i := Nat.pow_lt_pow_right (by norm_num) hai
    have hle : 2 ^ (a + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hai
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (lt_trans hr hlt)]
    omega
  · have hdvd : 2 ^ i ∣ 2 ^ a := Nat.pow_dvd_pow 2 hai
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    have := Nat.mod_lt r hpos
    omega

theorem padicValNat_two_factorial_top {n a : ℕ} (ha : 1 ≤ a) (h1 : 2 ^ a ≤ n)
    (h2 : n < 2 ^ (a + 1)) :
    padicValNat 2 n.factorial =
      2 ^ (a - 1) + padicValNat 2 (2 ^ (a - 1)).factorial +
        padicValNat 2 (n - 2 ^ a).factorial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : 2 ^ a = 2 * 2 ^ (a - 1) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hc := padicValNat_two_choose_top h1 h2
  have h := Nat.choose_mul_factorial_mul_factorial h1
  have hc0 : n.choose (2 ^ a) ≠ 0 := (Nat.choose_pos h1).ne'
  have h2a : (2 ^ a).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hna : (n - 2 ^ a).factorial ≠ 0 := Nat.factorial_ne_zero _
  have e : padicValNat 2 n.factorial = padicValNat 2 (n.choose (2 ^ a)) +
      padicValNat 2 (2 ^ a).factorial + padicValNat 2 (n - 2 ^ a).factorial := by
    rw [← h, padicValNat.mul (mul_ne_zero hc0 h2a) hna, padicValNat.mul hc0 h2a]
  have e2 : padicValNat 2 (2 ^ a).factorial =
      padicValNat 2 (2 ^ (a - 1)).factorial + 2 ^ (a - 1) := by
    rw [hk]
    exact padicValNat_factorial_mul _
  omega

theorem exists_fpf_involution {n a : ℕ} (ha : 2 ≤ a) (h : 2 ^ a ≤ n) :
    ∃ c : Perm (Fin n), c * c = 1 ∧ sign c = 1 ∧ c.support.card = 2 ^ a := by
  have hk2 : 2 * 2 ^ (a - 1) = 2 ^ a := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hkev : Even (2 ^ (a - 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
  obtain ⟨c, hc⟩ := (Equiv.Perm.exists_with_cycleType_iff (m := Multiset.replicate (2 ^ (a - 1)) 2)
    (Fin n)).2 ⟨by
      simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]
      omega, fun x hx => by rw [Multiset.eq_of_mem_replicate hx]⟩
  have hcard : c.support.card = 2 ^ a := by
    rw [← Perm.sum_cycleType, hc]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    omega
  refine ⟨c, ?_, ?_, hcard⟩
  · have h1 : orderOf c ∣ 2 := by
      rw [← Perm.lcm_cycleType]
      apply Multiset.lcm_dvd.2
      intro x hx
      rw [hc] at hx
      rw [Multiset.eq_of_mem_replicate hx]
    have := orderOf_dvd_iff_pow_eq_one.1 h1
    simpa [pow_two] using this
  · rw [sign_of_cycleType, hc]
    simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
    have : 2 ^ (a - 1) * 2 + 2 ^ (a - 1) = 2 ^ (a - 1) * 3 := by ring
    rw [this]
    exact Even.neg_one_pow (hkev.mul_right 3)

theorem padicValNat_card_centralizer_alt {n a : ℕ} (ha : 2 ≤ a) (h1 : 2 ^ a ≤ n)
    (h2 : n < 2 ^ (a + 1)) {c : Perm (Fin n)} (hc2 : c * c = 1)
    (hcard : c.support.card = 2 ^ a) :
    padicValNat 2 (Nat.card ↥(centralizer ({c} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)))
      + 1 = padicValNat 2 n.factorial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 : 2 * 2 ^ (a - 1) = 2 ^ a := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hk1 : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  have hD := card_centralizer_inf_alternating hc2 (k := 2 ^ (a - 1)) (by rw [hcard, hk2]) hk1
  set N := Nat.card ↥(centralizer ({c} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) with hN
  have hNpos : 0 < N := Nat.card_pos
  have hne1 : (n - 2 * 2 ^ (a - 1)).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hne2 : (2 ^ (2 ^ (a - 1)) * (2 ^ (a - 1)).factorial) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero _)
  have hne3 : (2 ^ (a - 1)).factorial ≠ 0 := Nat.factorial_ne_zero _
  have e1 : padicValNat 2 (N * 2) = padicValNat 2 N + 1 := by
    rw [padicValNat.mul hNpos.ne' two_ne_zero, padicValNat.self (by norm_num)]
  have e2 : padicValNat 2 ((n - 2 * 2 ^ (a - 1)).factorial *
      (2 ^ (2 ^ (a - 1)) * (2 ^ (a - 1)).factorial)) =
      padicValNat 2 (n - 2 * 2 ^ (a - 1)).factorial +
        (2 ^ (a - 1) + padicValNat 2 (2 ^ (a - 1)).factorial) := by
    rw [padicValNat.mul hne1 hne2, padicValNat.mul (pow_ne_zero _ two_ne_zero) hne3,
      padicValNat.prime_pow]
  have e3 := padicValNat_two_factorial_top (n := n) (a := a) (by omega) h1 h2
  rw [hD, e2] at e1
  rw [← hk2] at e3
  omega

theorem exists_hub {n : ℕ} (hn : 8 ≤ n) {K : Type} [Group K] [Finite K] (C : CoverSetup n K) :
    ∃ (S : Sylow 2 K) (y : K), y ∈ (S : Subgroup K) ∧ y * y = 1 ∧ y ∉ center K ∧
      ∀ s ∈ (S : Subgroup K), ⁅s, y⁆ ∈ center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := Nat.log 2 n with ha
  have ha3 : 3 ≤ a := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have h1 : 2 ^ a ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  obtain ⟨c, hc2, hcs, hcard⟩ := exists_fpf_involution (by omega : 2 ≤ a) h1
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, Perm.support_one, Finset.card_empty] at hcard
    have := pow_pos (show (0 : ℕ) < 2 by norm_num) a
    omega
  set D : Subgroup (Perm (Fin n)) :=
    centralizer ({c} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) with hD
  have hcD : c ∈ D := ⟨mem_centralizer_singleton_iff.2 rfl, Perm.mem_alternatingGroup.2 hcs⟩
  have hval := padicValNat_card_centralizer_alt (by omega : 2 ≤ a) h1 h2 hc2 hcard
  have hKcard : Nat.card K = n.factorial := card_K_eq (by omega) C.hX
  set c' : ↥D := ⟨c, hcD⟩ with hc'
  have hc'2 : c' * c' = 1 := Subtype.ext hc2
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hpg : IsPGroup 2 (Subgroup.zpowers c') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hc'2) hc'1]
    simp
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  set P' : Subgroup (Perm (Fin n)) := (P : Subgroup ↥D).map D.subtype with hP'
  have hP'A : P' ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2.2
  have hP'c : ∀ x ∈ P', x * c = c * x := by
    rintro _ ⟨y, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 y.2.1
  have hcP' : c ∈ P' := ⟨c', hP (Subgroup.mem_zpowers c'), rfl⟩
  have hP'card : Nat.card P' = 2 ^ (Nat.card D).factorization 2 := by
    rw [hP', Subgroup.card_map_of_injective D.subtype_injective, P.card_eq_multiplicity]
  have hS₀card : Nat.card (P'.comap C.ρ) = 2 ^ (Nat.card K).factorization 2 := by
    rw [C.card_comap hP'A, hP'card, Nat.factorization_def _ Nat.prime_two,
      Nat.factorization_def _ Nat.prime_two, hKcard, ← hval, pow_succ]
    ring
  set S : Sylow 2 K := Sylow.ofCard (P'.comap C.ρ) hS₀card with hS
  obtain ⟨y, hy⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hP'A hcP'))
  have hyρ : C.ρ y * C.ρ y = 1 := by rw [hy]; exact hc2
  have h8 : 8 ∣ (C.ρ y).support.card := by
    rw [hy, hcard]
    exact (Nat.pow_dvd_pow 2 ha3)
  refine ⟨S, y, ?_, (C.sq_eq_one_iff_dvd hn hyρ).2 h8, ?_, ?_⟩
  · show y ∈ P'.comap C.ρ
    rw [Subgroup.mem_comap, hy]
    exact hcP'
  · intro hyc
    exact hc1 (by rw [← hy]; exact (C.ρ_eq_one_iff).2 hyc)
  · intro s hs
    have hs' : C.ρ s ∈ P' := hs
    rw [← C.ρ_eq_one_iff, map_commutatorElement, hy, commutatorElement_def]
    have := hP'c _ hs'
    calc C.ρ s * c * (C.ρ s)⁻¹ * c⁻¹ = (c * C.ρ s) * (C.ρ s)⁻¹ * c⁻¹ := by rw [← this]
      _ = 1 := by group

end CFSG.OddStandard.Solomon75.AhatData
