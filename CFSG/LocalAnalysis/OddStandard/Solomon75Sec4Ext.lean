module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Normal

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem swap_three_cycle_inv {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : swap b a * swap a c = swap b c * swap a b := by
  have := hab.symm
  have := hac.symm
  have := hbc.symm
  ext x
  by_cases hx1 : x = a
  · subst hx1
    simp [swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [swap_apply_def, *]
  simp [swap_apply_def, *]

theorem three_cycle_prod_eq {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a b * swap b d) * (swap a b * swap b c) = swap a d * swap b c := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  ext x
  by_cases hx1 : x = a
  · subst hx1
    simp [swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [swap_apply_def, *]
  simp [swap_apply_def, *]

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.exists_not_fixed_one {C : CoverSetup n K} (hn : 8 ≤ n) {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) (hk : σ.support.card = 2) :
    ∃ y : K, C.ρ y * σ = σ * C.ρ y ∧ α y ≠ y := by
  have hinv := involution_apply_apply hσ
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < σ.support.card)
  have haσ : σ a ≠ a := Equiv.Perm.mem_support.1 ha
  have hF : 4 ≤ (σ.support)ᶜ.card := by
    rw [Finset.card_compl, hk, Fintype.card_fin]
    omega
  obtain ⟨c, d, -, -, hc, hd, -, -, hcd, -, -, -, -, -⟩ := exists_four_distinct _ hF
  have hfx : ∀ x ∈ (σ.support)ᶜ, σ x = x := fun x hx => by
    simpa [Perm.notMem_support] using hx
  have hcσ : σ c = c := hfx c hc
  have hdσ : σ d = d := hfx d hd
  have hab : a ≠ σ a := haσ.symm
  have hac : a ≠ c := fun e => haσ (by rw [e]; exact hcσ)
  have had : a ≠ d := fun e => haσ (by rw [e]; exact hdσ)
  have hbc : σ a ≠ c := fun e => hac (by rw [← hinv a, e, hcσ])
  have hbd : σ a ≠ d := fun e => had (by rw [← hinv a, e, hdσ])
  obtain ⟨u, hu⟩ := C.exists_ρ_eq (sign_swap_mul_swap_of_ne hab hbc)
  obtain ⟨v, hv⟩ := C.exists_ρ_eq (sign_swap_mul_swap_of_ne hab hbd)
  have hαu : C.ρ (α u) = (C.ρ u)⁻¹ := by
    rw [h.map_ρ, hu, mul_inv_rev, swap_inv, swap_inv]
    have e1 : σ * swap a (σ a) * σ⁻¹ = swap (σ a) (σ (σ a)) :=
      (swap_apply_apply σ a (σ a)).symm
    have e2 : σ * swap (σ a) c * σ⁻¹ = swap (σ (σ a)) (σ c) :=
      (swap_apply_apply σ (σ a) c).symm
    calc σ * (swap a (σ a) * swap (σ a) c) * σ⁻¹
        = (σ * swap a (σ a) * σ⁻¹) * (σ * swap (σ a) c * σ⁻¹) := by group
      _ = swap (σ a) (σ (σ a)) * swap (σ (σ a)) (σ c) := by rw [e1, e2]
      _ = swap (σ a) a * swap a c := by rw [hinv a, hcσ]
      _ = swap (σ a) c * swap a (σ a) := swap_three_cycle_inv hab hac hbc
  have hαv : C.ρ (α v) = (C.ρ v)⁻¹ := by
    rw [h.map_ρ, hv, mul_inv_rev, swap_inv, swap_inv]
    have e1 : σ * swap a (σ a) * σ⁻¹ = swap (σ a) (σ (σ a)) :=
      (swap_apply_apply σ a (σ a)).symm
    have e2 : σ * swap (σ a) d * σ⁻¹ = swap (σ (σ a)) (σ d) :=
      (swap_apply_apply σ (σ a) d).symm
    calc σ * (swap a (σ a) * swap (σ a) d) * σ⁻¹
        = (σ * swap a (σ a) * σ⁻¹) * (σ * swap (σ a) d * σ⁻¹) := by group
      _ = swap (σ a) (σ (σ a)) * swap (σ (σ a)) (σ d) := by rw [e1, e2]
      _ = swap (σ a) a * swap a d := by rw [hinv a, hdσ]
      _ = swap (σ a) d * swap a (σ a) := swap_three_cycle_inv hab had hbd
  have hcu : u * α u ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, hαu, mul_inv_cancel]
  have hcv : v * α v ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, hαv, mul_inv_cancel]
  have hαu' : α u = u⁻¹ * (u * α u) := by group
  have hαv' : α v = v⁻¹ * (v * α v) := by group
  have hρx : C.ρ ⁅u, v⁆ = swap a (σ a) * swap c d := by
    rw [map_commutatorElement, hu, hv, commutator_three_cycles hab hac had hbc hbd hcd]
  have hρw : C.ρ (v * u) = swap a d * swap (σ a) c := by
    rw [map_mul, hu, hv, three_cycle_prod_eq hab hac had hbc hbd hcd]
  refine ⟨⁅u, v⁆, ?_, ?_⟩
  · rw [hρx]
    have hA : swap a (σ a) * σ = σ * swap a (σ a) :=
      mem_centralizer_singleton_iff.1 (swap_mem_centralizer_involution hσ a)
    have hB : σ * swap c d = swap c d * σ := mul_swap_comm_of_fixed hcσ hdσ
    calc swap a (σ a) * swap c d * σ = swap a (σ a) * (swap c d * σ) := mul_assoc _ _ _
      _ = swap a (σ a) * (σ * swap c d) := by rw [hB]
      _ = (swap a (σ a) * σ) * swap c d := (mul_assoc _ _ _).symm
      _ = (σ * swap a (σ a)) * swap c d := by rw [hA]
      _ = σ * (swap a (σ a) * swap c d) := mul_assoc _ _ _
  · intro hαx
    have h1 : α ⁅u, v⁆ = (v * u)⁻¹ * ⁅u, v⁆ * (v * u) := by
      rw [map_commutatorElement, hαu', hαv',
        CFSG.SectionRank.commutatorElement_mul_mem_center u⁻¹ v⁻¹ hcu hcv]
      simp only [commutatorElement_def]
      group
    have h2 : ⁅⁅u, v⁆, v * u⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      have h3 : (v * u)⁻¹ * ⁅u, v⁆ * (v * u) = ⁅u, v⁆ := by rw [← h1, hαx]
      calc ⁅u, v⁆ * (v * u) = (v * u) * ((v * u)⁻¹ * ⁅u, v⁆ * (v * u)) := by group
        _ = (v * u) * ⁅u, v⁆ := by rw [h3]
    have e1 : (C.π ⁅u, v⁆ : Perm (Fin n)) a = σ a := by
      show C.ρ ⁅u, v⁆ a = σ a
      rw [hρx, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
    have e2 : (C.π ⁅u, v⁆ : Perm (Fin n)) d = c := by
      show C.ρ ⁅u, v⁆ d = c
      rw [hρx, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
    have e3 : (C.π ⁅u, v⁆ : Perm (Fin n)) (σ a) = a := by
      show C.ρ ⁅u, v⁆ (σ a) = a
      rw [hρx, Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
    have e4 : (C.π ⁅u, v⁆ : Perm (Fin n)) c = d := by
      show C.ρ ⁅u, v⁆ c = d
      rw [hρx, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
    exact commutator_ne_one_of_doubleCover hn C.hX C.surj C.ker had hab hac hbd.symm hcd.symm hbc
      e1 e2 e3 e4 hρw h2

theorem CoverSetup.card_eq_factorial (C : CoverSetup n K) (hn : 2 ≤ n) :
    Nat.card K = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have h1 := C.card_comap (E := alternatingGroup (Fin n)) le_rfl
  have h2 : (alternatingGroup (Fin n)).comap C.ρ = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    rw [Subgroup.mem_comap]
    exact Perm.mem_alternatingGroup.2 (C.sign_ρ x)
  rw [h2, Subgroup.card_top] at h1
  have h3 := Subgroup.card_mul_index (alternatingGroup (Fin n))
  have hfin : Nat.card (Fin n) = n := by simp
  rw [alternatingGroup.index_eq_two, Nat.card_perm, hfin] at h3
  rw [h1, ← h3, mul_comm]

theorem padicValNat_two_le_factorial {n k : ℕ} (hk : 2 * k ≤ n) :
    k + padicValNat 2 k.factorial + padicValNat 2 (n - 2 * k).factorial ≤
      padicValNat 2 n.factorial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hc : n.choose (2 * k) ≠ 0 := (Nat.choose_pos hk).ne'
  have h2k : (2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hnk : (n - 2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have e : padicValNat 2 n.factorial = padicValNat 2 (n.choose (2 * k)) +
      padicValNat 2 (2 * k).factorial + padicValNat 2 (n - 2 * k).factorial := by
    rw [← h, padicValNat.mul (mul_ne_zero hc h2k) hnk, padicValNat.mul hc h2k]
  have e2 : padicValNat 2 (2 * k).factorial = padicValNat 2 k.factorial + k :=
    padicValNat_factorial_mul k
  omega

theorem CoverSetup.Induces.card_fixSub_pos [Finite K] {C : CoverSetup n K} (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k) :
    Nat.card (fixSub α) = 2 ^ (k - 1) * k.factorial * (n - 2 * k).factorial := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have hk' : k = 1 := by omega
    subst hk'
    exact h.card_fixSub_of_not_fixed hσ hk hk1 (h.exists_not_fixed_one hn hσ hk)
  · exact h.card_fixSub hn hσ hk h2

theorem CoverSetup.Induces.not_sylow_le_fixSub [Finite K] {C : CoverSetup n K} (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k) (T : Sylow 2 K) :
    ¬ (T : Subgroup K) ≤ fixSub α := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkn : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    simpa [hk] using this
  have hcard := h.card_fixSub_pos hn hσ hk hk1
  have hdvd : Nat.card (T : Subgroup K) ∣ Nat.card (fixSub α) := Subgroup.card_dvd_of_le hle
  rw [Sylow.card_eq_multiplicity, C.card_eq_factorial (by omega), hcard,
    Nat.factorization_def _ Nat.prime_two] at hdvd
  have hne : 2 ^ (k - 1) * k.factorial * (n - 2 * k).factorial ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)
  have h1 := (padicValNat_dvd_iff_le hne).1 hdvd
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _), padicValNat.mul (pow_ne_zero _ two_ne_zero)
    (Nat.factorial_ne_zero _), padicValNat.prime_pow] at h1
  have h2 := padicValNat_two_le_factorial hkn
  omega

end AhatData

end CFSG.OddStandard.Solomon75
