module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Gaschutz
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem tableVII_exists_compl {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 120)
    (N : Subgroup Γ) (hN : N.Normal) (hN2 : Nat.card N = 2) {x x₂ : Γ} (hx : x ^ 2 = 1)
    (hx₂ : x₂ ^ 2 = 1) (hcomm : x * x₂ = x₂ * x) (hxN : x ∉ N) (hx₂N : x₂ ∉ N)
    (hxx₂N : x * x₂ ∉ N) : ∃ D : Subgroup Γ, N ⊓ D = ⊥ ∧ N ⊔ D = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpp : x * x = 1 := by rw [← pow_two, hx]
  have hqq : x₂ * x₂ = 1 := by rw [← pow_two, hx₂]
  have hqp : x₂ * x = x * x₂ := hcomm.symm
  have hpq_p : x * (x * x₂) = x₂ := by rw [← mul_assoc, hpp, one_mul]
  have hqp_q : x₂ * (x * x₂) = x := by rw [← mul_assoc, hqp, mul_assoc, hqq, mul_one]
  have hpq_q : (x * x₂) * x₂ = x := by rw [mul_assoc, hqq, mul_one]
  have hpq_p' : (x * x₂) * x = x₂ := by rw [mul_assoc, hqp, ← mul_assoc, hpp, one_mul]
  have hpq_pq : (x * x₂) * (x * x₂) = 1 := by rw [mul_assoc, hqp_q, hpp]
  have hx1 : x ≠ 1 := fun h => hxN (h.symm ▸ N.one_mem)
  have hx₂1 : x₂ ≠ 1 := fun h => hx₂N (h.symm ▸ N.one_mem)
  have hr1 : x * x₂ ≠ 1 := fun h => hxx₂N (h.symm ▸ N.one_mem)
  have hxx₂ : x ≠ x₂ := by
    intro h
    exact hxx₂N (by rw [← h, hpp]; exact N.one_mem)
  have hxr : x ≠ x * x₂ := by
    intro h
    exact hx₂1 (by
      calc x₂ = x * (x * x₂) := hpq_p.symm
        _ = x * x := by rw [← h]
        _ = 1 := hpp)
  have hx₂r : x₂ ≠ x * x₂ := by
    intro h
    exact hx1 (by
      calc x = x₂ * (x * x₂) := hqp_q.symm
        _ = x₂ * x₂ := by rw [← h]
        _ = 1 := hqq)
  let Qset : Set Γ := {y | y = 1 ∨ y = x ∨ y = x₂ ∨ y = x * x₂}
  let Q : Subgroup Γ :=
    { carrier := Qset
      mul_mem' := by
        rintro a b ha hb
        change a * b ∈ Qset
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl <;>
          simp [Qset, mul_one, one_mul, hpp, hqq, hqp, hpq_p, hqp_q, hpq_q, hpq_p', hpq_pq]
      one_mem' := by change (1 : Γ) ∈ Qset; exact Or.inl rfl
      inv_mem' := by
        rintro a ha
        change a⁻¹ ∈ Qset
        rcases ha with rfl | rfl | rfl | rfl <;>
          simp [Qset, inv_one, inv_eq_of_mul_eq_one_right hpp,
            inv_eq_of_mul_eq_one_right hqq, inv_eq_of_mul_eq_one_right hpq_pq] }
  let S : Finset Γ := {1, x, x₂, x * x₂}
  have hS : S.card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨1, x, x₂, x * x₂, hx1.symm, hx₂1.symm, hr1.symm, hxx₂, hxr, hx₂r, rfl⟩
  have hQeq : (Q : Set Γ) = ↑S := by
    ext y
    show y ∈ Qset ↔ y ∈ (S : Set Γ)
    simp [Qset, S]
  have hQcard : Nat.card Q = 4 := by
    change Nat.card (Q : Set Γ) = 4
    rw [Nat.card_coe_set_eq, hQeq, Set.ncard_coe_finset, hS]
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (p := 2) (n := 2) (by rw [hQcard]; norm_num)
  have hNp : IsPGroup 2 N := IsPGroup.of_card (p := 2) (n := 1) (by rw [hN2]; norm_num)
  have hNQ : N ⊓ Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    have hyQ : y ∈ Qset := hy.2
    rcases hyQ with h | h | h | h
    · exact h
    · exact absurd (h ▸ hy.1) hxN
    · exact absurd (h ▸ hy.1) hx₂N
    · exact absurd (h ▸ hy.1) hxx₂N
  have hfact : (120 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def 120 Nat.prime_two]
    rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  have hcard : Nat.card N * Nat.card Q = 2 ^ (Nat.card Γ).factorization 2 := by
    rw [hN2, hQcard, hΓ, hfact]
    norm_num
  haveI : N.Normal := hN
  haveI : IsMulCommutative ↥N := by
    haveI : IsCyclic ↥N := isCyclic_of_prime_card (p := 2) hN2
    infer_instance
  obtain ⟨C, hC1, hC2⟩ :=
    CFSG.EvenSporadicStandard.HNRecog.Harada.exists_complement_of_two_sylow_complement
      (K := N) (D := Q) hNp hQp hNQ hcard
  exact ⟨C, hC1, hC2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
