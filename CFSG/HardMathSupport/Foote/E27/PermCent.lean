module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.Foote.E27

open Equiv Subgroup Nat

theorem dvd81_factorial_aux (n m : ℕ) (hn : 12 ≤ n) (hm : 1 ≤ m) (h3m : 3 * m ≤ n) :
    81 ∣ (n - 3 * m)! * 3 ^ m * m ! := by
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | rfl | h
  · have h1 : 9 ! ∣ (n - 3 * 1)! := Nat.factorial_dvd_factorial (by omega)
    have h2 : 9 ! * 3 ^ 1 * 1 ! ∣ (n - 3 * 1)! * 3 ^ 1 * 1 ! :=
      mul_dvd_mul_right (mul_dvd_mul_right h1 _) _
    exact dvd_trans (by decide) h2
  · have h1 : 6 ! ∣ (n - 3 * 2)! := Nat.factorial_dvd_factorial (by omega)
    have h2 : 6 ! * 3 ^ 2 * 2 ! ∣ (n - 3 * 2)! * 3 ^ 2 * 2 ! :=
      mul_dvd_mul_right (mul_dvd_mul_right h1 _) _
    exact dvd_trans (by decide) h2
  · have h1 : 3 ! ∣ (n - 3 * 3)! := Nat.factorial_dvd_factorial (by omega)
    have h2 : 3 ! * 3 ^ 3 * 3 ! ∣ (n - 3 * 3)! * 3 ^ 3 * 3 ! :=
      mul_dvd_mul_right (mul_dvd_mul_right h1 _) _
    exact dvd_trans (by decide) h2
  · have : 3 ^ 4 ∣ 3 ^ m := pow_dvd_pow 3 h
    exact (by norm_num : 81 = 3 ^ 4) ▸
      Dvd.dvd.mul_right (Dvd.dvd.mul_left this _) _

theorem dvd81_card_centralizer_perm {n : ℕ} (hn : 12 ≤ n) {σ : Perm (Fin n)}
    (hσ : orderOf σ = 3) : 81 ∣ Nat.card (centralizer {σ}) := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hσ]; exact Nat.prime_three)
  have hle := Equiv.Perm.sum_cycleType_le σ
  rw [hk, hσ] at hle
  rw [Equiv.Perm.nat_card_centralizer, hk, hσ]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul, Fintype.card_fin,
    Multiset.toFinset_replicate] at hle ⊢
  have hne : k + 1 ≠ 0 := by omega
  simp only [hne]
  have := dvd81_factorial_aux n (k + 1) hn (by omega) (by simpa [mul_comm] using hle)
  simpa [mul_comm, mul_assoc, mul_left_comm] using this

theorem dvd81_card_alt_commuting {n : ℕ} (hn : 12 ≤ n) {σ : Perm (Fin n)}
    (hσ : orderOf σ = 3) :
    81 ∣ Nat.card {a : alternatingGroup (Fin n) // σ * (a : Perm (Fin n)) = a * σ} := by
  let f : centralizer ({σ} : Set (Perm (Fin n))) →* ℤˣ :=
    Perm.sign.comp (centralizer ({σ} : Set (Perm (Fin n)))).subtype
  have h1 := dvd81_card_centralizer_perm hn hσ
  rw [← f.ker.card_mul_index, Subgroup.index_ker] at h1
  have h2 : Nat.card f.range ∣ 2 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
  have h3 : Nat.Coprime 81 (Nat.card f.range) := by
    have hp : Nat.card f.range = 1 ∨ Nat.card f.range = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp h2
    rcases hp with h | h <;> rw [h] <;> norm_num
  have h4 : 81 ∣ Nat.card f.ker := h3.dvd_of_dvd_mul_right h1
  have hf : ∀ c : centralizer ({σ} : Set (Perm (Fin n))), c ∈ f.ker ↔ Perm.sign (c : Perm (Fin n)) = 1 :=
    fun c => MonoidHom.mem_ker
  have e : {a : alternatingGroup (Fin n) // σ * (a : Perm (Fin n)) = a * σ} ≃ f.ker :=
    { toFun := fun a => ⟨⟨a.1.1, mem_centralizer_singleton_iff.mpr a.2.symm⟩,
        (hf _).mpr (Equiv.Perm.mem_alternatingGroup.mp a.1.2)⟩
      invFun := fun c => ⟨⟨c.1.1, Equiv.Perm.mem_alternatingGroup.mpr ((hf _).mp c.2)⟩,
        (mem_centralizer_singleton_iff.mp c.1.2).symm⟩
      left_inv := fun a => rfl
      right_inv := fun c => rfl }
  rwa [Nat.card_congr e]

end CFSG.HardMathSupport.Foote.E27
