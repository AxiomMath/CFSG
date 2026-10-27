module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG

namespace Ivk93M12Data

variable {J : Type} [Group J] [Finite J] {y : J}

theorem orderOf_eq_two (D : Ivk93M12Data J y) : orderOf y = 2 := D.central.1

theorem mul_self_eq_one (D : Ivk93M12Data J y) : y * y = 1 := by
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [D.orderOf_eq_two])

theorem ne_one (D : Ivk93M12Data J y) : y ≠ 1 := by
  intro h
  have := D.orderOf_eq_two
  rw [h, orderOf_one] at this
  omega

theorem two_pow_six_dvd_card_aut (D : Ivk93M12Data J y) : 2 ^ 6 ∣ Nat.card (MulAut J) :=
  (show 2 ^ 6 ∣ 192 by norm_num).trans (D.aut.trans (Subgroup.card_subgroup_dvd_card _))

theorem false_of_card_aut (D : Ivk93M12Data J y) (h : ¬ 2 ^ 6 ∣ Nat.card (MulAut J)) : False :=
  h D.two_pow_six_dvd_card_aut

theorem false_of_two_pow_seven_dvd (D : Ivk93M12Data J y) (h : 2 ^ 7 ∣ Nat.card J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
  have hcard := Sylow.card_eq_multiplicity T
  have hle : 7 ≤ (Nat.card J).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h
  have h128 : 2 ^ 7 ≤ Nat.card ↥(T : Subgroup J) := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) hle
  rcases D.sylow_card T with h8 | h32 | h64 <;> omega

theorem false_of_cent_card_eq (D : Ivk93M12Data J y) {c : ℕ}
    (hc : Nat.card ↥(centralizer ({y} : Set J)) = c)
    (hno : ∀ n m : ℕ, (n = 8 ∨ n = 32 ∨ n = 96 ∨ n = 192) → Odd m → n * m ≠ c) : False := by
  obtain ⟨n, m, hn, hm, hnm⟩ := D.cent_card
  exact hno n m hn hm (hnm.symm.trans hc)

theorem card_sylow_dvd_cent (D : Ivk93M12Data J y) (T : Sylow 2 J) :
    Nat.card ↥(T : Subgroup J) ∣ Nat.card ↥(centralizer ({y} : Set J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T₀, -, hcomm⟩ := D.central
  have hle : (T₀ : Subgroup J) ≤ centralizer ({y} : Set J) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm s hs)
  have h1 : Nat.card ↥(T₀ : Subgroup J) ∣ Nat.card ↥(centralizer ({y} : Set J)) :=
    Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(T : Subgroup J) = Nat.card ↥(T₀ : Subgroup J) := by
    rw [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity T₀]
  rw [h2]
  exact h1

end Ivk93M12Data

end CFSG.GH74.GLS.IVK.Proofs2
