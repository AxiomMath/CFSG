module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Q8
public import CFSG.ClassicalInvolution.Q3.TL3Act

public section

namespace CFSG.ClassicalInvolution.Q3

open QuaternionGroup CFSG.ClassicalInvolution

section Aut

variable {M : Type*} [Group M]

theorem tl3_aut_pow_three_of_pow_three_pow (e : M ≃* QuaternionGroup 2) {P : MulAut M} {k : ℕ}
    (hPk : P ^ 3 ^ k = 1) : P ^ 3 = 1 := by
  by_cases hP1 : P = 1
  · rw [hP1, one_pow]
  have : Finite M := Finite.of_equiv (QuaternionGroup 2) e.symm.toEquiv
  have hA := tl3_natCard_mulAut_le e
  have hI := tl3_natCard_inn e
  have : Finite (MulAut M) :=
    Finite.of_injective (fun f : MulAut M => (f : M → M)) DFunLike.coe_injective
  have hApos : 0 < Nat.card (MulAut M) := Nat.card_pos
  have h4A : 4 ∣ Nat.card (MulAut M) := by
    have := Subgroup.card_subgroup_dvd_card (MulAut.conj : M →* MulAut M).range
    rwa [hI] at this
  have hord : orderOf P = 3 := by
    have hd : orderOf P ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hPk
    obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hdA : orderOf P ∣ Nat.card (MulAut M) := orderOf_dvd_natCard P
    rcases m with _ | _ | m
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hmo)) hP1
    · simpa using hmo
    · exfalso
      have h9 : 9 ∣ orderOf P := by
        rw [hmo]
        exact pow_dvd_pow 3 (by omega : 2 ≤ m + 1 + 1)
      have h9A : 9 ∣ Nat.card (MulAut M) := h9.trans hdA
      have h36 : 36 ∣ Nat.card (MulAut M) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4A h9A
      have := Nat.le_of_dvd hApos h36
      omega
  rw [← hord]
  exact pow_orderOf_eq_one P

private theorem pow_two_ne_one_of_orderOf_eq_four {N : Type*} [Group N] {x : N}
    (hx : orderOf x = 4) : x ^ 2 ≠ 1 := fun h => by
  have := orderOf_dvd_of_pow_eq_one h
  rw [hx] at this
  omega

private theorem pow_four_eq_one_of_orderOf_eq_four {N : Type*} [Group N] {x : N}
    (hx : orderOf x = 4) : x ^ 4 = 1 := by
  rw [← hx]
  exact pow_orderOf_eq_one x

theorem tl3_aut_transitive (e : M ≃* QuaternionGroup 2) {φ : MulAut M} {k : ℕ}
    (hk : φ ^ 3 ^ k = 1) (h1 : φ ≠ 1) {g h : M} (hg : orderOf g = 4) (hh : orderOf h = 4) :
    ∃ m : ℕ, m < 3 ∧ ((φ ^ m) g = h ∨ (φ ^ m) g = h⁻¹) := by
  have h3 : φ ^ 3 = 1 := tl3_aut_pow_three_of_pow_three_pow e hk
  set ψ : MulAut (QuaternionGroup 2) := MulAut.congr e φ with hψ
  have hψ3 : ψ ^ 3 = 1 := by rw [hψ, ← map_pow, h3, map_one]
  have hψ1 : ψ ≠ 1 := fun h => h1 ((MulAut.congr e).injective (by rw [← hψ, h, map_one]))
  have hge : orderOf (e g) = 4 := by rw [MulEquiv.orderOf_eq]; exact hg
  have hhe : orderOf (e h) = 4 := by rw [MulEquiv.orderOf_eq]; exact hh
  obtain ⟨m, hm, hmm⟩ := q8_aut_transitive hψ3 hψ1 (pow_two_ne_one_of_orderOf_eq_four hge)
    (pow_four_eq_one_of_orderOf_eq_four hge) (pow_two_ne_one_of_orderOf_eq_four hhe)
    (pow_four_eq_one_of_orderOf_eq_four hhe)
  refine ⟨m, hm, ?_⟩
  have key : ∀ x : M, (ψ ^ m) (e x) = e ((φ ^ m) x) := fun x => by
    rw [hψ, ← map_pow]
    simp [MulAut.congr_apply]
  rcases hmm with h0 | h0
  · exact Or.inl (e.injective (by rw [← key]; exact h0))
  · exact Or.inr (e.injective (by rw [← key, h0, map_inv]))

theorem tl3_aut_three (e : M ≃* QuaternionGroup 2) {φ₁ φ₂ : MulAut M}
    (h₁ : φ₁ (e.symm (a 1)) = e.symm (xa 0) ∨ φ₁ (e.symm (a 1)) = (e.symm (xa 0))⁻¹)
    (h₂ : φ₂ (e.symm (a 1)) = e.symm (xa 1) ∨ φ₂ (e.symm (a 1)) = (e.symm (xa 1))⁻¹) :
    (φ₁ ≠ 1 ∧ φ₁ ^ 3 = 1) ∨ (φ₂ ≠ 1 ∧ φ₂ ^ 3 = 1) ∨ (φ₁ * φ₂ ≠ 1 ∧ (φ₁ * φ₂) ^ 3 = 1) := by
  have back : ∀ φ : MulAut M, (MulAut.congr e φ ≠ 1 ∧ MulAut.congr e φ ^ 3 = 1) →
      (φ ≠ 1 ∧ φ ^ 3 = 1) := fun φ ⟨hn, h3⟩ =>
    ⟨fun h => hn (by rw [h, map_one]),
      (MulAut.congr e).injective (by rw [map_pow, map_one]; exact h3)⟩
  have conv : ∀ (φ : MulAut M) (x y : QuaternionGroup 2),
      (φ (e.symm x) = e.symm y ∨ φ (e.symm x) = (e.symm y)⁻¹) →
      (MulAut.congr e φ x = y ∨ MulAut.congr e φ x = y⁻¹) := fun φ x y h => by
    rcases h with h | h
    · left
      simp [MulAut.congr_apply, h]
    · right
      simp [MulAut.congr_apply, h]
  rcases q8_aut_three (conv φ₁ _ _ h₁) (conv φ₂ _ _ h₂) with h | h | h
  · exact Or.inl (back φ₁ h)
  · exact Or.inr (Or.inl (back φ₂ h))
  · refine Or.inr (Or.inr (back (φ₁ * φ₂) ?_))
    rwa [map_mul]

end Aut

section Extract

theorem exists_pow_three_pow_of_ne_one {C A : Type*} [Group C] [Finite C] [Group A] (ρ : C →* A)
    {c : C} (h1 : ρ c ≠ 1) (h3 : ρ c ^ 3 = 1) :
    ∃ (x : C) (k : ℕ), x ^ 3 ^ k = 1 ∧ ρ x ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  refine ⟨c ^ b, a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  · intro hx
    rw [map_pow] at hx
    have hord : orderOf (ρ c) = 3 := orderOf_eq_prime h3 h1
    exact hb (hord ▸ orderOf_dvd_of_pow_eq_one hx)

end Extract

end CFSG.ClassicalInvolution.Q3
