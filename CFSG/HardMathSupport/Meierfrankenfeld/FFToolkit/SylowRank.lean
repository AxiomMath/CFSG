module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open scoped Pointwise

theorem card_le_two_pow_pred_of_orderOf_four {G : Type} [Group G] [Finite G] {k m : ℕ}
    (hG : Nat.card G = 2 ^ k * m) (hm : Odd m) {y : G} (hy : orderOf y = 4)
    (B : Subgroup G) (hBc : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x) (hB2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ (k - 1) := by
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : y ^ 2 = 1 := by rw [sq]; exact h
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at hd
    norm_num at hd
  have hB2g : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]
    exact hB2 _ g.2)⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have h2m : ¬ 2 ∣ m := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.1 hm
    omega
  have hfac : Nat.factorization (Nat.card G) 2 = k := by
    rw [hG, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h2m, add_zero]
  obtain ⟨Q, hBQ⟩ := hB2g.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup G) = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
  have hdvd : Nat.card B ∣ 2 ^ k := hQcard ▸ Subgroup.card_dvd_of_le hBQ
  obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hlt : i < k := by
    rcases Nat.lt_or_eq_of_le hik with h | h
    · exact h
    · exfalso
      have hBeq : B = (Q : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hBQ (by rw [hQcard, hi, h])
      have hyg2 : IsPGroup 2 (Subgroup.zpowers y) :=
        IsPGroup.of_card (p := 2) (n := 2) (by rw [Nat.card_zpowers, hy]; norm_num)
      obtain ⟨Py, hyPy⟩ := hyg2.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Py Q
      have hyg : g * y * g⁻¹ ∈ B := by
        rw [hBeq, ← hg]
        exact (Set.mem_smul_set.2 ⟨y, hyPy (Subgroup.mem_zpowers y), rfl⟩ :
          g * y * g⁻¹ ∈ MulAut.conj g • (Py : Set G))
      have hsq := hB2 _ hyg
      apply hy2
      have h' : g * (y * y) * g⁻¹ = 1 := by
        rw [← hsq]
        group
      calc y * y = g⁻¹ * (g * (y * y) * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
  rw [hi]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem rank_le_two_pow_pred_of_orderOf_four {G : Type} [Group G] [Finite G] {k m : ℕ}
    (hG : Nat.card G = 2 ^ k * m) (hm : Odd m) {y : G} (hy : orderOf y = 4) :
    ∀ B : Subgroup G, (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ (k - 1) :=
  fun B hBc hB2 => card_le_two_pow_pred_of_orderOf_four hG hm hy B hBc hB2

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
