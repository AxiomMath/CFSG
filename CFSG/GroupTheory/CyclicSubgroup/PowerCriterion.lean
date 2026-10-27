module

public import CFSG.RankThree.PartTwo.KFacts.K71PSU3

public section

namespace CFSG.GroupTheory.CyclicSubgroup

open CFSG.RankThree.PartTwo.KFacts

theorem exists_pow_eq_mul_inv_of_pow_form {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    {n Q j : ℕ} (f : C →* C) (hf : ∀ x : C, f x = x ^ (Q ^ j))
    (hQ : 1 ≤ Q) (hd : (Nat.card C).gcd n ∣ Q ^ j - 1) (a : C) :
    ∃ μ : C, μ ^ n = a * (f a)⁻¹ := by
  set N := Nat.card C with hN
  set d := N.gcd n with hddef
  have hdvd : d ∣ N := Nat.gcd_dvd_left _ _
  have hHcard : Nat.card (powMonoidHom n : C →* C).range = N / d :=
    IsCyclic.card_powMonoidHom_range C n
  have hmem : a * (f a)⁻¹ ∈ (powMonoidHom n : C →* C).range := by
    refine mem_of_pow_card_eq_one_of_isCyclic (H := (powMonoidHom n : C →* C).range) ?_
    rw [hHcard]
    set t := a ^ (N / d) with ht
    have htd : t ^ d = 1 := by
      rw [ht, ← pow_mul, Nat.div_mul_cancel hdvd, pow_card_eq_one']
    have hmod : Q ^ j ≡ 1 [MOD d] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hQ)).mpr hd).symm
    have htq : t ^ (Q ^ j) = t := by
      have hmodt : Q ^ j ≡ 1 [MOD orderOf t] :=
        Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one htd) hmod
      simpa using (pow_eq_pow_iff_modEq (x := t) (n := Q ^ j) (m := 1)).mpr hmodt
    have hfa : f a = a ^ (Q ^ j) := hf a
    calc (a * (f a)⁻¹) ^ (N / d)
        = a ^ (N / d) * ((f a) ^ (N / d))⁻¹ := by rw [mul_pow, inv_pow]
      _ = t * ((a ^ (Q ^ j)) ^ (N / d))⁻¹ := by rw [hfa, ht]
      _ = t * (a ^ (Q ^ j * (N / d)))⁻¹ := by rw [← pow_mul]
      _ = t * (a ^ ((N / d) * (Q ^ j)))⁻¹ := by rw [mul_comm (Q ^ j) (N / d)]
      _ = t * ((a ^ (N / d)) ^ (Q ^ j))⁻¹ := by rw [pow_mul]
      _ = t * t⁻¹ := by rw [← ht, htq]
      _ = 1 := mul_inv_cancel t
  obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨μ, hμ⟩

end CFSG.GroupTheory.CyclicSubgroup

end
