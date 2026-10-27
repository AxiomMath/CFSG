module

public import CFSG.FeitThompson.Foundations.PGroupNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n : ℕ} {P : Type*} [Group P] {M : Subgroup P}

theorem normal_of_isCoatom_of_natCard_eq_prime_pow (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hM : IsCoatom M) : M.Normal :=
  have : Group.IsNilpotent P := isNilpotent_of_natCard_eq_prime_pow hp hP
  Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM

theorem index_eq_of_isCoatom_of_natCard_eq_prime_pow (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hM : IsCoatom M) : M.index = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have hMn : M.Normal := normal_of_isCoatom_of_natCard_eq_prime_pow hp hP hM
  obtain ⟨k, -, hik⟩ := (Nat.dvd_prime_pow hp).mp (hP ▸ M.index_dvd_card)
  have hkpos : k ≠ 0 := by
    rintro rfl
    exact hM.1 (Subgroup.index_eq_one.mp (by simpa using hik))
  have hp_dvd : p ∣ Nat.card (P ⧸ M) := by
    rw [← Subgroup.index_eq_card, hik]; exact dvd_pow_self p hkpos
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ M) p hp_dvd
  have hsurj : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
  have hcomap : M ≤ Subgroup.comap (QuotientGroup.mk' M) (zpowers x) := fun m hm => by
    have h1 : (QuotientGroup.mk' M) m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    simp only [Subgroup.mem_comap, h1]
    exact one_mem _
  rcases eq_or_lt_of_le hcomap with heq | hlt
  ·
    refine absurd hx (fun hx => hp.one_lt.ne ?_)
    have hbot : zpowers x = ⊥ := by
      have h := Subgroup.map_comap_eq_self_of_surjective hsurj (zpowers x)
      rw [← heq, QuotientGroup.map_mk'_self] at h
      exact h.symm
    have hx1 : x = 1 := by simpa using (hbot ▸ mem_zpowers x : x ∈ (⊥ : Subgroup (P ⧸ M)))
    rw [← hx, hx1, orderOf_one]
  ·
    have heqtop : zpowers x = ⊤ := by
      have h := Subgroup.map_comap_eq_self_of_surjective hsurj (zpowers x)
      rw [hM.2 _ hlt, Subgroup.map_top_of_surjective _ hsurj] at h
      exact h.symm
    rw [Subgroup.index_eq_card, ← Subgroup.card_top (G := P ⧸ M), ← heqtop, Nat.card_zpowers, hx]

theorem normal_and_index_eq_of_isCoatom_of_natCard_eq_prime_pow (hp : p.Prime)
    (hP : Nat.card P = p ^ n) (hM : IsCoatom M) : M.Normal ∧ M.index = p :=
  ⟨normal_of_isCoatom_of_natCard_eq_prime_pow hp hP hM,
    index_eq_of_isCoatom_of_natCard_eq_prime_pow hp hP hM⟩

theorem natCard_quotient_of_isCoatom_of_natCard_eq_prime_pow (hp : p.Prime)
    (hP : Nat.card P = p ^ n) (hM : IsCoatom M) : Nat.card (P ⧸ M) = p := by
  rw [← Subgroup.index_eq_card]
  exact index_eq_of_isCoatom_of_natCard_eq_prime_pow hp hP hM

end

end CFSG.FeitThompson
