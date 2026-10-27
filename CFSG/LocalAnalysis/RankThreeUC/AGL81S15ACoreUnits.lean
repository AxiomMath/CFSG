module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

@[expose] def unitsPPart (F : Type) [Field F] (r : ℕ) : Subgroup Fˣ where
  carrier := {u | ∃ k : ℕ, u ^ (r ^ k) = 1}
  mul_mem' := fun {a b} ⟨k, hk⟩ ⟨l, hl⟩ => ⟨k + l, by
    rw [mul_pow, pow_add, pow_mul, hk, one_pow, one_mul, mul_comm, pow_mul, hl, one_pow]⟩
  one_mem' := ⟨0, by simp⟩
  inv_mem' := fun {a} ⟨k, hk⟩ => ⟨k, by rw [inv_pow, hk, inv_one]⟩

variable {F : Type} [Field F]

theorem unitsPPart_isCyclic (F : Type) [Field F] [Finite F] (r : ℕ) :
    IsCyclic (unitsPPart F r) :=
  inferInstance

theorem unitsPPart_isPGroup (F : Type) [Field F] [Finite F] (r : ℕ) [Fact r.Prime] :
    IsPGroup r (unitsPPart F r) := fun u => by
  obtain ⟨k, hk⟩ := u.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem unitsPPart_eq_sylow (F : Type) [Field F] [Finite F] (r : ℕ) [Fact r.Prime]
    (P : Sylow r Fˣ) : unitsPPart F r = P := by
  refine le_antisymm ((unitsPPart_isPGroup F r).le_sylow_of_normal P) fun u hu => ?_
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem card_unitsPPart (F : Type) [Field F] [Fintype F] (r : ℕ) [Fact r.Prime] :
    Nat.card (unitsPPart F r) = r ^ padicValNat r (Fintype.card F - 1) := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r Fˣ))
  rw [unitsPPart_eq_sylow F r P, P.card_eq_multiplicity, Nat.card_units, Nat.card_eq_fintype_card,
    Nat.factorization_def _ Fact.out]

theorem two_le_of_card_eq_sq [Fintype F] {q : ℕ} (hF : Fintype.card F = q ^ 2) : 2 ≤ q := by
  by_contra h
  have h1 : q ^ 2 ≤ 1 := by interval_cases q <;> simp
  have := Fintype.one_lt_card (α := F)
  omega

theorem card_unitsPPart_of_dvd_add_one [Fintype F] {q r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hF : Fintype.card F = q ^ 2) (hrq : r ∣ q + 1) :
    Nat.card (unitsPPart F r) = r ^ padicValNat r (q + 1) := by
  have hq := two_le_of_card_eq_sq hF
  have hsub : ¬ r ∣ q - 1 := fun h => by
    have h2 : r ∣ 2 := by
      have := Nat.dvd_sub hrq h
      rwa [show q + 1 - (q - 1) = 2 by omega] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 h2)
  have hfac : Fintype.card F - 1 = (q - 1) * (q + 1) := by
    rw [hF]
    zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
    ring
  rw [card_unitsPPart, hfac, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd hsub, zero_add]

theorem pow_add_one_eq_one_of_mem_unitsPPart [Fintype F] {q r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hF : Fintype.card F = q ^ 2) (hrq : r ∣ q + 1) {u : Fˣ}
    (hu : u ∈ unitsPPart F r) : u ^ (q + 1) = 1 := by
  have h : Nat.card (unitsPPart F r) ∣ q + 1 := by
    rw [card_unitsPPart_of_dvd_add_one hr2 hF hrq]
    exact pow_padicValNat_dvd
  obtain ⟨c, hc⟩ := h
  have h1 : (⟨u, hu⟩ : unitsPPart F r) ^ Nat.card (unitsPPart F r) = 1 := pow_card_eq_one'
  have h2 : u ^ Nat.card (unitsPPart F r) = 1 := by
    have h := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  rw [hc, pow_mul, h2, one_pow]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
