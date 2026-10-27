module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart

open Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {M : Type*} [Group M] {p : ℕ}

theorem prime_dvd_natCard_of_sylow_ne_bot [Finite M] (hp : p.Prime) (P : Sylow p M)
    (hP : (P : Subgroup M) ≠ ⊥) : p ∣ Nat.card M := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : 1 < Nat.card (P : Subgroup M) := ((P : Subgroup M).one_lt_card_iff_ne_bot).mpr hP
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  rw [hn] at h1
  have hn0 : n ≠ 0 := by rintro rfl; simp at h1
  refine dvd_trans ?_ ((P : Subgroup M).card_subgroup_dvd_card)
  rw [hn]
  exact dvd_pow_self p hn0

variable {K D D0 : Subgroup M}

theorem exists_mem_sylow_orderOf_eq_and_inf_centralizer_eq_bot [Finite M] [K.Normal]
    (hKD : K.IsComplement' D) (hexp : Monoid.exponent D0 = Monoid.exponent D)
    (hC : ∀ d ∈ D0, d ≠ 1 → K ⊓ centralizer ({d} : Set M) = ⊥)
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (P : Sylow p M) (hP : (P : Subgroup M) ≠ ⊥) :
    ∃ a ∈ (P : Subgroup M), orderOf a = p ∧ K ⊓ centralizer ({a} : Set M) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpM : p ∣ Nat.card M := prime_dvd_natCard_of_sylow_ne_bot hp P hP
  have hpD : p ∣ Nat.card D := by
    rw [← hKD.card_mul_card] at hpM
    exact (hp.dvd_mul.mp hpM).resolve_left hpK
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpD
  have hpexp : p ∣ Monoid.exponent D0 := by
    rw [hexp, ← hy, ← Subgroup.orderOf_coe y]
    exact orderOf_dvd_exponent_of_mem y.2
  have hpD0 : p ∣ Nat.card D0 := hpexp.trans Group.exponent_dvd_nat_card
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := D0) p hpD0
  have hbord : orderOf (b : M) = p := by rw [Subgroup.orderOf_coe]; exact hb
  have hb1 : (b : M) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbord
    exact hp.one_lt.ne hbord
  have hCb : K ⊓ centralizer ({(b : M)} : Set M) = ⊥ := hC _ b.2 hb1
  obtain ⟨g, hg⟩ := exists_forall_inv_mul_mul_mem P.card_eq_multiplicity
    (S := zpowers (b : M)) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord, pow_one]))
  refine ⟨g⁻¹ * (b : M) * g, hg _ (mem_zpowers _), ?_, ?_⟩
  · rw [SemiconjBy.orderOf_eq g (x := g⁻¹ * (b : M) * g) (y := (b : M))
      (by unfold SemiconjBy; group)]
    exact hbord
  ·
    rw [eq_bot_iff]
    rintro z ⟨hzK, hzc⟩
    have hzc' : z * (g⁻¹ * (b : M) * g) = (g⁻¹ * (b : M) * g) * z :=
      mem_centralizer_singleton_iff.1 hzc
    have hw : g * z * g⁻¹ ∈ K ⊓ centralizer ({(b : M)} : Set M) := by
      refine ⟨by simpa using ‹K.Normal›.conj_mem z hzK g, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (g * z * g⁻¹) * (b : M) = g * (z * (g⁻¹ * (b : M) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * (b : M) * g) * z) * g⁻¹ := by rw [hzc']
        _ = (b : M) * (g * z * g⁻¹) := by group
    rw [hCb, Subgroup.mem_bot] at hw
    rw [Subgroup.mem_bot]
    have hzeq : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [hzeq, hw]; group

theorem inf_centralizer_sylow_lt [Finite M] [K.Normal]
    (hKD : K.IsComplement' D) (hexp : Monoid.exponent D0 = Monoid.exponent D)
    (hC : ∀ d ∈ D0, d ≠ 1 → K ⊓ centralizer ({d} : Set M) = ⊥)
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (P : Sylow p M) (hP : (P : Subgroup M) ≠ ⊥)
    (hK : K ≠ ⊥) : K ⊓ centralizer ((P : Subgroup M) : Set M) < K := by
  obtain ⟨a, haP, -, hCa⟩ :=
    exists_mem_sylow_orderOf_eq_and_inf_centralizer_eq_bot hKD hexp hC hp hpK P hP
  refine lt_of_le_of_lt ?_ (bot_lt_iff_ne_bot.mpr hK)
  calc K ⊓ centralizer ((P : Subgroup M) : Set M)
      ≤ K ⊓ centralizer ({a} : Set M) :=
        inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr haP))
    _ = ⊥ := hCa

theorem inf_centralizer_sylow_eq_bot [Finite M] [K.Normal]
    (hKD : K.IsComplement' D) (hexp : Monoid.exponent D0 = Monoid.exponent D)
    (hC : ∀ d ∈ D0, d ≠ 1 → K ⊓ centralizer ({d} : Set M) = ⊥)
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (P : Sylow p M) (hP : (P : Subgroup M) ≠ ⊥) :
    K ⊓ centralizer ((P : Subgroup M) : Set M) = ⊥ := by
  obtain ⟨a, haP, -, hCa⟩ :=
    exists_mem_sylow_orderOf_eq_and_inf_centralizer_eq_bot hKD hexp hC hp hpK P hP
  refine le_antisymm ?_ bot_le
  calc K ⊓ centralizer ((P : Subgroup M) : Set M)
      ≤ K ⊓ centralizer ({a} : Set M) :=
        inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr haP))
    _ = ⊥ := hCa

end

end CFSG.FeitThompson
