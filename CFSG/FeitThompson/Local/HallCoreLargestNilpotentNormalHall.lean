module

public import CFSG.FeitThompson.Definitions.NormalSylowHallCore
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {X : Type*} [Group X]

theorem exists_normal_sylow_of_dvd_natCard_hallCore [Finite X] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (hallCore X)) : ∃ P : Sylow p X, (P : Subgroup X).Normal := by
  set π : Set ℕ := {q : ℕ | q.Prime ∧ ∃ P : Sylow q X, (P : Subgroup X).Normal} with hπ
  have h1 : hallCore X ≤ piCore π X := by
    refine hallCore_le fun H hH => ?_
    obtain ⟨q, hq, hqd, hn, P, hPH⟩ := mem_normalSylows.1 hH
    refine le_piCore hn (isPiSubgroup_iff.2 fun r hr => ?_)
    have hcard : Nat.card H = q ^ (Nat.card X).factorization q := by
      have : Fact q.Prime := ⟨hq⟩
      rw [← hPH]; exact P.card_eq_multiplicity
    rw [hcard] at hr
    have hrq : r = q := by
      have hrp := Nat.prime_of_mem_primeFactors hr
      exact (Nat.prime_dvd_prime_iff_eq hrp hq).1
        (hrp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hr))
    subst hrq
    exact ⟨hq, P, hPH ▸ hn⟩
  have h2 : IsPiSubgroup π (hallCore X) := (isPiSubgroup_piCore π X).of_le h1
  exact (isPiSubgroup_iff.1 h2 p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)).2

theorem not_dvd_index_hallCore [Finite X] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (hallCore X)) : ¬ p ∣ (hallCore X).index := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_normal_sylow_of_dvd_natCard_hallCore hp hdvd
  have := hP
  intro hidx
  have h1 : p ^ ((Nat.card X).factorization p + 1)
      ∣ Nat.card (hallCore X) * (hallCore X).index := by
    rw [pow_succ]
    exact mul_dvd_mul (pow_factorization_dvd_card_hallCore P) hidx
  rw [Subgroup.card_mul_index] at h1
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 h1
  omega

theorem coprime_natCard_index_hallCore [Finite X] :
    Nat.Coprime (Nat.card (hallCore X)) (hallCore X).index := by
  by_contra hc
  obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact not_dvd_index_hallCore hp h1 h2

theorem isHallSubgroup_hallCore [Finite X] :
    IsHallSubgroup {p | p ∣ Nat.card (hallCore X)} (hallCore X) where
  natCard := isPiNumber_iff.2 fun _ hp => Nat.dvd_of_mem_primeFactors hp
  index := isPiNumber_compl_iff.2 fun _p hp hmem =>
    not_dvd_index_hallCore (Nat.prime_of_mem_primeFactors hp) hmem
      (Nat.dvd_of_mem_primeFactors hp)

theorem hallCore_le_fittingRaw [Finite X] : hallCore X ≤ fittingRaw X := by
  refine hallCore_le fun H hH => ?_
  obtain ⟨q, hq, hqd, hn, P, hPH⟩ := mem_normalSylows.1 hH
  exact le_fittingRaw hn (isPrimePowerOrder_iff_isPGroup.2 ⟨q, hq, hPH ▸ P.isPGroup'⟩)

instance hallCore_isNilpotent [Finite X] : Group.IsNilpotent (hallCore X) :=
  isNilpotent_of_le_fittingRaw hallCore_le_fittingRaw

theorem factorization_natCard_eq_of_coprime_index [Finite X] {Y : Subgroup X}
    (hcop : Nat.Coprime (Nat.card Y) Y.index) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card Y) :
    (Nat.card Y).factorization p = (Nat.card X).factorization p := by
  have hnd : ¬ p ∣ Y.index := fun h =>
    hp.ne_one (Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hdvd h))
  rw [← Subgroup.card_mul_index Y,
    Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

theorem le_hallCore_of_normal_of_isNilpotent_of_coprime [Finite X] {Y : Subgroup X}
    (hY : Y.Normal) (hnil : Group.IsNilpotent Y)
    (hcop : Nat.Coprime (Nat.card Y) Y.index) : Y ≤ hallCore X := by
  have := hY
  have := hnil
  have key : ∀ p ∈ (Nat.card Y).primeFactors, p ∣ Nat.card (hallCore X) := by
    intro p hpmem
    have hp := Nat.prime_of_mem_primeFactors hpmem
    have hpd := Nat.dvd_of_mem_primeFactors hpmem
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q⟩ : Nonempty (Sylow p Y) := inferInstance
    have hQn : (Q : Subgroup Y).Normal := inferInstance
    have : (Q : Subgroup Y).Characteristic := Sylow.characteristic_of_normal Q hQn
    have hmn : ((Q : Subgroup Y).map Y.subtype).Normal := inferInstance
    have hcard : Nat.card ((Q : Subgroup Y).map Y.subtype)
        = p ^ (Nat.card X).factorization p := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, Q.card_eq_multiplicity,
        factorization_natCard_eq_of_coprime_index hcop hp hpd]
    have hnorm : ((Sylow.ofCard _ hcard : Sylow p X) : Subgroup X).Normal := by
      rw [Sylow.coe_ofCard]; exact hmn
    have hle := sylow_le_hallCore (Sylow.ofCard _ hcard)
    rw [Sylow.coe_ofCard] at hle
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
    rw [hcard]
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne'
      (hpd.trans (Subgroup.card_subgroup_dvd_card Y))).ne'
  exact IsHallSubgroup.normal_le (isPiNumber_iff.2 key) isHallSubgroup_hallCore

theorem isGreatest_hallCore [Finite X] :
    IsGreatest {Y : Subgroup X | Y.Normal ∧ Group.IsNilpotent Y ∧
      Nat.Coprime (Nat.card Y) Y.index} (hallCore X) :=
  ⟨⟨hallCore_normal, hallCore_isNilpotent, coprime_natCard_index_hallCore⟩,
    fun _ h => le_hallCore_of_normal_of_isNilpotent_of_coprime h.1 h.2.1 h.2.2⟩

theorem eq_hallCore_of_isGreatest [Finite X] {Y : Subgroup X}
    (h : IsGreatest {Y : Subgroup X | Y.Normal ∧ Group.IsNilpotent Y ∧
      Nat.Coprime (Nat.card Y) Y.index} Y) : Y = hallCore X :=
  h.unique isGreatest_hallCore

end CFSG.FeitThompson
