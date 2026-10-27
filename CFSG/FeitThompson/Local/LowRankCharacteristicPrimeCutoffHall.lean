module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.LowRankSmallestPrimeHallReduction
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p t : ℕ} {E : Type*} [Group E] [Finite E]

def primesGT (t : ℕ) : Set ℕ := {q : ℕ | q.Prime ∧ t < q}

def primesGE (p : ℕ) : Set ℕ := {q : ℕ | q.Prime ∧ p ≤ q}

@[simp] theorem mem_primesGT {q : ℕ} : q ∈ primesGT t ↔ q.Prime ∧ t < q := Iff.rfl

@[simp] theorem mem_primesGE {q : ℕ} : q ∈ primesGE p ↔ q.Prime ∧ p ≤ q := Iff.rfl

theorem primesGT_subset_setOf_prime (t : ℕ) : primesGT t ⊆ {q : ℕ | q.Prime} := fun _ hq => hq.1

theorem primesGE_subset_setOf_prime (p : ℕ) : primesGE p ⊆ {q : ℕ | q.Prime} := fun _ hq => hq.1

theorem primesGT_subset_primesGE (p : ℕ) : primesGT p ⊆ primesGE p := fun _ hq => ⟨hq.1, hq.2.le⟩

theorem primesGT_antitone {t t' : ℕ} (h : t ≤ t') : primesGT t' ⊆ primesGT t :=
  fun _ hq => ⟨hq.1, lt_of_le_of_lt h hq.2⟩

theorem primesGE_eq_primesGT_pred (hp : 1 ≤ p) : primesGE p = primesGT (p - 1) := by
  ext q
  simp only [mem_primesGE, mem_primesGT, and_congr_right_iff]
  omega

private theorem isHallSubgroup_piCore_primesGT_aux (n : ℕ) :
    ∀ (E : Type*) [Group E] [Finite E] [Group.IsSolvable E], Nat.card E ≤ n →
      Odd (Nat.card E) →
      (∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw E) ≤ 2) →
      ∀ t : ℕ, IsHallSubgroup (primesGT t) (piCore (primesGT t) E) := by
  induction n with
  | zero =>
    intro E _ _ _ hle
    exact absurd (Nat.le_zero.1 hle) Nat.card_pos.ne'
  | succ n ih =>
    intro E _ _ _ hle hodd hrank t
    by_cases hA : IsPiNumber (primesGT t) (Nat.card E)
    ·
      have htop : piCore (primesGT t) E = ⊤ :=
        top_le_iff.1 (le_piCore (Subgroup.normal_of_characteristic ⊤)
          (by rw [isPiSubgroup_iff_isPiNumber, Subgroup.card_top]; exact hA))
      rw [htop, isHallSubgroup_top_iff]
      exact hA
    ·
      rw [isPiNumber_iff] at hA
      simp only [not_forall] at hA
      obtain ⟨q, hq, hq'⟩ := hA
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ Nat.card E := Nat.dvd_of_mem_primeFactors hq
      have hqt : q ≤ t := by
        by_contra hc
        exact hq' ⟨hqprime, by omega⟩
      have hne1 : Nat.card E ≠ 1 := fun h => hqprime.one_lt.ne' (Nat.eq_one_of_dvd_one (h ▸ hqdvd))
      set s := (Nat.card E).minFac with hs_def
      have hs : s.Prime := Nat.minFac_prime hne1
      have hsdvd : s ∣ Nat.card E := Nat.minFac_dvd _
      have hmin : ∀ r : ℕ, r.Prime → r ∣ Nat.card E → s ≤ r :=
        fun r hr hrd => Nat.minFac_le_of_dvd hr.two_le hrd
      have hst : s ≤ t := le_trans (hmin q hqprime hqdvd) hqt
      set D := charHallPCompl s E with hD_def
      have hDcard : ¬ s ∣ Nat.card ↥D := not_dvd_natCard_charHallPCompl hs E
      have hdvd : Nat.card ↥D ∣ Nat.card E := Subgroup.card_subgroup_dvd_card D
      have hDlt : Nat.card ↥D < Nat.card E :=
        lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq => hDcard (heq ▸ hsdvd)
      have hDodd : Odd (Nat.card ↥D) := hodd.of_dvd_nat hdvd
      have hDrank : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥D) ≤ 2 :=
        fun r hr => elementaryAbelianPRank_fittingRaw_charHallPCompl_le hr s E hrank
      have hK' := ih ↥D (by omega) hDodd hDrank t
      set K : Subgroup E := (piCore (primesGT t) ↥D).map D.subtype with hK_def
      have hKchar : K.Characteristic := by rw [hK_def]; infer_instance
      have : K.Normal := have := hKchar; Subgroup.normal_of_characteristic _
      have hKcard : Nat.card ↥K = Nat.card ↥(piCore (primesGT t) ↥D) :=
        Subgroup.card_map_of_injective D.subtype_injective
      have hKidx : K.index = (piCore (primesGT t) ↥D).index * D.index :=
        Subgroup.index_map_subtype _
      have hDidx : IsPiNumber ((primesGT t)ᶜ) D.index := by
        obtain ⟨a, ha⟩ := exists_index_charHallPCompl_eq_pow hs hmin hodd hrank
        refine isPiNumber_iff.2 fun r hr => ?_
        rw [hD_def, ha] at hr
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · simp at hr
        · rw [Nat.primeFactors_prime_pow hpos.ne' hs, Finset.mem_singleton] at hr
          subst hr
          simp only [Set.mem_compl_iff, mem_primesGT, not_and]
          omega
      have hKhall : IsHallSubgroup (primesGT t) K :=
        ⟨by rw [hKcard]; exact hK'.natCard, by rw [hKidx]; exact hK'.index.mul hDidx⟩
      rw [← (isHallSubgroup_iff_isHallPiSubgroup.1 hKhall).eq_piCore]
      exact hKhall

theorem isHallSubgroup_piCore_primesGT [Group.IsSolvable E] (hodd : Odd (Nat.card E))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw E) ≤ 2) (t : ℕ) :
    IsHallSubgroup (primesGT t) (piCore (primesGT t) E) :=
  isHallSubgroup_piCore_primesGT_aux (Nat.card E) E le_rfl hodd hrank t

theorem characteristic_and_isHallSubgroup_piCore_primesGT [Group.IsSolvable E]
    (hodd : Odd (Nat.card E))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw E) ≤ 2) (t : ℕ) :
    (piCore (primesGT t) E).Characteristic ∧
      IsHallSubgroup (primesGT t) (piCore (primesGT t) E) :=
  ⟨piCore_characteristic _ _, isHallSubgroup_piCore_primesGT hodd hrank t⟩

theorem isHallSubgroup_piCore_primesGE [Group.IsSolvable E] (hodd : Odd (Nat.card E))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw E) ≤ 2) (hp : 1 ≤ p) :
    IsHallSubgroup (primesGE p) (piCore (primesGE p) E) := by
  rw [primesGE_eq_primesGT_pred hp]
  exact isHallSubgroup_piCore_primesGT hodd hrank _

theorem piCore_primesGE_eq_piCore_primesGT_sup_sylow (hp : p.Prime)
    (hK : IsHallSubgroup (primesGT p) (piCore (primesGT p) E))
    (hL : IsHallSubgroup (primesGE p) (piCore (primesGE p) E)) (P : Sylow p E) :
    piCore (primesGE p) E = piCore (primesGT p) E ⊔ (P : Subgroup E) := by
  have : Fact p.Prime := ⟨hp⟩
  set K := piCore (primesGT p) E with hKdef
  set L := piCore (primesGE p) E with hLdef
  set a := (Nat.card E).factorization p with hadef
  have hPcard : Nat.card ↥(P : Subgroup E) = p ^ a := P.card_eq_multiplicity
  have hKL : K ≤ L := piCore_mono (primesGT_subset_primesGE p)
  have hpK : ¬ p ∣ Nat.card ↥K := fun hd =>
    (isPiNumber_iff.1 hK.natCard p (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩)).2.false
  have hPL : (P : Subgroup E) ≤ L := by
    refine (isHallSubgroup_iff_isHallPiSubgroup.1 hL).le_of_isPiSubgroup ?_
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [hPcard] at hr
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0, pow_zero] at hr; simp at hr
    · rw [Nat.primeFactors_prime_pow hpos.ne' hp, Finset.mem_singleton] at hr
      subst hr
      exact ⟨hp, le_rfl⟩
  have hrel : Nat.card ↥K * K.relIndex L = Nat.card ↥L := natCard_mul_relIndex hKL
  have hrelne : K.relIndex L ≠ 0 := by
    intro h
    rw [h, mul_zero] at hrel
    exact Nat.card_pos.ne' hrel.symm
  have hreldvdL : K.relIndex L ∣ Nat.card ↥L := ⟨_, by rw [← hrel]; ring⟩
  have hunique : ∀ {d : ℕ}, d.Prime → d ∣ K.relIndex L → d = p := by
    intro d hd hddvd
    have h1 : d ∣ K.index := hddvd.trans (Subgroup.relIndex_dvd_index_of_le hKL)
    have h2 : d ∉ primesGT p :=
      isPiNumber_iff.1 hK.index d
        (Nat.mem_primeFactors.2 ⟨hd, h1, Subgroup.index_ne_zero_of_finite⟩)
    have h3 : d ∈ primesGE p :=
      isPiNumber_iff.1 hL.natCard d
        (Nat.mem_primeFactors.2 ⟨hd, hddvd.trans hreldvdL, Nat.card_pos.ne'⟩)
    simp only [mem_primesGT, not_and, not_lt] at h2
    simp only [mem_primesGE] at h3
    have := h2 hd
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ, K.relIndex L = p ^ b :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hrelne hunique⟩
  have hab : a = b := by
    have h1 : p ^ a ∣ Nat.card ↥L := hPcard ▸ Subgroup.card_dvd_of_le hPL
    have hcop : Nat.Coprime (p ^ a) (Nat.card ↥K) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
    have h2 : p ^ a ∣ p ^ b := by
      rw [← hrel, hb] at h1
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop h1
    have h3 : p ^ b ∣ Nat.card E := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card L)
      rw [← hb]; exact hreldvdL
    have hle1 : a ≤ b := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
    have hle2 : b ≤ a := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h3
    omega
  have hLcard : Nat.card ↥L = Nat.card ↥K * p ^ a := by rw [← hrel, hb, hab]
  have hinf : Nat.card ↥(K ⊓ (P : Subgroup E)) = 1 := by
    have h1 : Nat.card ↥(K ⊓ (P : Subgroup E)) ∣ Nat.card ↥K :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(K ⊓ (P : Subgroup E)) ∣ p ^ a :=
      hPcard ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK).symm) h1 h2
  have : K.Normal := Subgroup.normal_of_characteristic _
  have hsupcard : Nat.card ↥(K ⊔ (P : Subgroup E)) = Nat.card ↥K * p ^ a := by
    have h := natCard_mul_mul_natCard_inf K (P : Subgroup E)
    rw [hinf, mul_one, hPcard] at h
    rw [← h]
    exact Nat.card_congr (Set.equivOfEq (Subgroup.normal_mul K (P : Subgroup E)))
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hKL hPL) (by rw [hLcard, hsupcard])).symm

theorem piCore_primesGT_primesGE_isCharacteristicHall_and_sup_sylow [Group.IsSolvable E]
    (hp : p.Prime) (hodd : Odd (Nat.card E))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw E) ≤ 2) :
    (piCore (primesGT p) E).Characteristic ∧
      IsHallSubgroup (primesGT p) (piCore (primesGT p) E) ∧
      (piCore (primesGE p) E).Characteristic ∧
      IsHallSubgroup (primesGE p) (piCore (primesGE p) E) ∧
      ∀ P : Sylow p E,
        piCore (primesGE p) E = piCore (primesGT p) E ⊔ (P : Subgroup E) :=
  ⟨piCore_characteristic _ _, isHallSubgroup_piCore_primesGT hodd hrank p,
    piCore_characteristic _ _, isHallSubgroup_piCore_primesGE hodd hrank hp.one_lt.le,
    fun P => piCore_primesGE_eq_piCore_primesGT_sup_sylow hp
      (isHallSubgroup_piCore_primesGT hodd hrank p)
      (isHallSubgroup_piCore_primesGE hodd hrank hp.one_lt.le) P⟩

end

end CFSG.FeitThompson
