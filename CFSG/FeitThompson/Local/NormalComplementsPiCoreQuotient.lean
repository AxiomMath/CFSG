module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Foundations.PGroupNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X] {π : Set ℕ}

def primesOutside (π : Set ℕ) (X : Type*) [Group X] [Finite X] : Set ℕ :=
  {p | p ∈ (Nat.card X).primeFactors ∧ p ∉ π}

theorem mem_primesOutside_iff {p : ℕ} :
    p ∈ primesOutside π X ↔ p ∈ (Nat.card X).primeFactors ∧ p ∉ π := (Iff.rfl)

theorem mem_primeFactors_of_mem_primesOutside {p : ℕ} (hp : p ∈ primesOutside π X) :
    p ∈ (Nat.card X).primeFactors := (mem_primesOutside_iff.1 hp).1

theorem notMem_of_mem_primesOutside {p : ℕ} (hp : p ∈ primesOutside π X) : p ∉ π :=
  (mem_primesOutside_iff.1 hp).2

theorem prime_of_mem_primesOutside {p : ℕ} (hp : p ∈ primesOutside π X) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_primeFactors_of_mem_primesOutside hp)

theorem finite_primesOutside (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (primesOutside π X).Finite :=
  (Nat.card X).primeFactors.finite_toSet.subset fun _ hp => mem_primeFactors_of_mem_primesOutside hp

instance instFinitePrimesOutside (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    Finite (primesOutside π X) := (finite_primesOutside π X).to_subtype

theorem iInf_pComplCore_eq_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    ⨅ p : primesOutside π X, pComplCore (p : ℕ) X = piCore π X := by
  have hJ : (⨅ p : primesOutside π X, pComplCore (p : ℕ) X).Normal :=
    Subgroup.normal_iInf_normal fun _ => inferInstance
  refine le_antisymm (le_piCore hJ (isPiSubgroup_iff.2 fun q hq => ?_)) (le_iInf fun p => ?_)
  · by_contra hqπ
    have hqX : q ∈ (Nat.card X).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card _) Nat.card_pos.ne' hq
    have hle : (⨅ p : primesOutside π X, pComplCore (p : ℕ) X) ≤ pComplCore q X :=
      iInf_le (fun p : primesOutside π X => pComplCore (p : ℕ) X)
        ⟨q, mem_primesOutside_iff.2 ⟨hqX, hqπ⟩⟩
    exact not_dvd_natCard_pComplCore (Nat.prime_of_mem_primeFactors hq) X
      (Nat.dvd_of_mem_primeFactors
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hle) Nat.card_pos.ne' hq))
  · exact le_pComplCore (piCore_normal π X) fun hp =>
      notMem_of_mem_primesOutside p.2 (isPiSubgroup_iff.1 (isPiSubgroup_piCore π X) _ hp)

theorem isHallPiSubgroup_pComplCore {p a : ℕ} (hp : p.Prime)
    (h : (pComplCore p X).index = p ^ a) :
    IsHallPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} (pComplCore p X) where
  isPiSubgroup := pComplCore_eq_piCore p X ▸ isPiSubgroup_piCore _ X
  notMem_of_mem_primeFactors_index := by
    intro r hr
    rw [h] at hr
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at hr
    · rw [Nat.primeFactors_pow _ (by omega), hp.primeFactors, Finset.mem_singleton] at hr
      subst hr
      exact fun hmem => hmem.2 rfl

theorem isHallPiSubgroup_piCore [Group.IsSolvable X]
    (h : ∀ p ∈ (Nat.card X).primeFactors, p ∉ π → ∃ a : ℕ, (pComplCore p X).index = p ^ a) :
    IsHallPiSubgroup π (piCore π X) := by
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := X) π
  have hHle : H ≤ piCore π X := by
    rw [← iInf_pComplCore_eq_piCore]
    refine le_iInf fun p => ?_
    obtain ⟨a, ha⟩ :=
      h p (mem_primeFactors_of_mem_primesOutside p.2) (notMem_of_mem_primesOutside p.2)
    exact (isHallPiSubgroup_pComplCore (prime_of_mem_primesOutside p.2) ha).le_of_isPiSubgroup
      (isPiSubgroup_iff.2 fun q hq =>
        ⟨Nat.prime_of_mem_primeFactors hq, fun hqp =>
          notMem_of_mem_primesOutside p.2 (hqp ▸ isPiSubgroup_iff.1 hH.isPiSubgroup q hq)⟩)
  refine ⟨isPiSubgroup_piCore π X, fun q hq => ?_⟩
  exact isPiNumber_iff.1 hH.index q (Nat.primeFactors_mono (Subgroup.index_dvd_of_le hHle)
    Subgroup.index_ne_zero_of_finite hq)

theorem isHallSubgroup_piCore [Group.IsSolvable X]
    (h : ∀ p ∈ (Nat.card X).primeFactors, p ∉ π → ∃ a : ℕ, (pComplCore p X).index = p ^ a) :
    IsHallSubgroup π (piCore π X) :=
  ⟨isPiSubgroup_iff_isPiNumber.1 (isHallPiSubgroup_piCore h).isPiSubgroup,
    isPiNumber_compl_iff.2 (isHallPiSubgroup_piCore h).notMem_of_mem_primeFactors_index⟩

def diagQuotPComplCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    X →* ∀ p : primesOutside π X, X ⧸ pComplCore (p : ℕ) X :=
  MonoidHom.pi fun p => QuotientGroup.mk' (pComplCore (p : ℕ) X)

@[simp]
theorem diagQuotPComplCore_apply (π : Set ℕ) (X : Type*) [Group X] [Finite X] (x : X)
    (p : primesOutside π X) :
    diagQuotPComplCore π X x p = QuotientGroup.mk (s := pComplCore (p : ℕ) X) x := (rfl)

theorem ker_diagQuotPComplCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (diagQuotPComplCore π X).ker = piCore π X := by
  rw [← iInf_pComplCore_eq_piCore]
  ext x
  simp [MonoidHom.mem_ker, funext_iff, QuotientGroup.eq_one_iff, Subgroup.mem_iInf]

theorem isNilpotent_quotient_piCore
    (h : ∀ p ∈ (Nat.card X).primeFactors, p ∉ π → ∃ a : ℕ, (pComplCore p X).index = p ^ a) :
    Group.IsNilpotent (X ⧸ piCore π X) := by
  have hfac : ∀ p : primesOutside π X, Group.IsNilpotent (X ⧸ pComplCore (p : ℕ) X) := by
    intro p
    obtain ⟨a, ha⟩ :=
      h p (mem_primeFactors_of_mem_primesOutside p.2) (notMem_of_mem_primesOutside p.2)
    refine isNilpotent_of_natCard_eq_prime_pow (prime_of_mem_primesOutside p.2) (a := a) ?_
    rw [← Subgroup.index_eq_card, ha]
  have hker : Group.IsNilpotent (X ⧸ (diagQuotPComplCore π X).ker) :=
    Group.nilpotent_of_mulEquiv (QuotientGroup.quotientKerEquivRange _).symm
  exact Group.nilpotent_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (ker_diagQuotPComplCore π X))

end

end CFSG.FeitThompson
