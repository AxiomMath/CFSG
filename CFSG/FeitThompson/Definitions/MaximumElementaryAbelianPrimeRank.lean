module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p q d : ℕ} {X Y : Type*} [Group X] [Group Y]

def elementaryAbelianPrimeRanks (X : Type*) [Group X] : Set ℕ :=
  {d | ∃ p : ℕ, p.Prime ∧ d ∈ elementaryAbelianRanks p X}

@[simp]
theorem mem_elementaryAbelianPrimeRanks :
    d ∈ elementaryAbelianPrimeRanks X ↔ ∃ p : ℕ, p.Prime ∧ d ∈ elementaryAbelianRanks p X :=
  Iff.rfl

theorem mem_elementaryAbelianPrimeRanks_iff_exists_subgroup :
    d ∈ elementaryAbelianPrimeRanks X ↔
      ∃ p : ℕ, p.Prime ∧ ∃ H : Subgroup X,
        Nonempty (H ≃* (Fin d → Multiplicative (ZMod p))) := by
  simp

theorem mem_elementaryAbelianPrimeRanks_of_prime (hp : p.Prime)
    (hd : d ∈ elementaryAbelianRanks p X) : d ∈ elementaryAbelianPrimeRanks X :=
  ⟨p, hp, hd⟩

theorem zero_mem_elementaryAbelianPrimeRanks (X : Type*) [Group X] :
    0 ∈ elementaryAbelianPrimeRanks X :=
  ⟨2, Nat.prime_two, zero_mem_elementaryAbelianRanks 2 X⟩

theorem elementaryAbelianPrimeRanks_nonempty (X : Type*) [Group X] :
    (elementaryAbelianPrimeRanks X).Nonempty :=
  ⟨0, zero_mem_elementaryAbelianPrimeRanks X⟩

theorem le_card_of_mem_elementaryAbelianPrimeRanks [Finite X]
    (hd : d ∈ elementaryAbelianPrimeRanks X) : d ≤ Nat.card X := by
  obtain ⟨p, hp, hd⟩ := hd
  exact le_card_of_mem_elementaryAbelianRanks hp.one_lt hd

theorem bddAbove_elementaryAbelianPrimeRanks (X : Type*) [Group X] [Finite X] :
    BddAbove (elementaryAbelianPrimeRanks X) :=
  ⟨Nat.card X, fun _ hd => le_card_of_mem_elementaryAbelianPrimeRanks hd⟩

noncomputable def maxElementaryAbelianPRank (X : Type*) [Group X] : ℕ :=
  sSup (elementaryAbelianPrimeRanks X)

theorem maxElementaryAbelianPRank_eq_sSup (X : Type*) [Group X] :
    maxElementaryAbelianPRank X = sSup (elementaryAbelianPrimeRanks X) := (rfl)

theorem le_maxElementaryAbelianPRank [Finite X] (hd : d ∈ elementaryAbelianPrimeRanks X) :
    d ≤ maxElementaryAbelianPRank X :=
  le_csSup (bddAbove_elementaryAbelianPrimeRanks X) hd

theorem maxElementaryAbelianPRank_le {n : ℕ}
    (h : ∀ d ∈ elementaryAbelianPrimeRanks X, d ≤ n) : maxElementaryAbelianPRank X ≤ n :=
  csSup_le (elementaryAbelianPrimeRanks_nonempty X) h

theorem maxElementaryAbelianPRank_mem_elementaryAbelianPrimeRanks (X : Type*) [Group X]
    [Finite X] : maxElementaryAbelianPRank X ∈ elementaryAbelianPrimeRanks X :=
  Nat.sSup_mem (elementaryAbelianPrimeRanks_nonempty X) (bddAbove_elementaryAbelianPrimeRanks X)

theorem exists_prime_subgroup_mulEquiv_maxElementaryAbelianPRank (X : Type*) [Group X] [Finite X] :
    ∃ p : ℕ, p.Prime ∧ ∃ H : Subgroup X,
      Nonempty (H ≃* (Fin (maxElementaryAbelianPRank X) → Multiplicative (ZMod p))) :=
  mem_elementaryAbelianPrimeRanks_iff_exists_subgroup.1
    (maxElementaryAbelianPRank_mem_elementaryAbelianPrimeRanks X)

theorem elementaryAbelianPRank_le_maxElementaryAbelianPRank [Finite X] (hp : p.Prime) :
    elementaryAbelianPRank p X ≤ maxElementaryAbelianPRank X :=
  le_maxElementaryAbelianPRank
    ⟨p, hp, elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt⟩

theorem exists_prime_elementaryAbelianPRank_eq (X : Type*) [Group X] [Finite X] :
    ∃ p : ℕ, p.Prime ∧ elementaryAbelianPRank p X = maxElementaryAbelianPRank X := by
  obtain ⟨p, hp, hd⟩ := maxElementaryAbelianPRank_mem_elementaryAbelianPrimeRanks X
  exact ⟨p, hp, Nat.le_antisymm (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp)
    (le_elementaryAbelianPRank hp.one_lt hd)⟩

theorem bddAbove_image_elementaryAbelianPRank (X : Type*) [Group X] [Finite X] :
    BddAbove ((fun p => elementaryAbelianPRank p X) '' {p : ℕ | p.Prime}) := by
  refine ⟨Nat.card X, ?_⟩
  rintro n ⟨p, hp, rfl⟩
  exact elementaryAbelianPRank_le_card hp.one_lt

theorem maxElementaryAbelianPRank_eq_sSup_image (X : Type*) [Group X] [Finite X] :
    maxElementaryAbelianPRank X =
      sSup ((fun p => elementaryAbelianPRank p X) '' {p : ℕ | p.Prime}) := by
  refine Nat.le_antisymm (maxElementaryAbelianPRank_le ?_) (csSup_le ⟨_, 2, Nat.prime_two, rfl⟩ ?_)
  · rintro d ⟨p, hp, hd⟩
    exact (le_elementaryAbelianPRank hp.one_lt hd).trans
      (le_csSup (bddAbove_image_elementaryAbelianPRank X) ⟨p, hp, rfl⟩)
  · rintro n ⟨p, hp, rfl⟩
    exact elementaryAbelianPRank_le_maxElementaryAbelianPRank hp

theorem maxElementaryAbelianPRank_le_card (X : Type*) [Group X] [Finite X] :
    maxElementaryAbelianPRank X ≤ Nat.card X :=
  maxElementaryAbelianPRank_le fun _ hd => le_card_of_mem_elementaryAbelianPrimeRanks hd

theorem maxElementaryAbelianPRank_pi (hp : p.Prime) (d : ℕ) :
    maxElementaryAbelianPRank (Fin d → Multiplicative (ZMod p)) = d := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine Nat.le_antisymm (maxElementaryAbelianPRank_le ?_) ?_
  · rintro e ⟨q, hq, he⟩
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · exact Nat.zero_le _
    obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks he
    have hdvd : q ^ e ∣ p ^ d := by
      rw [← card_pi_multiplicative_zmod p d, ← hH]; exact H.card_subgroup_dvd_card
    have hqp : q = p := by
      have h1 : q ∣ p ^ d := (dvd_pow_self q (by omega)).trans hdvd
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1)
    subst hqp
    exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).1 hdvd
  · exact (elementaryAbelianPRank_pi hp.one_lt d).ge.trans
      (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp)

theorem maxElementaryAbelianPRank_le_of_injective [Finite Y] {f : X →* Y}
    (hf : Function.Injective f) :
    maxElementaryAbelianPRank X ≤ maxElementaryAbelianPRank Y := by
  have : Finite X := Finite.of_injective f hf
  obtain ⟨p, hp, H, ⟨g⟩⟩ := exists_prime_subgroup_mulEquiv_maxElementaryAbelianPRank X
  exact le_maxElementaryAbelianPRank (mem_elementaryAbelianPrimeRanks_iff_exists_subgroup.2
    ⟨p, hp, H.map f, ⟨(H.equivMapOfInjective f hf).symm.trans g⟩⟩)

theorem maxElementaryAbelianPRank_le_of_le [Finite X] {H K : Subgroup X} (h : H ≤ K) :
    maxElementaryAbelianPRank H ≤ maxElementaryAbelianPRank K :=
  maxElementaryAbelianPRank_le_of_injective (f := Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem maxElementaryAbelianPRank_subgroup_le [Finite X] (H : Subgroup X) :
    maxElementaryAbelianPRank H ≤ maxElementaryAbelianPRank X :=
  maxElementaryAbelianPRank_le_of_injective H.subtype_injective

theorem maxElementaryAbelianPRank_eq_of_mulEquiv [Finite X] [Finite Y] (e : X ≃* Y) :
    maxElementaryAbelianPRank X = maxElementaryAbelianPRank Y :=
  Nat.le_antisymm (maxElementaryAbelianPRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (maxElementaryAbelianPRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

theorem one_le_maxElementaryAbelianPRank_iff (X : Type*) [Group X] [Finite X] :
    1 ≤ maxElementaryAbelianPRank X ↔ Nontrivial X := by
  constructor
  · intro h
    obtain ⟨p, hp, hd⟩ := maxElementaryAbelianPRank_mem_elementaryAbelianPrimeRanks X
    obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks hd
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ maxElementaryAbelianPRank X := Nat.one_lt_pow (by omega) hp.one_lt
      _ = Nat.card H := hH.symm
      _ ≤ Nat.card X := H.card_le_card_group
  · intro h
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (n := Nat.card X) (by have := Finite.one_lt_card (α := X); omega)
    exact ((one_le_elementaryAbelianPRank_iff hp).2 hpd).trans
      (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp)

theorem maxElementaryAbelianPRank_eq_zero_iff (X : Type*) [Group X] [Finite X] :
    maxElementaryAbelianPRank X = 0 ↔ Subsingleton X := by
  rw [← not_nontrivial_iff_subsingleton, ← one_le_maxElementaryAbelianPRank_iff]
  omega

end

end CFSG.FeitThompson
