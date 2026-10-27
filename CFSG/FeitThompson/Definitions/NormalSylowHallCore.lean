module

public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G G' : Type*} [Group G] [Group G']

def normalSylows (G : Type*) [Group G] : Set (Subgroup G) :=
  {H | ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card G ∧ H.Normal ∧ ∃ P : Sylow p G, (P : Subgroup G) = H}

theorem mem_normalSylows {H : Subgroup G} :
    H ∈ normalSylows G ↔
      ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card G ∧ H.Normal ∧ ∃ P : Sylow p G, (P : Subgroup G) = H :=
  Iff.rfl

theorem coe_mem_normalSylows {p : ℕ} (hp : p.Prime) (hpd : p ∣ Nat.card G) (P : Sylow p G)
    [(P : Subgroup G).Normal] : (P : Subgroup G) ∈ normalSylows G :=
  ⟨p, hp, hpd, ‹_›, P, rfl⟩

def hallCore (G : Type*) [Group G] : Subgroup G := sSup (normalSylows G)

theorem hallCore_eq_sSup : hallCore G = sSup (normalSylows G) := (rfl)

theorem le_hallCore_of_mem {H : Subgroup G} (h : H ∈ normalSylows G) : H ≤ hallCore G := by
  rw [hallCore_eq_sSup]; exact le_sSup h

theorem hallCore_le {K : Subgroup G} (h : ∀ H ∈ normalSylows G, H ≤ K) : hallCore G ≤ K := by
  rw [hallCore_eq_sSup]; exact sSup_le h

instance hallCore_normal : (hallCore G).Normal := by
  rw [hallCore_eq_sSup]
  exact Subgroup.sSup_normal _ fun _ hH => hH.choose_spec.2.2.1

theorem sylow_le_hallCore [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] : (P : Subgroup G) ≤ hallCore G := by
  by_cases hpd : p ∣ Nat.card G
  · exact le_hallCore_of_mem (coe_mem_normalSylows Fact.out hpd P)
  · obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have hbot : (P : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp (by simpa using hn)
      rw [hbot]
      exact bot_le
    · exact absurd
        ((dvd_pow_self p (by omega)).trans (hn ▸ (P : Subgroup G).card_subgroup_dvd_card)) hpd

theorem mem_normalSylows_map {H : Subgroup G} (hH : H ∈ normalSylows G) (ϕ : G ≃* G') :
    H.map (ϕ : G →* G') ∈ normalSylows G' := by
  obtain ⟨p, hp, hpd, hn, P, hPH⟩ := hH
  have hinj : Function.Injective ((ϕ.symm : G' →* G)) := ϕ.symm.injective
  refine ⟨p, hp, ?_, hn.map _ ϕ.surjective, ?_⟩
  · rwa [Nat.card_congr ϕ.toEquiv] at hpd
  · subst hPH
    refine ⟨P.comapOfInjective (ϕ.symm : G' →* G) hinj ?_, ?_⟩
    · rw [MonoidHom.range_eq_top_of_surjective _ ϕ.symm.surjective]
      exact le_top
    · rw [Sylow.coe_comapOfInjective, Subgroup.map_equiv_eq_comap_symm]

theorem map_hallCore (ϕ : G ≃* G') : (hallCore G).map (ϕ : G →* G') = hallCore G' := by
  refine le_antisymm ?_ ?_
  · rw [hallCore_eq_sSup, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun H hH => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_hallCore_of_mem (mem_normalSylows_map hH ϕ)
  · refine hallCore_le fun H hH => ?_
    have h1 : H.map (ϕ.symm : G' →* G) ∈ normalSylows G := mem_normalSylows_map hH ϕ.symm
    have h2 := Subgroup.map_mono (f := (ϕ : G →* G')) (le_hallCore_of_mem h1)
    rw [Subgroup.map_map] at h2
    simpa using h2

instance hallCore_characteristic : (hallCore G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun ϕ => by simpa using map_hallCore ϕ

theorem hallCore_eq_bot_of_subsingleton [Subsingleton G] : hallCore G = ⊥ :=
  eq_bot_of_subsingleton _

theorem pow_factorization_dvd_card_hallCore [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] : p ^ (Nat.card G).factorization p ∣ Nat.card (hallCore G) := by
  have h := Subgroup.card_dvd_of_le (sylow_le_hallCore P)
  rwa [P.card_eq_multiplicity] at h

theorem hallCore_eq_top_of_isNilpotent [Finite G] [Group.IsNilpotent G] : hallCore G = ⊤ := by
  have hcard : Nat.card G ∣ Nat.card (hallCore G) := by
    refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp ?_
    intro p
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp
        (pow_factorization_dvd_card_hallCore P)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  exact Subgroup.eq_top_of_card_eq _
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) hcard)

end CFSG.FeitThompson
