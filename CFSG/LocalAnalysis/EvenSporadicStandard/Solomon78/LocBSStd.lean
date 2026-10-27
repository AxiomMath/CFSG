module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal
public import CFSG.LocalAnalysis.EvenSmallLie.Setup

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

section Standard

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem twoAdic_map_conj (K : Subgroup X) (g : X) :
    twoAdic (K.map (MulAut.conj g).toMonoidHom) = twoAdic K := by
  unfold twoAdic
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem standard_of_unique {K : Subgroup X} {u : X} (hK : CFSG.Open.IsQuasisimple K)
    (hu2 : orderOf u = 2) (huC : u ∈ centralizer (K : Set X))
    (huniq : ∀ t : X, orderOf t = 2 → t ∈ centralizer (K : Set X) →
      ∀ K' : Subgroup X, K' ≤ centralizer ({t} : Set X) → Group.IsPerfect K' →
        Nat.card K' = Nat.card K → K' = K)
    (hcent : twoAdic (centralizer (K : Set X)) < twoAdic K) :
    standardComponentIsStandard K := by
  set C : Subgroup X := centralizer (K : Set X) with hC
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hconj_cent : ∀ g : X, g ∈ normalizer (K : Set X) → g ∈ normalizer (C : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer hg hx
    · intro hx
      have h1 := CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  have hKg_perf : ∀ g : X, Group.IsPerfect (K.map (MulAut.conj g).toMonoidHom) := by
    intro g
    have := hperf
    exact Group.IsPerfect.map _
  have hKg_card : ∀ g : X, Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K := fun g =>
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hnorm_of_eq : ∀ g : X, K.map (MulAut.conj g).toMonoidHom = K →
      g ∈ normalizer (K : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : g * h * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨h, hh, rfl⟩
      rwa [hg] at this
    · intro hh
      have hh' : g * h * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by rw [hg]; exact hh
      obtain ⟨y, hy, hyh⟩ := hh'
      have h2 : g * y * g⁻¹ = g * h * g⁻¹ := hyh
      have : y = h := mul_left_cancel (mul_right_cancel h2)
      exact this ▸ hy
  refine ⟨hK, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : orderOf (⟨u, huC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk, hu2]
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  ·
    intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
    have ht2 : orderOf (t : X) = 2 := by rw [orderOf_coe, ht]
    have htC : (t : X) ∈ C := t.2.1
    obtain ⟨c, hc, hct⟩ := t.2.2
    have hKg : K.map (MulAut.conj g).toMonoidHom ≤ centralizer ({(t : X)} : Set X) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : k * (c : X) = c * k := mem_centralizer_iff.1 hc k hk
      rw [← hct]
      show (g * k * g⁻¹) * (g * c * g⁻¹) = (g * c * g⁻¹) * (g * k * g⁻¹)
      calc g * k * g⁻¹ * (g * c * g⁻¹) = g * (k * c) * g⁻¹ := by group
        _ = g * (c * k) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * (g * k * g⁻¹) := by group
    have heq := huniq t ht2 htC _ hKg (hKg_perf g) (hKg_card g)
    exact hg (hconj_cent g (hnorm_of_eq g heq))
  ·
    refine le_antisymm ?_ ?_
    · intro g hg
      have hu' : g * u * g⁻¹ ∈ C := (mem_normalizer_iff.1 hg u).1 huC
      have hu'2 : orderOf (g * u * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu2]
      have hKg : K.map (MulAut.conj g).toMonoidHom ≤ centralizer ({g * u * g⁻¹} : Set X) := by
        rintro _ ⟨k, hk, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have h1 : k * u = u * k := mem_centralizer_iff.1 huC k hk
        show (g * k * g⁻¹) * (g * u * g⁻¹) = (g * u * g⁻¹) * (g * k * g⁻¹)
        calc g * k * g⁻¹ * (g * u * g⁻¹) = g * (k * u) * g⁻¹ := by group
          _ = g * (u * k) * g⁻¹ := by rw [h1]
          _ = g * u * g⁻¹ * (g * k * g⁻¹) := by group
      have heq := huniq _ hu'2 hu' _ hKg (hKg_perf g) (hKg_card g)
      exact hnorm_of_eq g heq
    · exact fun g hg => hconj_cent g hg
  ·
    intro g hbot
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ C := by
      rw [commutator_comm] at hbot
      exact commutator_eq_bot_iff_le_centralizer.1 hbot
    have h1 := twoAdic_mono hle
    rw [twoAdic_map_conj] at h1
    exact absurd (lt_of_le_of_lt h1 hcent) (lt_irrefl _)

end Standard

section AutCentralizer

variable {G : Type} [Group G]

theorem autCentralizer_le_map_centralizer {L K : Subgroup G}
    (hinn : ∀ α : MulAut ↥L, ∃ c : ↥L, ∀ x, α x = c * x * c⁻¹) :
    autCentralizer L K ≤ (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
      (MulAut.conj : ↥L →* MulAut ↥L) := by
  intro α hα
  obtain ⟨c, hc⟩ := hinn α
  refine ⟨c, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro k hk
    have h1 := hα k (mem_subgroupOf.1 hk)
    rw [hc] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · ext x
    simp [hc]

variable [Finite G]

theorem twoAdic_autCentralizer_le_of_allInner {L K : Subgroup G}
    (hinn : ∀ α : MulAut ↥L, ∃ c : ↥L, ∀ x, α x = c * x * c⁻¹) :
    twoAdic (autCentralizer L K) ≤
      twoAdic (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) := by
  have h1 := twoAdic_mono (autCentralizer_le_map_centralizer (K := K) hinn)
  refine h1.trans ?_
  unfold twoAdic
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_map_dvd _ _) 2

end AutCentralizer

theorem twoAdic_le_of_map_le {X Z : Type} [Group X] [Group Z] [Finite Z] {H : Subgroup X}
    {H' : Subgroup Z} (f : X →* Z) (hf : Function.Injective f) (h : H.map f ≤ H') :
    twoAdic H ≤ twoAdic H' := by
  have h1 := twoAdic_mono h
  unfold twoAdic at h1 ⊢
  rwa [Subgroup.card_map_of_injective hf] at h1

end CFSG.EvenSporadicStandard.Solomon78
