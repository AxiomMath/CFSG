module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveKer

public section

namespace CFSG.OddStandard

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
  {S : Sylow 2 (centralizer (L : Set G))} {t : G}

theorem eq_one_or_eq_t_of_mem_sg (hs : Sector L S t) (hcard : Nat.card (sg L S) = 2) {u : G}
    (hu : u ∈ sg L S) : u = 1 ∨ u = t := by
  have h1 : orderOf (⟨u, hu⟩ : sg L S) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact Or.inl (orderOf_eq_one_iff.1 h)
  · exact Or.inr (eq_t_of_orderOf_eq_two hs hu h)

theorem oddKer_inf_centralizer_eq_bot (hs : Sector L S t)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) :
    oddKer L ⊓ centralizer ({t} : Set G) = ⊥ := by
  obtain ⟨hKodd, -, -⟩ := oddKer_complement hs
  obtain ⟨hHM, -, -, -⟩ := centralizer_t_facts hs
  set H := centralizer ({t} : Set G) with hH
  let N : Subgroup H := (oddKer L).subgroupOf H
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ oddKer L := hn
    show ((g * n * g⁻¹ : H) : G) ∈ oddKer L
    exact oddKer_normalized hs (hHM g.2) hn'
  have hNodd : Odd (Nat.card N) := by
    have h1 : Nat.card N = Nat.card (oddKer L ⊓ H : Subgroup G) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]
    rw [h1]
    exact Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_left)
  have hle : N ≤ CFSG.oddCore H := le_oddCore_of_normal_odd hNn hNodd
  rw [hbal, le_bot_iff] at hle
  refine eq_bot_iff.2 fun k hk => ?_
  have hkN : (⟨k, hk.2⟩ : H) ∈ N := hk.1
  rw [hle, Subgroup.mem_bot] at hkN
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hkN)

theorem eq_one_or_eq_t_of_mem_centralizer (hs : Sector L S t) (hcard : Nat.card (sg L S) = 2)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) {r : G}
    (hrC : r ∈ centralizer (L : Set G)) (hrH : r ∈ centralizer ({t} : Set G)) : r = 1 ∨ r = t := by
  obtain ⟨-, -, hprod⟩ := oddKer_complement hs
  have hr' : r ∈ (oddKer L : Set G) * (sg L S : Set G) := by rw [hprod]; exact hrC
  obtain ⟨k, hk, u, hu, rfl⟩ := hr'
  have huH : u ∈ centralizer ({t} : Set G) := sg_le_centralizer_t hs hu
  have hkH : k ∈ centralizer ({t} : Set G) := by
    have := Subgroup.mul_mem _ hrH (Subgroup.inv_mem _ huH)
    simpa using this
  have hk1 : k = 1 := by
    have := oddKer_inf_centralizer_eq_bot hs hbal
    have hmem : k ∈ oddKer L ⊓ centralizer ({t} : Set G) := ⟨hk, hkH⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hmem
  show k * u = 1 ∨ k * u = t
  rw [hk1, one_mul]
  exact eq_one_or_eq_t_of_mem_sg hs hcard hu

end CFSG.OddStandard
