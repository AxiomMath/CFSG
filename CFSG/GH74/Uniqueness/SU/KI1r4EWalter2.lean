module

public import CFSG.GH74.Uniqueness.SU.KI1r4EWalter

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup
open scoped commutatorElement

theorem card_eq_mul_card_map_mk {M : Type} [Group M] [Finite M] (Φ W : Subgroup M) [Φ.Normal]
    (hΦW : Φ ≤ W) : Nat.card W = Nat.card Φ * Nat.card (W.map (QuotientGroup.mk' Φ)) := by
  set f : ↥W →* M ⧸ Φ := (QuotientGroup.mk' Φ).comp W.subtype with hf
  have hrange : f.range = W.map (QuotientGroup.mk' Φ) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = Φ.subgroupOf W := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (u : M)
  have hkerc : Nat.card f.ker = Nat.card Φ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΦW).toEquiv
  have h := Subgroup.card_ker_mul_card_range f
  rw [hkerc, hrange] at h
  exact h.symm

theorem false_of_sylow_over_center
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (hZ2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥) (P : Sylow 2 K)
    (hcomm : ∀ a ∈ (P : Subgroup K), ∀ b ∈ (P : Subgroup K), ⁅a, b⁆ ∈ center K)
    (hcard : Nat.card (P : Subgroup K) = 16 * Nat.card (center K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : K →* K ⧸ center K := QuotientGroup.mk' (center K) with hπ
  have hZP : center K ≤ (P : Subgroup K) := hZ2.le_sylow_of_normal P
  have hPbcard : Nat.card ((P : Subgroup K).map π) = 16 := by
    have h := card_eq_mul_card_map_mk (center K) (P : Subgroup K) hZP
    have hpos : 0 < Nat.card (center K) := Nat.card_pos
    rw [hcard] at h
    have h2 : Nat.card (center K) * 16 = Nat.card (center K) * Nat.card ((P : Subgroup K).map π) := by
      rw [mul_comm]; exact h
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hZ2
  have hKcard : Nat.card K = Nat.card (K ⧸ center K) * Nat.card (center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  have hPcard : Nat.card (P : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
    P.card_eq_multiplicity
  have hfac : (Nat.card K).factorization 2 = (Nat.card (K ⧸ center K)).factorization 2 + j := by
    rw [hKcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', hj]
    simp [Nat.Prime.factorization_pow Nat.prime_two]
  have hPbsyl : Nat.card ((P : Subgroup K).map π) =
      2 ^ (Nat.card (K ⧸ center K)).factorization 2 := by
    have h1 : 2 ^ ((Nat.card K).factorization 2) = 16 * 2 ^ j := by
      rw [← hPcard, hcard, hj]
    rw [hfac, pow_add] at h1
    have hpos : 0 < 2 ^ j := by positivity
    have h2 : 2 ^ (Nat.card (K ⧸ center K)).factorization 2 * 2 ^ j = 16 * 2 ^ j := h1
    have := Nat.eq_of_mul_eq_mul_right hpos h2
    rw [hPbcard, this]
  let Pb : Sylow 2 (K ⧸ center K) := Sylow.ofCard ((P : Subgroup K).map π) hPbsyl
  have hPbcomm : IsMulCommutative (Pb : Subgroup (K ⧸ center K)) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha'e⟩ := a.2
    obtain ⟨b', hb', hb'e⟩ := b.2
    apply Subtype.ext
    show (a : K ⧸ center K) * b = b * a
    rw [← ha'e, ← hb'e]
    have h1 : π ⁅a', b'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm a' ha' b' hb')
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
    exact h1.eq
  exact false_of_central_quotient_sylow_sixteen hq hZ2 hZ Pb hPbcomm hPbcard

end CFSG.GH74.Uniqueness.SU.K.R4
