module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.ABGLocalTools
open scoped MatrixGroups

section SL2

variable {G : Type*} [Group G]

theorem localNormalizer_coatom_of {N : Type*} [Finite G] [Group N] {T L : Subgroup G}
    (hU : IsSylowOf 2 (T ⊓ L) L) (θ : ↥L ≃* N) {m : ℕ}
    (hS : ∀ Q' : Sylow 2 N, IsCoatom (Subgroup.normalizer ((Q' : Subgroup N) : Set N)) ∧
      (Subgroup.normalizer ((Q' : Subgroup N) : Set N)).index = m) :
    localNormalizer T L < L ∧ (∀ Y : Subgroup G, localNormalizer T L ≤ Y → Y ≤ L →
      Y = localNormalizer T L ∨ Y = L) ∧ (localNormalizer T L).relIndex L = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  let Q' : Sylow 2 N := Q.mapSurjective (f := θ.toMonoidHom) θ.surjective
  have hQ' : (Q' : Subgroup N) = (Q : Subgroup ↥L).map θ.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hcoat, hidx⟩ := hS Q'
  have hTL : T ⊓ L ≤ L := inf_le_right
  let N' : Subgroup ↥L := (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)).subgroupOf L
  have hNQ : Subgroup.normalizer ((Q' : Subgroup N) : Set N) = N'.map θ.toMonoidHom := by
    rw [hQ', ← Subgroup.map_normalizer_eq_of_bijective _ θ.bijective, hQ,
      normalizer_subgroupOf_eq hTL]
  have hloc : localNormalizer T L = N'.map L.subtype := by
    unfold localNormalizer
    rw [Subgroup.subgroupOf_map_subtype]
  have hcoat' : IsCoatom N' := by
    rw [hNQ] at hcoat
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup θ) N').1 hcoat
  have hidx' : N'.index = m := by
    rw [hNQ] at hidx
    rw [← hidx]
    exact (Subgroup.index_map_equiv N' θ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hloc]
    have h1 : N' < ⊤ := hcoat'.lt_top
    have := (Subgroup.map_lt_map_iff_of_injective L.subtype_injective).2 h1
    rwa [map_top_subtype] at this
  · intro Y hNY hYL
    have h1 : N' ≤ Y.subgroupOf L := by
      intro x hx
      have : (x : G) ∈ localNormalizer T L := by
        rw [hloc]
        exact ⟨x, hx, rfl⟩
      exact hNY this
    rcases hcoat'.le_iff.1 h1 with h | h
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hYL, h, map_top_subtype]
    · left
      rw [hloc, ← h, Subgroup.map_subgroupOf_eq_of_le hYL]
  · rw [hloc]
    show ((N'.map L.subtype).subgroupOf L).index = m
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    exact hidx'

theorem charP_two_of_card_pow {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨k, hk, hpk⟩ := FiniteField.card F p
  have h1 : p ^ (k : ℕ) = 2 ^ n := by rw [← hpk, hF]
  have : p ∣ 2 ^ n := by
    rw [← h1]
    exact dvd_pow_self p k.pos.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow this)
  subst hp2
  exact hp

theorem localNormalizer_coatom [Finite G] {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {T L : Subgroup G} (hU : IsSylowOf 2 (T ⊓ L) L)
    (θ : ↥L ≃* SL(2, F)) :
    localNormalizer T L < L ∧ (∀ Y : Subgroup G, localNormalizer T L ≤ Y → Y ≤ L →
      Y = localNormalizer T L ∨ Y = L) ∧ (localNormalizer T L).relIndex L = 2 ^ n + 1 := by
  have : CharP F 2 := charP_two_of_card_pow hF
  refine localNormalizer_coatom_of hU θ (m := 2 ^ n + 1) fun Q' => ?_
  obtain ⟨g, -, -, hcoat, -, hidx⟩ :=
    (SL2Modules.sl2_defining_characteristic_Sylow_normalizer_maximal_Borel (F := F)
      (p := 2)).2.2.2.2.2.2.2 Q'
  exact ⟨hcoat, by rw [hidx, hF]⟩

end SL2

end CFSG.QuasithinUnique.Setup.Lift
