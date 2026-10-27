module

public import Mathlib.GroupTheory.Sylow

public section

open Subgroup

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def IsSylowOf (p : ℕ) (P K : Subgroup G) : Prop :=
  ∃ Q : Sylow p K, (Q : Subgroup K).map K.subtype = P

theorem relIndex_sup_eq_relIndex_of_normal [Finite G] (N P : Subgroup G) [N.Normal] :
    P.relIndex (N ⊔ P) = P.relIndex N := by
  have h1 := Subgroup.relIndex_mul_card P (N ⊔ P)
  have h2 := Subgroup.relIndex_mul_card N (N ⊔ P)
  have h3 := Subgroup.relIndex_mul_card N P
  have h4 := Subgroup.relIndex_mul_card P N
  have h5 : N.relIndex (N ⊔ P) = N.relIndex P := Subgroup.relIndex_sup_left P N
  rw [inf_eq_left.mpr (le_sup_right : P ≤ N ⊔ P)] at h1
  rw [inf_eq_left.mpr (le_sup_left : N ≤ N ⊔ P), h5] at h2
  rw [inf_comm] at h4
  have hpos : 0 < N.relIndex P * Nat.card (N ⊓ P : Subgroup G) := by
    rw [h3]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc P.relIndex (N ⊔ P) * (N.relIndex P * Nat.card (N ⊓ P : Subgroup G))
      = P.relIndex (N ⊔ P) * Nat.card P := by rw [h3]
    _ = N.relIndex P * Nat.card N := by rw [h1, h2]
    _ = P.relIndex N * (N.relIndex P * Nat.card (N ⊓ P : Subgroup G)) := by
        rw [← h4]
        ring

namespace IsSylowOf

variable {p : ℕ} {P K N : Subgroup G}

theorem le (h : IsSylowOf p P K) : P ≤ K := by
  obtain ⟨Q, rfl⟩ := h
  exact Subgroup.map_subtype_le _

theorem isPGroup (h : IsSylowOf p P K) : IsPGroup p P := by
  obtain ⟨Q, rfl⟩ := h
  exact Q.isPGroup'.map K.subtype

theorem exists_sylow_eq_subgroupOf (h : IsSylowOf p P K) :
    ∃ Q : Sylow p K, (Q : Subgroup K) = P.subgroupOf K := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q, ?_⟩
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

end IsSylowOf

variable {p : ℕ}

theorem isSylowOf_iff [Finite G] [Fact p.Prime] {P K : Subgroup G} :
    IsSylowOf p P K ↔ P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K := by
  constructor
  · intro h
    refine ⟨h.le, h.isPGroup, ?_⟩
    obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
    have := Q.not_dvd_index
    rwa [hQ] at this
  · rintro ⟨hle, hP, hdvd⟩
    have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
    have hdvd' : ¬ p ∣ (P.subgroupOf K).index := hdvd
    refine ⟨hP'.toSylow hdvd', ?_⟩
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]

theorem exists_isSylowOf [Finite G] (p : ℕ) [Fact p.Prime] (K : Subgroup G) :
    ∃ P : Subgroup G, IsSylowOf p P K := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p K))
  exact ⟨_, Q, rfl⟩

theorem IsSylowOf.card_eq [Finite G] [Fact p.Prime] {P K : Subgroup G} (h : IsSylowOf p P K) :
    Nat.card P = p ^ (Nat.card K).factorization p := by
  obtain ⟨Q, rfl⟩ := h
  rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity]

theorem isSylowOf_of_card [Finite G] [Fact p.Prime] {P K : Subgroup G} (hle : P ≤ K)
    (hcard : Nat.card P = p ^ (Nat.card K).factorization p) : IsSylowOf p P K := by
  have hcard' : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  refine ⟨Sylow.ofCard (P.subgroupOf K) hcard', ?_⟩
  rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]

theorem IsSylowOf.eq_of_le [Finite G] [Fact p.Prime] {P Q K : Subgroup G} (h : IsSylowOf p P K)
    (hPQ : P ≤ Q) (hQK : Q ≤ K) (hQ : IsPGroup p Q) : Q = P := by
  obtain ⟨S, hS⟩ := h.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  have hle : (S : Subgroup K) ≤ Q.subgroupOf K := by
    rw [hS]
    exact fun x hx => hPQ hx
  have heq : Q.subgroupOf K = (S : Subgroup K) := S.3 hQ' hle
  apply le_antisymm _ hPQ
  intro x hx
  have hx' : (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K := hx
  rw [heq, hS] at hx'
  exact hx'

theorem IsSylowOf.inf_of_le_normalizer [Finite G] [Fact p.Prime] {P K N : Subgroup G}
    (h : IsSylowOf p P K) (hNK : N ≤ K) (hKN : K ≤ normalizer (N : Set G)) :
    IsSylowOf p (P ⊓ N) N := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨_, hP, hdvd⟩ := h
  refine ⟨inf_le_right, hP.to_inf_left, ?_⟩
  rw [Subgroup.inf_relIndex_right]
  have : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  rw [← Subgroup.relIndex_subgroupOf hNK,
    ← relIndex_sup_eq_relIndex_of_normal (N.subgroupOf K) (P.subgroupOf K)]
  intro hdvd'
  exact hdvd (hdvd'.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))

theorem IsSylowOf.of_le [Finite G] [Fact p.Prime] {P K L : Subgroup G} (h : IsSylowOf p P K)
    (hPL : P ≤ L) (hLK : L ≤ K) : IsSylowOf p P L := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨_, hP, hdvd⟩ := h
  refine ⟨hPL, hP, fun hdvd' => hdvd ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P L K hPL hLK]
  exact hdvd'.mul_right _

theorem isSylowOf_map_subtype_iff [Finite G] [Fact p.Prime] (K : Subgroup G) {A B : Subgroup K} :
    IsSylowOf p (A.map K.subtype) (B.map K.subtype) ↔ IsSylowOf p A B := by
  rw [isSylowOf_iff, isSylowOf_iff, Subgroup.map_le_map_iff_of_injective K.subtype_injective,
    Subgroup.relIndex_map_map, Subgroup.ker_subtype, sup_bot_eq, sup_bot_eq]
  constructor
  · rintro ⟨hle, hA, hdvd⟩
    exact ⟨hle, hA.of_equiv (Subgroup.equivMapOfInjective A K.subtype K.subtype_injective).symm,
      hdvd⟩
  · rintro ⟨hle, hA, hdvd⟩
    exact ⟨hle, hA.map K.subtype, hdvd⟩

end CFSG.ABGLocalTools
