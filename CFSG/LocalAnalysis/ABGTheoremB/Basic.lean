module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public noncomputable section

namespace CFSG.ABGTheoremB

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def oddCoreIn (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore H).map H.subtype

@[expose] def solvRadIn (H : Subgroup G) : Subgroup G :=
  (CFSG.solvableRadical H).map H.subtype

@[expose] def pCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (CFSG.pCore p H).map H.subtype

@[expose] def pPrimeCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore p H).map H.subtype

@[expose] def pPrimePCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (CFSG.Op_p'p p H).map H.subtype

@[expose] def IsPLocal (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup p R ∧ H = Subgroup.normalizer (R : Set G)

@[expose] def signalizers (H X : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {R | R ≤ H ∧ IsPGroup p R ∧ X ≤ Subgroup.normalizer (R : Set G) ∧ R ⊓ X = ⊥}

@[expose] def signalizersPerm (H X Y : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {R | R ∈ signalizers H X p ∧ (R : Set G) * (Y : Set G) = (Y : Set G) * (R : Set G)}

@[expose] def maximals (𝓢 : Set (Subgroup G)) : Set (Subgroup G) :=
  {R | R ∈ 𝓢 ∧ ∀ R' ∈ 𝓢, R ≤ R' → R' = R}

theorem oddCoreIn_le (H : Subgroup G) : oddCoreIn H ≤ H :=
  Subgroup.map_subtype_le _

theorem solvRadIn_le (H : Subgroup G) : solvRadIn H ≤ H :=
  Subgroup.map_subtype_le _

theorem pCoreIn_le (p : ℕ) (H : Subgroup G) : pCoreIn p H ≤ H :=
  Subgroup.map_subtype_le _

theorem pPrimeCoreIn_le (p : ℕ) (H : Subgroup G) : pPrimeCoreIn p H ≤ H :=
  Subgroup.map_subtype_le _

theorem pPrimePCoreIn_le (p : ℕ) (H : Subgroup G) : pPrimePCoreIn p H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_normalizer_map_subtype (H : Subgroup G) (K : Subgroup H) [K.Normal] :
    H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

theorem le_normalizer_oddCoreIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
  le_normalizer_map_subtype H (CFSG.oddCore H)

theorem odd_card_oddCore (K : Type*) [Group K] [Finite K] : Odd (Nat.card (CFSG.oddCore K)) :=
  CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

theorem odd_card_oddCoreIn [Finite G] (H : Subgroup G) : Odd (Nat.card (oddCoreIn H)) := by
  rw [oddCoreIn, Nat.card_congr ((CFSG.oddCore H).equivMapOfInjective H.subtype
    H.subtype_injective).toEquiv.symm]
  exact odd_card_oddCore H

theorem le_oddCoreIn {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal := by
    constructor
    intro a ha h
    have hmem := (Subgroup.mem_normalizer_iff.mp (hnorm h.property)) a
    exact hmem.mp ha
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

end CFSG.ABGTheoremB
