module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsSylow2Of (S H : Subgroup G) : Prop :=
  S ≤ H ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex H

@[expose] def IsMaxElemAbelianIn (S A : Subgroup G) : Prop :=
  A ≤ S ∧ CFSG.Open.IsElemAbelian 2 A ∧
    ∀ B : Subgroup G, B ≤ S → CFSG.Open.IsElemAbelian 2 B → Nat.card B ≤ Nat.card A

@[expose] def centerIn (L : Subgroup G) : Subgroup G :=
  (Subgroup.center L).map L.subtype

@[expose] noncomputable def ctrQ (X : Subgroup G) : ℕ :=
  Nat.card (X ⧸ center X)

@[expose] def conjClassIn (H : Subgroup G) (x : G) : Set G :=
  {y | ∃ h ∈ H, y = h * x * h⁻¹}

structure Asc82Notation {G : Type} [Group G] (t : G) (L : Subgroup G) (S : Subgroup G) (z : G) :
    Prop where
  sylow : IsSylow2Of S (centralizer ({t} : Set G))
  mem_S : z ∈ S
  central : ∀ s ∈ S, s * z = z * s
  pocket : IsI4PlusIn L z

theorem IsSylow2Of.exists_sylow {S H : Subgroup G} (h : IsSylow2Of S H) :
    ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H).map H.subtype = S := by
  obtain ⟨hle, hp, hndvd⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : IsPGroup 2 ↥(S.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hnd : ¬ 2 ∣ (S.subgroupOf H).index := hndvd
  refine ⟨hP0.toSylow hnd, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subgroupOf_eq_of_le hle

theorem isSylow2Of_map_sylow [Finite G] {H : Subgroup G} (P : Sylow 2 ↥H) :
    IsSylow2Of ((P : Subgroup ↥H).map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact (P.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)
  · have h : ((P : Subgroup ↥H).map H.subtype).subgroupOf H = (P : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, h]
    exact P.not_dvd_index

end CFSG.OddStandard.SmallF3.Omega
