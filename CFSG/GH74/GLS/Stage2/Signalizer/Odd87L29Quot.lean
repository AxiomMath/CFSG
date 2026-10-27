module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29Quot

section Abstract

variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem comap_pPrimeCore_of_odd_ker (φ : A →* B) (hφ : Function.Surjective φ)
    (hk : Odd (Nat.card φ.ker)) :
    (pPrimeCore 2 B).comap φ = pPrimeCore 2 A :=
  (prime_complement_kernel_core_preimage (p := 2) φ hφ hk.not_two_dvd_nat).1

theorem map_pPrimeCore_of_odd_ker (φ : A →* B) (hφ : Function.Surjective φ)
    (hk : Odd (Nat.card φ.ker)) :
    (pPrimeCore 2 A).map φ = pPrimeCore 2 B :=
  (prime_complement_kernel_core_preimage (p := 2) φ hφ hk.not_two_dvd_nat).2

theorem comap_pPrimePCore_of_odd_ker (φ : A →* B) (hφ : Function.Surjective φ)
    (hk : Odd (Nat.card φ.ker)) :
    (pPrimePCore 2 B).comap φ = pPrimePCore 2 A := by
  have h1 := comap_pPrimeCore_of_odd_ker φ hφ hk
  have hψ : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 B)).comp φ) :=
    (QuotientGroup.mk'_surjective _).comp hφ
  have hker : ((QuotientGroup.mk' (pPrimeCore 2 B)).comp φ).ker = pPrimeCore 2 A := by
    rw [← h1]
    ext a
    simp [QuotientGroup.eq_one_iff]
  let e : (A ⧸ pPrimeCore 2 A) ≃* (B ⧸ pPrimeCore 2 B) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hψ)
  have hcore := pCore_map_iso 2 e
  have hψe : (QuotientGroup.mk' (pPrimeCore 2 B)).comp φ =
      e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A)) := by
    ext y; rfl
  unfold pPrimePCore
  rw [Subgroup.comap_comap, hψe, ← Subgroup.comap_comap, ← hcore,
    Subgroup.comap_map_eq_self_of_injective e.injective]

theorem map_pPrimePCore_of_odd_ker (φ : A →* B) (hφ : Function.Surjective φ)
    (hk : Odd (Nat.card φ.ker)) :
    (pPrimePCore 2 A).map φ = pPrimePCore 2 B := by
  rw [← comap_pPrimePCore_of_odd_ker φ hφ hk, Subgroup.map_comap_eq_self_of_surjective hφ]

end Abstract

section Restrict

variable {C E : Type} [Group C] [Group E]

theorem odd_card_ker_subgroupMap (π : C →* E) (D : Subgroup C)
    (hD : Odd (Nat.card ↥(D ⊓ π.ker))) : Odd (Nat.card (π.subgroupMap D).ker) := by
  have h : (π.subgroupMap D).ker = (D ⊓ π.ker).subgroupOf D := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
  rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ π.ker ≤ D)).toEquiv]
  exact hD

theorem map_map_subtype_eq (π : C →* E) (D : Subgroup C) (S : Subgroup ↥D) :
    (S.map D.subtype).map π = (S.map (π.subgroupMap D)).map (D.map π).subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem inf_comap_map_subtype (π : C →* E) (D : Subgroup C) (S : Subgroup ↥(D.map π)) :
    D ⊓ (S.map (D.map π).subtype).comap π = (S.comap (π.subgroupMap D)).map D.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨hxD, y, hy, hyx⟩
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    have : π.subgroupMap D ⟨x, hxD⟩ = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  · rintro ⟨⟨z, hz⟩, hzS, rfl⟩
    exact ⟨hz, π.subgroupMap D ⟨z, hz⟩, hzS, rfl⟩

end Restrict

end L29Quot

section Quot

variable {C E : Type} [Group C] [Group E] [Finite C] [Finite E]

theorem map_pPrimeCoreOf_of_odd (π : C →* E) (D : Subgroup C)
    (hD : Odd (Nat.card ↥(D ⊓ π.ker))) :
    (pPrimeCoreOf 2 D).map π = pPrimeCoreOf 2 (D.map π) := by
  unfold pPrimeCoreOf
  rw [L29Quot.map_map_subtype_eq, L29Quot.map_pPrimeCore_of_odd_ker _
    (π.subgroupMap_surjective D) (L29Quot.odd_card_ker_subgroupMap π D hD)]

theorem map_O22Of_of_odd (π : C →* E) (D : Subgroup C)
    (hD : Odd (Nat.card ↥(D ⊓ π.ker))) :
    (O22Of D).map π = O22Of (D.map π) := by
  unfold O22Of
  rw [L29Quot.map_map_subtype_eq, L29Quot.map_pPrimePCore_of_odd_ker _
    (π.subgroupMap_surjective D) (L29Quot.odd_card_ker_subgroupMap π D hD)]

theorem comap_pPrimeCoreOf_of_odd (π : C →* E) (D : Subgroup C)
    (hD : Odd (Nat.card ↥(D ⊓ π.ker))) :
    D ⊓ (pPrimeCoreOf 2 (D.map π)).comap π = pPrimeCoreOf 2 D := by
  unfold pPrimeCoreOf
  rw [L29Quot.inf_comap_map_subtype, L29Quot.comap_pPrimeCore_of_odd_ker _
    (π.subgroupMap_surjective D) (L29Quot.odd_card_ker_subgroupMap π D hD)]

theorem comap_O22Of_of_odd (π : C →* E) (D : Subgroup C)
    (hD : Odd (Nat.card ↥(D ⊓ π.ker))) :
    D ⊓ (O22Of (D.map π)).comap π = O22Of D := by
  unfold O22Of
  rw [L29Quot.inf_comap_map_subtype, L29Quot.comap_pPrimePCore_of_odd_ker _
    (π.subgroupMap_surjective D) (L29Quot.odd_card_ker_subgroupMap π D hD)]

end Quot

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
