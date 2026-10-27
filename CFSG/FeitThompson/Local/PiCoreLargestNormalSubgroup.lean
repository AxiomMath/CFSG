module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import Mathlib.Data.SetLike.Fintype
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {X : Type*} [Group X] {π : Set ℕ}

theorem natCard_sup_dvd (M N : Subgroup X) [M.Normal] :
    Nat.card (M ⊔ N : Subgroup X) ∣ Nat.card M * Nat.card N := by
  have h : Nat.card ((M ⊔ N : Subgroup X) : Set X) * Nat.card (M ⊓ N : Subgroup X)
      = Nat.card M * Nat.card N := by
    rw [Subgroup.normal_mul]
    exact natCard_mul_mul_natCard_inf M N
  rw [SetLike.coe_sort_coe] at h
  exact ⟨_, h.symm⟩

theorem IsPiSubgroup.map_equiv {N : Subgroup X} (hN : IsPiSubgroup π N) (ϕ : X ≃* X) :
    IsPiSubgroup π (N.map ϕ.toMonoidHom) := by
  refine isPiSubgroup_iff.2 fun p hp => ?_
  rw [Subgroup.card_map_of_injective ϕ.injective] at hp
  exact isPiSubgroup_iff.1 hN p hp

variable [Finite X]

theorem IsPiSubgroup.sup {M N : Subgroup X} [M.Normal] (hM : IsPiSubgroup π M)
    (hN : IsPiSubgroup π N) : IsPiSubgroup π (M ⊔ N) := by
  refine isPiSubgroup_iff.2 fun p hp => ?_
  have h2 := Nat.primeFactors_mono (natCard_sup_dvd M N)
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') hp
  rw [Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h2
  rcases Finset.mem_union.1 h2 with h | h
  · exact isPiSubgroup_iff.1 hM p h
  · exact isPiSubgroup_iff.1 hN p h

instance piCore_characteristic (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (piCore π X).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine piCore_le fun N hN hπ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_piCore (hN.map _ ϕ.surjective) (hπ.map_equiv ϕ)

theorem piCore_map_equiv (π : Set ℕ) (X : Type*) [Group X] [Finite X] (ϕ : X ≃* X) :
    (piCore π X).map ϕ.toMonoidHom = piCore π X :=
  Subgroup.characteristic_iff_map_eq.1 (piCore_characteristic π X) ϕ

theorem piCore_normal (π : Set ℕ) (X : Type*) [Group X] [Finite X] : (piCore π X).Normal :=
  Subgroup.normal_of_characteristic _

theorem normal_and_isPiSubgroup_finset_sup (t : Finset (Subgroup X))
    (ht : ∀ N ∈ t, N.Normal ∧ IsPiSubgroup π N) :
    (t.sup id).Normal ∧ IsPiSubgroup π (t.sup id) := by
  refine Finset.sup_induction (p := fun H : Subgroup X => H.Normal ∧ IsPiSubgroup π H)
    ⟨inferInstance, isPiSubgroup_bot π⟩ ?_ ht
  rintro M ⟨hM, hM'⟩ N ⟨hN, hN'⟩
  exact ⟨Subgroup.sup_normal M N, hM'.sup hN'⟩

theorem isPiSubgroup_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    IsPiSubgroup π (piCore π X) := by
  have hfin : {N : Subgroup X | N.Normal ∧ IsPiSubgroup π N}.Finite := Set.toFinite _
  refine (normal_and_isPiSubgroup_finset_sup hfin.toFinset
    fun N hN => hfin.mem_toFinset.1 hN).2.of_le (piCore_le fun N hN hπ => ?_)
  exact Finset.le_sup (f := id) (hfin.mem_toFinset.2 ⟨hN, hπ⟩)

theorem isGreatest_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    IsGreatest {N : Subgroup X | N.Normal ∧ IsPiSubgroup π N} (piCore π X) :=
  ⟨⟨piCore_normal π X, isPiSubgroup_piCore π X⟩, fun _ hN => le_piCore hN.1 hN.2⟩

instance pCore_characteristic (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pCore p X).Characteristic := by
  rw [pCore_eq_piCore]; infer_instance

instance pComplCore_characteristic (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplCore p X).Characteristic := by
  rw [pComplCore_eq_piCore]; infer_instance

theorem isPGroup_pCore {p : ℕ} (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    IsPGroup p (pCore p X) := by
  rw [pCore_eq_piCore]
  exact (isPiSubgroup_singleton_iff hp _).1 (isPiSubgroup_piCore _ X)

theorem not_dvd_natCard_pComplCore {p : ℕ} (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    ¬ p ∣ Nat.card (pComplCore p X) := by
  intro hdvd
  have hmem : p ∈ (Nat.card (pComplCore p X)).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩
  rw [pComplCore_eq_piCore] at hmem
  exact (isPiSubgroup_iff.1 (isPiSubgroup_piCore _ X) p hmem).2 rfl

end CFSG.FeitThompson
