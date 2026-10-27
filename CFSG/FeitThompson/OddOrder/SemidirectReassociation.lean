module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {M : Type*} [Group M] {J B H U : Subgroup M}

theorem disjoint_of_isComplement'_of_sup_eq (hJB : J.IsComplement' B) (hsup : H ⊔ U = J) :
    Disjoint U B :=
  hJB.disjoint.mono_left (hsup ▸ le_sup_right)

theorem normal_subgroupOf_sup (hBU : B ≤ normalizer (U : Set M)) :
    (U.subgroupOf (U ⊔ B)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hBU)

theorem isComplement'_subgroupOf_sup (hBU : B ≤ normalizer (U : Set M)) (hUB : Disjoint U B) :
    (U.subgroupOf (U ⊔ B)).IsComplement' (B.subgroupOf (U ⊔ B)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    exact Subtype.ext (Subgroup.disjoint_def.mp hUB hx1 hx2)
  · ext x
    simp only [Set.mem_univ, iff_true]
    have hx : (x : M) ∈ ((U ⊔ B : Subgroup M) : Set M) := x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U B hBU] at hx
    obtain ⟨u, hu, b, hb, hub⟩ := hx
    exact Set.mem_mul.2 ⟨⟨u, mem_sup_left hu⟩, Subgroup.mem_subgroupOf.2 hu,
      ⟨b, mem_sup_right hb⟩, Subgroup.mem_subgroupOf.2 hb, Subtype.ext hub⟩

theorem isComplement'_sup [H.Normal] (hJB : J.IsComplement' B) (hsup : H ⊔ U = J)
    (hHU : Disjoint H U) (hBU : B ≤ normalizer (U : Set M)) :
    H.IsComplement' (U ⊔ B) := by
  have hHJ : H ≤ J := hsup ▸ le_sup_left
  have hUJ : U ≤ J := hsup ▸ le_sup_right
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxA
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left U B hBU] at hxA
    obtain ⟨u, hu, b, hb, rfl⟩ := hxA
    have hbJ : b ∈ J := by
      have : u⁻¹ * (u * b) ∈ J := J.mul_mem (J.inv_mem (hUJ hu)) (hHJ hxH)
      simpa using this
    have hb1 : b = 1 := Subgroup.disjoint_def.mp hJB.disjoint hbJ hb
    subst hb1
    simpa using Subgroup.disjoint_def.mp hHU (by simpa using hxH) hu
  · calc (H : Set M) * ((U ⊔ B : Subgroup M) : Set M)
        = (H : Set M) * ((U : Set M) * (B : Set M)) := by
          rw [Subgroup.coe_mul_of_right_le_normalizer_left U B hBU]
      _ = ((H : Set M) * (U : Set M)) * (B : Set M) := (mul_assoc _ _ _).symm
      _ = ((H ⊔ U : Subgroup M) : Set M) * (B : Set M) := by rw [← Subgroup.normal_mul H U]
      _ = (J : Set M) * (B : Set M) := by rw [hsup]
      _ = Set.univ := hJB.mul_eq

theorem index_eq_natCard_sup [H.Normal] (hJB : J.IsComplement' B) (hsup : H ⊔ U = J)
    (hHU : Disjoint H U) (hBU : B ≤ normalizer (U : Set M)) :
    H.index = Nat.card (U ⊔ B : Subgroup M) :=
  (isComplement'_sup hJB hsup hHU hBU).symm.index_eq_card

theorem natCard_mul_natCard_sup [H.Normal] (hJB : J.IsComplement' B) (hsup : H ⊔ U = J)
    (hHU : Disjoint H U) (hBU : B ≤ normalizer (U : Set M)) :
    Nat.card H * Nat.card (U ⊔ B : Subgroup M) = Nat.card M :=
  (isComplement'_sup hJB hsup hHU hBU).card_mul_card

theorem coprime_natCard_sup [H.Normal] (hJB : J.IsComplement' B) (hsup : H ⊔ U = J)
    (hHU : Disjoint H U) (hBU : B ≤ normalizer (U : Set M))
    (hHall : (Nat.card H).Coprime H.index) :
    (Nat.card H).Coprime (Nat.card (U ⊔ B : Subgroup M)) := by
  rwa [index_eq_natCard_sup hJB hsup hHU hBU] at hHall

theorem natCard_sup_of_le_normalizer (hBU : B ≤ normalizer (U : Set M)) (hUB : Disjoint U B) :
    Nat.card (U ⊔ B : Subgroup M) = Nat.card U * Nat.card B := by
  have h := natCard_mul_mul_natCard_inf U B
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left U B hBU, disjoint_iff.mp hUB] at h
  simpa using h

end

end CFSG.FeitThompson
