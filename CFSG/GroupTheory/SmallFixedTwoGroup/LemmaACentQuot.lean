module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup
open CFSG.GH74.GLS.Stage1.Thm6.Sec13 (cls card_cls_mul')

theorem card_centralizer_quotient_le {R : Type*} [Group R] [Finite R] (N : Subgroup R)
    [N.Normal] (z : R) :
    Nat.card (centralizer ({(QuotientGroup.mk z : R ⧸ N)} : Set (R ⧸ N))) ≤
      Nat.card (centralizer ({z} : Set R)) := by
  set Cq := centralizer ({(QuotientGroup.mk z : R ⧸ N)} : Set (R ⧸ N)) with hCq
  set D : Subgroup R := Cq.comap (QuotientGroup.mk' N) with hD
  have hmem : ∀ r : R, r ∈ D ↔ (QuotientGroup.mk r : R ⧸ N) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk r := by
    intro r
    show QuotientGroup.mk' N r ∈ Cq ↔ _
    rw [hCq, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hCle : centralizer ({z} : Set R) ≤ D := by
    intro g hg
    rw [hmem]
    have := mem_centralizer_iff.1 hg z rfl
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  have h1 : Nat.card D = Nat.card N * Nat.card Cq := by
    have e1 := Subgroup.card_mul_index D
    have e2 := Subgroup.card_mul_index Cq
    have e3 := Subgroup.index_comap_of_surjective Cq (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
    have e4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hi : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← hD] at e3
    have : Nat.card D * D.index = Nat.card N * Nat.card Cq * D.index := by
      rw [e1, e4, ← e2, e3]; ring
    exact Nat.eq_of_mul_eq_mul_right hi this
  have h2 := card_cls_mul' D z
  have h3 : D ⊓ centralizer ({z} : Set R) = centralizer ({z} : Set R) := inf_eq_right.2 hCle
  rw [h3] at h2
  have hsub : cls D z ⊆ (fun n => z * n) '' (N : Set R) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' := (hmem r).1 hr
    refine ⟨z⁻¹ * (r * z * r⁻¹), ?_, by group⟩
    have : (QuotientGroup.mk (r * z * r⁻¹) : R ⧸ N) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hr', QuotientGroup.mk_inv]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    exact (QuotientGroup.eq).1 this.symm
  have h4 : Nat.card (cls D z) ≤ Nat.card N := by
    have a1 : Nat.card (cls D z) = (cls D z).ncard := (Nat.card_coe_set_eq _).symm
    have a2 : (cls D z).ncard ≤ ((fun n => z * n) '' (N : Set R)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have a3 : ((fun n => z * n) '' (N : Set R)).ncard ≤ (N : Set R).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have a4 : (N : Set R).ncard = Nat.card N := Nat.card_coe_set_eq _
    omega
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have h5 : Nat.card N * Nat.card Cq ≤
      Nat.card N * Nat.card (centralizer ({z} : Set R)) := by
    calc Nat.card N * Nat.card Cq = Nat.card D := h1.symm
      _ = Nat.card (cls D z) * Nat.card (centralizer ({z} : Set R)) := h2.symm
      _ ≤ Nat.card N * Nat.card (centralizer ({z} : Set R)) := Nat.mul_le_mul_right _ h4
  exact Nat.le_of_mul_le_mul_left h5 hNpos

end CFSG.GroupTheory.SmallFixedTwoGroup
