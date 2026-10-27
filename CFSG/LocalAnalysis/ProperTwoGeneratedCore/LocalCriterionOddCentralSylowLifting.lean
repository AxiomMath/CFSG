module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementProduct

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII

variable {K : Type*} [Group K]

theorem odd_central_quotient_subgroup_factorization
    (J A : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJA : J ≤ A)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    ∀ a ∈ A, ∃ c ∈ A ⊓ Subgroup.centralizer ({t} : Set K),
      ∃ j ∈ J, c * j = a := by
  let q := QuotientGroup.mk' J
  have hkernel : Odd (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using hJodd
  have htinvolution : IsInvolution t :=
    ⟨(orderOf_eq_prime_iff.mp ht).2, (orderOf_eq_prime_iff.mp ht).1⟩
  have hmap := involution_centralizer_image q (QuotientGroup.mk'_surjective J)
    hkernel htinvolution
  intro a ha
  have hqa : q a ∈ Subgroup.centralizer ({q t} : Set (K ⧸ J)) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_center_iff.mp hcentral (q a))
  rw [← hmap] at hqa
  obtain ⟨c, hct, hca⟩ := hqa
  have hj : c⁻¹ * a ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (c⁻¹ * a) = 1
    rw [map_mul, map_inv, hca, inv_mul_cancel]
  have hcA : c ∈ A := by
    have hm := A.mul_mem ha (A.inv_mem (hJA hj))
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one, inv_inv] using hm
  exact ⟨c, ⟨hcA, hct⟩, c⁻¹ * a, hj, mul_inv_cancel_left c a⟩

theorem odd_central_quotient_subgroup_sup
    (J A : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJA : J ≤ A)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    (A ⊓ Subgroup.centralizer ({t} : Set K)) ⊔ J = A := by
  apply le_antisymm (sup_le inf_le_left hJA)
  intro a ha
  obtain ⟨c, hc, j, hj, hprod⟩ :=
    odd_central_quotient_subgroup_factorization J A t ht hJodd hJA hcentral a ha
  exact Subgroup.mem_sup_of_normal_right.mpr ⟨c, hc, j, hj, hprod⟩

theorem odd_central_quotient_subgroup_normalized
    (J A : Subgroup K) [J.Normal] (t : K) (hJA : J ≤ A)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set K) := by
  apply Subgroup.zpowers_le.mpr
  apply (Subgroup.mem_normalizer_iff_map_conj_eq).mpr
  apply le_antisymm
  · rintro a ⟨b, hb, rfl⟩
    let q := QuotientGroup.mk' J
    have hcomm : Commute (q t) (q b) :=
      (Subgroup.mem_center_iff.mp hcentral (q b)).symm
    have hdiff : (t * b * t⁻¹) * b⁻¹ ∈ J := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((t * b * t⁻¹) * b⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hcomm.eq]
      group
    have hm := A.mul_mem (hJA hdiff) hb
    change t * b * t⁻¹ ∈ A
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  · intro a ha
    let q := QuotientGroup.mk' J
    have hcomm : Commute (q t) (q a) :=
      (Subgroup.mem_center_iff.mp hcentral (q a)).symm
    have hdiff : (t⁻¹ * a * t) * a⁻¹ ∈ J := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((t⁻¹ * a * t) * a⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [mul_assoc (q t)⁻¹ (q a) (q t), ← hcomm.eq]
      group
    have hpre : t⁻¹ * a * t ∈ A := by
      have hm := A.mul_mem (hJA hdiff) ha
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
    refine ⟨t⁻¹ * a * t, hpre, ?_⟩
    change t * (t⁻¹ * a * t) * t⁻¹ = a
    group

theorem odd_central_quotient_subgroup_centralizer_index [Finite K]
    (J A : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJA : J ≤ A)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    (Subgroup.centralizer ({t} : Set K)).relIndex A =
      (Subgroup.centralizer ({t} : Set K)).relIndex J := by
  let C := Subgroup.centralizer ({t} : Set K)
  have hmeet : J ⊓ (A ⊓ C) = J ⊓ C := by
    ext a
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hJA h.1, h.2⟩⟩
  have hcard := CFSG.RankThreeEvenClassification.Helpers.normalized_sup_card_mul_inf
    J (A ⊓ C) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  rw [sup_comm J, odd_central_quotient_subgroup_sup J A t ht hJodd hJA hcentral,
    hmeet] at hcard
  have hAcard := C.relIndex_mul_card A
  have hJcard := C.relIndex_mul_card J
  rw [inf_comm C A] at hAcard
  rw [inf_comm C J] at hJcard
  apply Nat.mul_right_cancel (Nat.card_pos (α := ↥(J ⊓ C)))
  apply Nat.mul_right_cancel (Nat.card_pos (α := ↥(A ⊓ C)))
  calc
    C.relIndex A * Nat.card (J ⊓ C : Subgroup K) *
        Nat.card (A ⊓ C : Subgroup K) =
      Nat.card A * Nat.card (J ⊓ C : Subgroup K) := by
        rw [mul_right_comm, hAcard]
    _ = Nat.card J * Nat.card (A ⊓ C : Subgroup K) := hcard
    _ = C.relIndex J * Nat.card (J ⊓ C : Subgroup K) *
        Nat.card (A ⊓ C : Subgroup K) := by rw [hJcard]

theorem odd_central_quotient_subgroup_centralizer_index_odd [Finite K]
    (J A : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJA : J ≤ A)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    Odd ((Subgroup.centralizer ({t} : Set K)).relIndex A) := by
  rw [odd_central_quotient_subgroup_centralizer_index J A t ht hJodd hJA hcentral]
  exact hJodd.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)

end CFSG.ProperTwoGeneratedCore
