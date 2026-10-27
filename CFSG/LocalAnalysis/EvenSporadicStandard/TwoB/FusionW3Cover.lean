module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Local

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS

section Cover

variable {X : Type} [Group X] [Finite X]

abbrev preimageCent (w : X) : Subgroup X :=
  (centralizer ({(QuotientGroup.mk w : X ⧸ center X)} : Set (X ⧸ center X))).comap
    (QuotientGroup.mk' (center X))

theorem centralizer_le_preimageCent (w : X) : centralizer ({w} : Set X) ≤ preimageCent w := by
  intro x hx
  rw [mem_comap, mem_centralizer_singleton_iff]
  have := mem_centralizer_singleton_iff.1 hx
  simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]

theorem comm_mem_center_of_mem_preimageCent {w x : X} (hx : x ∈ preimageCent w) :
    x * w * x⁻¹ * w⁻¹ ∈ center X := by
  rw [mem_comap, mem_centralizer_singleton_iff] at hx
  simp only [QuotientGroup.mk'_apply] at hx
  rw [← QuotientGroup.eq_one_iff (N := center X)]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  calc (QuotientGroup.mk x : X ⧸ center X) * QuotientGroup.mk w * (QuotientGroup.mk x)⁻¹ *
      (QuotientGroup.mk w)⁻¹ = (QuotientGroup.mk w * QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ *
        (QuotientGroup.mk w)⁻¹ := by rw [hx]
    _ = 1 := by group

theorem relIndex_centralizer_preimageCent_le (w : X) :
    (centralizer ({w} : Set X)).relIndex (preimageCent w) ≤ Nat.card (center X) := by
  let C : Subgroup X := preimageCent w
  let f : ↥C →* ↥(center X) := MonoidHom.mk' (fun x => ⟨(x : X) * w * (x : X)⁻¹ * w⁻¹,
    comm_mem_center_of_mem_preimageCent x.2⟩) (by
      intro a b
      apply Subtype.ext
      have ha := comm_mem_center_of_mem_preimageCent a.2
      have hb := comm_mem_center_of_mem_preimageCent b.2
      have hb' := mem_center_iff.1 hb
      have ha' := mem_center_iff.1 ha
      show (a : X) * b * w * ((a : X) * b)⁻¹ * w⁻¹ =
        ((a : X) * w * (a : X)⁻¹ * w⁻¹) * ((b : X) * w * (b : X)⁻¹ * w⁻¹)
      calc (a : X) * b * w * ((a : X) * b)⁻¹ * w⁻¹
          = (a : X) * ((b : X) * w * (b : X)⁻¹ * w⁻¹) * w * (a : X)⁻¹ * w⁻¹ := by group
        _ = ((b : X) * w * (b : X)⁻¹ * w⁻¹) * (a : X) * w * (a : X)⁻¹ * w⁻¹ := by
          rw [hb' a]
        _ = ((b : X) * w * (b : X)⁻¹ * w⁻¹) * ((a : X) * w * (a : X)⁻¹ * w⁻¹) := by group
        _ = ((a : X) * w * (a : X)⁻¹ * w⁻¹) * ((b : X) * w * (b : X)⁻¹ * w⁻¹) :=
          ha' ((b : X) * w * (b : X)⁻¹ * w⁻¹))
  have hker : f.ker = (centralizer ({w} : Set X)).subgroupOf C := by
    ext x
    simp only [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (x : X) * w * (x : X)⁻¹ * w⁻¹ = 1 := congrArg Subtype.val h
      have h2 : (x : X) * w * (x : X)⁻¹ = w := by
        rw [mul_inv_eq_one] at h1
        exact h1
      calc (x : X) * w = (x : X) * w * (x : X)⁻¹ * x := by group
        _ = w * x := by rw [h2]
    · intro h
      apply Subtype.ext
      show (x : X) * w * (x : X)⁻¹ * w⁻¹ = 1
      rw [h]
      group
  rw [Subgroup.relIndex, ← hker, index_ker]
  exact Subgroup.card_le_card_group _


theorem natCard_preimageCent (w : X) :
    Nat.card (preimageCent w) = Nat.card (center X) *
      Nat.card (centralizer ({(QuotientGroup.mk w : X ⧸ center X)} : Set (X ⧸ center X))) :=
  QuotientGroup.card_preimage_mk (center X)
    (centralizer ({(QuotientGroup.mk w : X ⧸ center X)} : Set (X ⧸ center X)) : Set (X ⧸ center X))

theorem exists_babyInv_card_cases (hT3 : BabyTableIII) (hc : Nat.card (center X) = 2)
    (φ : X ⧸ center X ≃* Carrier .B) {w : X} (hw : orderOf w = 2) (hwc : w ∉ center X) :
    ∃ k : Fin 4, BabyInv k (φ (QuotientGroup.mk w)) ∧
      (Nat.card ↥(centralizer ({w} : Set X)) = babyCentOrder k ∨
        Nat.card ↥(centralizer ({w} : Set X)) = 2 * babyCentOrder k) := by
  set wb : X ⧸ center X := QuotientGroup.mk w with hwb
  have hwb1 : wb ≠ 1 := by
    rw [hwb, Ne, QuotientGroup.eq_one_iff]
    exact hwc
  have hwb2 : orderOf wb = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hwb1
    have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    rw [hwb, ← QuotientGroup.mk_pow, hw2, QuotientGroup.mk_one]
  have hb2 : orderOf (φ wb) = 2 := by rw [MulEquiv.orderOf_eq]; exact hwb2
  obtain ⟨k, hk⟩ := hT3.1 (φ wb) hb2
  refine ⟨k, hk, ?_⟩
  have h1 : Nat.card (centralizer ({wb} : Set (X ⧸ center X))) = babyCentOrder k := by
    rw [← hk.2]
    exact Nat.card_congr (centralizerEquiv φ wb).toEquiv
  have h2 := natCard_preimageCent w
  rw [h1, hc] at h2
  have h3 := Subgroup.relIndex_mul_card (H := centralizer ({w} : Set X)) (K := preimageCent w)
  rw [inf_of_le_left (centralizer_le_preimageCent w), h2] at h3
  have h4 := relIndex_centralizer_preimageCent_le w
  rw [hc] at h4
  have hpos : 0 < Nat.card (preimageCent w) := Nat.card_pos
  rw [h2] at hpos
  have h5 : 0 < (centralizer ({w} : Set X)).relIndex (preimageCent w) := by
    rcases Nat.eq_zero_or_pos ((centralizer ({w} : Set X)).relIndex (preimageCent w)) with h0 | h0
    · rw [h0, zero_mul] at h3
      omega
    · exact h0
  rcases (show (centralizer ({w} : Set X)).relIndex (preimageCent w) = 1 ∨
      (centralizer ({w} : Set X)).relIndex (preimageCent w) = 2 by omega) with h6 | h6
  · right
    rw [h6, one_mul] at h3
    exact h3
  · left
    rw [h6] at h3
    omega

theorem exists_card_centralizer_cases (hT3 : BabyTableIII) (h : IsTwoBCover X) {w : X}
    (hw : orderOf w = 2) (hwc : w ∉ center X) :
    ∃ k : Fin 4, Nat.card ↥(centralizer ({w} : Set X)) = babyCentOrder k ∨
      Nat.card ↥(centralizer ({w} : Set X)) = 2 * babyCentOrder k := by
  obtain ⟨-, hc, ⟨φ⟩⟩ := h
  obtain ⟨k, -, hk⟩ := exists_babyInv_card_cases hT3 hc φ hw hwc
  exact ⟨k, hk⟩

end Cover

end CFSG.EvenSporadicStandard.TwoB
