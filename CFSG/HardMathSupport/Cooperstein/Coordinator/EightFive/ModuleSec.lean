module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem index_fixV_autSec_mul_relIndex_le {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    (fixV (autSec A W U)).index * (fixV A).relIndex U ≤ (fixV A).relIndex W := by
  have h1 := card_inf_fixV_le_autSec (A := A) hUW hAW
  rw [inf_comm W, inf_comm U] at h1
  have h2 := card_sec_mul hUW
  have h3 := (fixV (autSec A W U)).index_mul_card
  have h4 := (fixV A).relIndex_mul_card U
  have h5 := (fixV A).relIndex_mul_card W
  have hpos : 0 < Nat.card (fixV (autSec A W U)) * Nat.card ↥(fixV A ⊓ U) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (fixV (autSec A W U)).index * (fixV A).relIndex U *
        (Nat.card (fixV (autSec A W U)) * Nat.card ↥(fixV A ⊓ U))
      = ((fixV (autSec A W U)).index * Nat.card (fixV (autSec A W U))) *
          ((fixV A).relIndex U * Nat.card ↥(fixV A ⊓ U)) := by ring
    _ = (fixV A).relIndex W * Nat.card ↥(fixV A ⊓ W) := by rw [h3, h4, h2, h5]
    _ ≤ (fixV A).relIndex W * (Nat.card (fixV (autSec A W U)) * Nat.card ↥(fixV A ⊓ U)) :=
        Nat.mul_le_mul_left _ h1

theorem relIndex_pos_of_finite (H K : Subgroup V) : 0 < H.relIndex K := by
  have h1 := H.relIndex_mul_card K
  have h2 : 0 < Nat.card K := Nat.card_pos
  rcases Nat.eq_zero_or_pos (H.relIndex K) with h | h
  · rw [h, zero_mul] at h1
    omega
  · exact h

theorem relIndex_fixV_le_index (A : Subgroup (MulAut V)) (W : Subgroup V) :
    (fixV A).relIndex W ≤ (fixV A).index := by
  rw [← Subgroup.relIndex_top_right]
  exact Subgroup.relIndex_le_of_le_right le_top
    (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)

theorem relIndex_fixV_mono (A : Subgroup (MulAut V)) {W W' : Subgroup V} (h : W ≤ W') :
    (fixV A).relIndex W ≤ (fixV A).relIndex W' :=
  Subgroup.relIndex_le_of_le_right h (relIndex_pos_of_finite (fixV A) W').ne'

theorem index_fixV_le_card {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    (fixV A).index ≤ Nat.card A := by
  have hv : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  rw [← (fixV A).index_mul_card] at hv
  exact Nat.le_of_mul_le_mul_right hv Nat.card_pos

theorem index_fixV_autSec_le {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {W U : Subgroup V} (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    (fixV (autSec A W U)).index ≤ Nat.card A := by
  have h1 := index_fixV_autSec_mul_relIndex_le hUW hAW
  have h2 : 0 < (fixV A).relIndex U := relIndex_pos_of_finite _ _
  calc (fixV (autSec A W U)).index ≤ (fixV (autSec A W U)).index * (fixV A).relIndex U :=
        Nat.le_mul_of_pos_right _ h2
    _ ≤ (fixV A).relIndex W := h1
    _ ≤ (fixV A).index := relIndex_fixV_le_index A W
    _ ≤ Nat.card A := index_fixV_le_card hA

theorem index_mul_index_le {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {Y₀ Y₁ Y₂ Y₃ : Subgroup V} (h01 : Y₀ ≤ Y₁) (h12 : Y₁ ≤ Y₂) (h23 : Y₂ ≤ Y₃)
    (hA1 : A ≤ stabSub Y₁) (hA3 : A ≤ stabSub Y₃) :
    (fixV (autSec A Y₁ Y₀)).index * (fixV (autSec A Y₃ Y₂)).index ≤ Nat.card A := by
  have e1 := index_fixV_autSec_mul_relIndex_le h01 hA1
  have e3 := index_fixV_autSec_mul_relIndex_le h23 hA3
  have e2 := relIndex_fixV_mono A h12
  have h0 : 0 < (fixV A).relIndex Y₀ := relIndex_pos_of_finite _ _
  calc (fixV (autSec A Y₁ Y₀)).index * (fixV (autSec A Y₃ Y₂)).index
      ≤ (fixV (autSec A Y₃ Y₂)).index * ((fixV (autSec A Y₁ Y₀)).index *
          (fixV A).relIndex Y₀) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h0)
    _ ≤ (fixV (autSec A Y₃ Y₂)).index * (fixV A).relIndex Y₂ :=
        Nat.mul_le_mul_left _ (e1.trans e2)
    _ ≤ (fixV A).relIndex Y₃ := e3
    _ ≤ (fixV A).index := relIndex_fixV_le_index A Y₃
    _ ≤ Nat.card A := index_fixV_le_card hA

theorem false_of_index_le_of_one_lt {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {Y₀ Y₁ Y₂ Y₃ : Subgroup V} (h01 : Y₀ ≤ Y₁) (h12 : Y₁ ≤ Y₂) (h23 : Y₂ ≤ Y₃)
    (hA1 : A ≤ stabSub Y₁) (hA3 : A ≤ stabSub Y₃)
    (h₁ : Nat.card A ≤ (fixV (autSec A Y₁ Y₀)).index)
    (h₃ : 1 < (fixV (autSec A Y₃ Y₂)).index) : False := by
  have h := index_mul_index_le hA h01 h12 h23 hA1 hA3
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nat.card A * 2 ≤ (fixV (autSec A Y₁ Y₀)).index * (fixV (autSec A Y₃ Y₂)).index :=
    Nat.mul_le_mul h₁ h₃
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
