module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMod
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFAbs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

section Basic

variable {n : ℕ} {L A : Subgroup (MulAut V)}

theorem U4OffenderData.simple (h : U4OffenderData n L A) : IsSimpleGroup ↥L :=
  (isU4_simple h.isU4).1

theorem U4OffenderData.nonabelian (h : U4OffenderData n L A) : ∃ a b : ↥L, a * b ≠ b * a :=
  (isU4_simple h.isU4).2

theorem U4OffenderData.perfect (h : U4OffenderData n L A) : _root_.commutator ↥L = ⊤ :=
  commutator_eq_top_of_simple h.simple h.nonabelian

theorem U4OffenderData.comm (h : U4OffenderData n L A) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
  h.elemAbelian.1

theorem U4OffenderData.sq (h : U4OffenderData n L A) : ∀ a ∈ A, a * a = 1 := fun a ha => by
  have := h.elemAbelian.2 a ha
  rwa [_root_.pow_two] at this

theorem U4OffenderData.exists_move (h : U4OffenderData n L A) : ∃ g ∈ L, ∃ v : V, g v ≠ v := by
  obtain ⟨a, b, hab⟩ := h.nonabelian
  by_contra hcon
  push Not at hcon
  apply hab
  have h1 : ∀ x : ↥L, (x : MulAut V) = 1 := fun x => by
    ext v; exact hcon x x.2 v
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, h1 a, h1 b]

theorem U4OffenderData.not_ltriv_commV (h : U4OffenderData n L A) :
    ¬ LTrivOn L ⊥ (commV L) := by
  intro htriv
  have hbot : commV L = ⊥ := by
    have h1 : commSub (commV L) L = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro u hu g hg
      have := htriv g hg u hu
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
    rw [← commSub_commV h.perfect, h1]
  obtain ⟨g, hg, v, hv⟩ := h.exists_move
  have : g v * v⁻¹ ∈ commV L := Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact hv this

end Basic

section Numerics

variable {n : ℕ} {L A : Subgroup (MulAut V)} [Finite V]

theorem card_le_relIndex_cenD_mul (h : U4OffenderData n L A) {Z : Subgroup V} (hZ : XInv L A Z)
    (hZD : Z ≤ fixV (cenD L A)) :
    Nat.card Z ≤ (cenD L A).relIndex A * Nat.card ↥(Z ⊓ fixV A) := by
  have h1 := h.offender Z hZ.2
  have hDle : cenD L A ≤ A ⊓ centSub Z := le_inf (cenD_le L A) (fun d hd z hz => hZD hz d hd)
  have h0 : (cenD L A).relIndex A ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.FiniteIndex.index_ne_zero
  have h2 : (A ⊓ centSub Z).relIndex A ≤ (cenD L A).relIndex A :=
    Subgroup.relIndex_le_of_le_left hDle h0
  exact h1.trans (Nat.mul_le_mul_right _ h2)

theorem relIndex_cenD_le_card_autSec (h : U4OffenderData n L A) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hZ : XInv L A Z) (hZ' : XInv L A Z') (hnc : ¬ LTrivOn L Z' Z) :
    (cenD L A).relIndex A ≤ Nat.card (autSec A Z Z') := by
  have hcard := card_autSec_mul hZ.2 hZ'.2
  have hle : A ⊓ centSec Z Z' ≤ cenD L A :=
    inf_centSec_le_cenD h.simple h.normalizes hZ'Z hZ.1 hZ'.1 hnc
  have h1 : Nat.card ↥(A ⊓ centSec Z Z') ≤ Nat.card ↥(cenD L A) := Subgroup.card_le_of_le hle
  have h2 : (cenD L A).relIndex A * Nat.card ↥(cenD L A) = Nat.card A := by
    have := Subgroup.relIndex_mul_card (cenD L A) A
    rwa [inf_eq_left.mpr (cenD_le L A)] at this
  have hpos : 0 < Nat.card ↥(cenD L A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (cenD L A).relIndex A * Nat.card ↥(cenD L A) = Nat.card A := h2
    _ = Nat.card (autSec A Z Z') * Nat.card ↥(A ⊓ centSec Z Z') := hcard.symm
    _ ≤ Nat.card (autSec A Z Z') * Nat.card ↥(cenD L A) := Nat.mul_le_mul_left _ h1

theorem card_sec_le (h : U4OffenderData n L A) {Z' Z : Subgroup V} (hZ'Z : Z' ≤ Z)
    (hZ : XInv L A Z) (hZ' : XInv L A Z') (hZD : Z ≤ fixV (cenD L A)) (hnc : ¬ LTrivOn L Z' Z) :
    Nat.card (Sec Z Z') ≤ Nat.card (autSec A Z Z') * Nat.card (fixV (autSec A Z Z')) := by
  have h1 := card_le_relIndex_cenD_mul h hZ hZD
  have h2 := card_inf_fixV_le_autSec (A := A) hZ'Z hZ.2
  have h3 := card_sec_mul hZ'Z
  have h4 : Nat.card ↥(Z' ⊓ fixV A) ≤ Nat.card Z' := Subgroup.card_le_of_le inf_le_left
  have h5 := relIndex_cenD_le_card_autSec h hZ'Z hZ hZ' hnc
  have hz' : 0 < Nat.card Z' := Nat.card_pos
  have : Nat.card (Sec Z Z') * Nat.card Z' ≤
      ((cenD L A).relIndex A * Nat.card (fixV (autSec A Z Z'))) * Nat.card Z' := by
    calc Nat.card (Sec Z Z') * Nat.card Z' = Nat.card Z := h3
      _ ≤ (cenD L A).relIndex A * Nat.card ↥(Z ⊓ fixV A) := h1
      _ ≤ (cenD L A).relIndex A * (Nat.card (fixV (autSec A Z Z')) * Nat.card ↥(Z' ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ (cenD L A).relIndex A * (Nat.card (fixV (autSec A Z Z')) * Nat.card Z') :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
      _ = ((cenD L A).relIndex A * Nat.card (fixV (autSec A Z Z'))) * Nat.card Z' := by ring
  have h6 := Nat.le_of_mul_le_mul_right this hz'
  exact h6.trans (Nat.mul_le_mul_right _ h5)

end Numerics

end CFSG.LocalAnalysis.RankThreeUC
