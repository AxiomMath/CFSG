module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem card_outer_le_of_card_mulAut_le {L : Type} [Group L] [Finite L] (hZ : center L = ⊥) {c : ℕ}
    (h : Nat.card (MulAut L) ≤ c * Nat.card L) : Nat.card (Outer L) ≤ c := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := conj_injective_of_center_eq_bot hZ
  have hinner : Nat.card ↥(inner L) = Nat.card L := by
    have : Nat.card ↥(inner L) = Nat.card ↥(MulAut.conj : L →* MulAut L).range := rfl
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner L)
  rw [hinner] at hmul
  change Nat.card (MulAut L) = Nat.card (MulAut L ⧸ inner L) * Nat.card L at hmul
  have hpos : 0 < Nat.card L := Nat.card_pos
  have : Nat.card (MulAut L ⧸ inner L) * Nat.card L ≤ c * Nat.card L := hmul ▸ h
  exact Nat.le_of_mul_le_mul_right this hpos

theorem hOut_of_card_outer_le_two {L : Type} [Group L] [Finite L] (h : Nat.card (Outer L) ≤ 2) :
    ∀ E : Subgroup (Outer L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
  intro E _
  have hfin : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  have : Finite (Outer L) := inferInstanceAs (Finite (MulAut L ⧸ inner L))
  have := Nat.card_le_card_of_injective E.subtype E.subtype_injective
  simpa using this.trans h

end CFSG.GH74.GLS.IVK.GHInv
