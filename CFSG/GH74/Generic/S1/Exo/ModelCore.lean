module

public import CFSG.GH74.Generic.S1.Exo.ModelOpsLin
public import CFSG.GH74.Generic.S1.Exo.LayerFix

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

structure ModelCore (S : Subgroup (GL (Fin 4) F)) where
  z0 : ↥S
  z0_sq : z0 * z0 = 1
  z0_ne : z0 ≠ 1
  neg : ↥S
  neg_center : ∀ g : ↥S, g ∈ Subgroup.center ↥S ↔ g = 1 ∨ g = neg
  neg_sq : neg * neg = 1
  neg_ne : neg ≠ 1
  norm : ∀ s : ↥S, s * s = 1 → s ≠ 1 → s ≠ neg → ∃ P : ↥S, P * s * P⁻¹ = z0
  swap : ∃ h : ↥S, h * z0 * h⁻¹ = neg * z0

namespace ModelCore

variable {S : Subgroup (GL (Fin 4) F)} (mc : ModelCore S)

theorem neg_mem_center : mc.neg ∈ Subgroup.center ↥S := (mc.neg_center mc.neg).2 (Or.inr rfl)

end ModelCore

@[expose] def ModelOps.core {S : Subgroup (GL (Fin 4) F)} (mo : ModelOps S) : ModelCore S where
  z0 := mo.z0
  z0_sq := mo.z0_sq
  z0_ne := mo.z0_ne
  neg := mo.neg
  neg_center := mo.neg_center
  neg_sq := mo.neg_sq
  neg_ne := mo.neg_ne
  norm := mo.norm
  swap := mo.swap

@[expose] noncomputable def linModelCore [Finite F] (hF : Nat.card F % 4 = 3) :
    ModelCore (StatedSL 4 F) where
  z0 := linZ0 F
  z0_sq := linZ0_mul_self
  z0_ne := linZ0_ne_one (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega)))
  neg := linNeg F
  neg_center := linNeg_center hF
  neg_sq := linNeg_mul_self
  neg_ne := linNeg_ne_one (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega)))
  norm := fun s hs2 hs1 hsn => exists_conj_linZ0 hF s hs2 hs1 hsn
  swap := ⟨linSwap F, linSwap_conj⟩

variable {G : Type} [Group G] [Finite G] {S : Subgroup (GL (Fin 4) F)}

theorem iso_xbar_eq_neg_core (mc : ModelCore S) {y : G} (D : LayerData y S) (hy : orderOf y = 2)
    (hxK : xbar y ∈ D.K) : D.iso ⟨xbar y, hxK⟩ = mc.neg := by
  have hz : (⟨xbar y, hxK⟩ : ↥D.K) ∈ Subgroup.center ↥D.K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm y (g : CentralizerBar y))
  have h1 := (mem_center_iff_of_mulEquiv D.iso _).2 hz
  rcases (mc.neg_center _).1 h1 with h | h
  · exfalso
    have : (⟨xbar y, hxK⟩ : ↥D.K) = 1 := D.iso.injective (by rw [h, map_one])
    exact xbar_ne_one hy (congrArg Subtype.val this)
  · exact h

theorem ι_neg_eq_core (mc : ModelCore S) {y : G} (D : LayerData y S) (hy : orderOf y = 2)
    (hxK : xbar y ∈ D.K) : D.ι mc.neg = y := by
  apply D.ι_eq_of_xbar hy
  rw [← iso_xbar_eq_neg_core mc D hy hxK]
  simp

end CFSG.GH74.Generic.S1.Exo
