module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {D : Type} [Group D]

@[expose] def sec12W_base (B : Subgroup D) : Subgroup (WrZ2 D) where
  carrier := {w | w.right = 1 ∧ ∀ x, w.left x ∈ B}
  one_mem' := ⟨rfl, fun _ => B.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha⟩ ⟨hb1, hb⟩
    refine ⟨by rw [RegularWreathProduct.mul_right, ha1, hb1, mul_one], fun x => ?_⟩
    rw [RegularWreathProduct.mul_left]
    exact B.mul_mem (ha x) (hb _)
  inv_mem' := by
    rintro a ⟨ha1, ha⟩
    refine ⟨by rw [RegularWreathProduct.inv_right, ha1]; exact inv_one, fun x => ?_⟩
    rw [RegularWreathProduct.inv_left]
    exact B.inv_mem (ha _)

theorem mem_sec12W_base {B : Subgroup D} {w : WrZ2 D} :
    w ∈ sec12W_base B ↔ w.right = 1 ∧ ∀ x, w.left x ∈ B := Iff.rfl

theorem sec12W_two_pts : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  decide

theorem sec12W_ext {w w' : WrZ2 D} (hr : w.right = 1) (hr' : w'.right = 1)
    (h1 : w.left 1 = w'.left 1) (h2 : w.left (Multiplicative.ofAdd 1) =
      w'.left (Multiplicative.ofAdd 1)) : w = w' := by
  refine RegularWreathProduct.ext (funext fun a => ?_) (hr.trans hr'.symm)
  rcases sec12W_two_pts a with rfl | rfl
  · exact h1
  · exact h2

@[expose] def sec12W_proj (i : Multiplicative (ZMod 2)) :
    ↥(RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)).ker →* D where
  toFun w := (w : WrZ2 D).left i
  map_one' := rfl
  map_mul' a b := by
    have ha : (a : WrZ2 D).right = 1 := MonoidHom.mem_ker.mp a.2
    change ((a : WrZ2 D) * (b : WrZ2 D)).left i = _
    have hinv : ((a : WrZ2 D).right)⁻¹ * i = i := by
      rw [ha]
      exact (congrArg (· * i) inv_one).trans (one_mul i)
    rw [RegularWreathProduct.mul_left]
    exact congrArg ((a : WrZ2 D).left i * ·) (congrArg (b : WrZ2 D).left hinv)

theorem sec12W_proj_apply (i : Multiplicative (ZMod 2))
    (w : ↥(RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)).ker) :
    sec12W_proj i w = (w : WrZ2 D).left i := rfl

theorem sec12W_card_base_le [Finite D] (B : Subgroup D) :
    Nat.card (sec12W_base B) ≤ Nat.card B * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun w =>
    (⟨(w : WrZ2 D).left 1, w.2.2 1⟩, ⟨(w : WrZ2 D).left (Multiplicative.ofAdd 1),
      w.2.2 _⟩)) ?_
  intro a b hab
  have h1 := congrArg (fun z : ↥B × ↥B => (z.1 : D)) hab
  have h2 := congrArg (fun z : ↥B × ↥B => (z.2 : D)) hab
  exact Subtype.ext (sec12W_ext a.2.1 b.2.1 h1 h2)

end CFSG.OddStandard.SmallF3.Omega
