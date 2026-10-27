module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JWr

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {D : Type} [Group D]

@[expose] def sec12W_base2 (U0 U1 : Subgroup D) : Subgroup (WrZ2 D) where
  carrier := {w | w.right = 1 ∧ w.left 1 ∈ U0 ∧ w.left (Multiplicative.ofAdd 1) ∈ U1}
  one_mem' := ⟨rfl, U0.one_mem, U1.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha0, ha2⟩ ⟨hb1, hb0, hb2⟩
    have hinv : ∀ x : Multiplicative (ZMod 2), a.right⁻¹ * x = x := fun x => by
      rw [ha1]
      exact (congrArg (· * x) inv_one).trans (one_mul x)
    refine ⟨by rw [RegularWreathProduct.mul_right, ha1, hb1, mul_one], ?_, ?_⟩
    · rw [RegularWreathProduct.mul_left]
      exact U0.mul_mem ha0 (show b.left (a.right⁻¹ * 1) ∈ U0 by rw [hinv]; exact hb0)
    · rw [RegularWreathProduct.mul_left]
      exact U1.mul_mem ha2
        (show b.left (a.right⁻¹ * Multiplicative.ofAdd 1) ∈ U1 by rw [hinv]; exact hb2)
  inv_mem' := by
    rintro a ⟨ha1, ha0, ha2⟩
    have hmul : ∀ x : Multiplicative (ZMod 2), a.right * x = x := fun x => by
      rw [ha1]
      exact one_mul x
    refine ⟨by rw [RegularWreathProduct.inv_right, ha1]; exact inv_one, ?_, ?_⟩
    · rw [RegularWreathProduct.inv_left]
      exact U0.inv_mem (show a.left (a.right * 1) ∈ U0 by rw [hmul]; exact ha0)
    · rw [RegularWreathProduct.inv_left]
      exact U1.inv_mem
        (show a.left (a.right * Multiplicative.ofAdd 1) ∈ U1 by rw [hmul]; exact ha2)

theorem sec12W_base_eq_base2 (B : Subgroup D) : sec12W_base B = sec12W_base2 B B := by
  ext w
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, h 1, h _⟩
  · rintro ⟨hr, h0, h1⟩
    refine ⟨hr, fun x => ?_⟩
    rcases sec12W_two_pts x with rfl | rfl
    · exact h0
    · exact h1

theorem sec12W_base2_card [Finite D] (U0 U1 : Subgroup D) :
    Nat.card (sec12W_base2 U0 U1) = Nat.card U0 * Nat.card U1 := by
  let f : sec12W_base2 U0 U1 → U0 × U1 := fun w =>
    (⟨w.1.left 1, w.2.2.1⟩, ⟨w.1.left (Multiplicative.ofAdd 1), w.2.2.2⟩)
  have hbij : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun p => ?_⟩
    · refine Subtype.ext (sec12W_ext a.2.1 b.2.1 ?_ ?_)
      · exact congrArg (fun z : U0 × U1 => (z.1 : D)) hab
      · exact congrArg (fun z : U0 × U1 => (z.2 : D)) hab
    · refine ⟨⟨⟨fun i => if i = 1 then (p.1 : D) else (p.2 : D), 1⟩,
        ⟨rfl, ?_, ?_⟩⟩, ?_⟩
      · show (if (1 : Multiplicative (ZMod 2)) = 1 then (p.1 : D) else (p.2 : D)) ∈ U0
        rw [if_pos rfl]
        exact p.1.2
      · show (if (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 then (p.1 : D)
            else (p.2 : D)) ∈ U1
        rw [if_neg (by decide)]
        exact p.2.2
      · apply Prod.ext
        · exact Subtype.ext (by
            show (if (1 : Multiplicative (ZMod 2)) = 1 then (p.1 : D) else (p.2 : D)) =
              (p.1 : D)
            rw [if_pos rfl])
        · exact Subtype.ext (by
            show (if (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 then (p.1 : D)
              else (p.2 : D)) = (p.2 : D)
            rw [if_neg (by decide)])
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).trans (Nat.card_prod U0 U1)

end CFSG.OddStandard.SmallF3.Omega
