module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.Open
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem card_powTorsionIn_of_mulEquiv {A : Subgroup G} [IsMulCommutative ↥A] {m r : ℕ}
    (e : ↥A ≃* Multiplicative (ZMod m × ZMod m)) (hr : r.Prime) (hdvd : r ∣ m) :
    Nat.card ↥((powMonoidHom r : ↥A →* ↥A).ker) = r ^ 2 := by
  classical
  have hcardA : Nat.card ↥A = m * m := by
    calc Nat.card ↥A = Nat.card (Multiplicative (ZMod m × ZMod m)) := Nat.card_congr e.toEquiv
      _ = Nat.card (ZMod m × ZMod m) := Nat.card_congr Multiplicative.toAdd
      _ = m * m := by simp [Nat.card_prod, Nat.card_zmod]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcardA
    exact (Nat.card_pos (α := ↥A)).ne' hcardA
  haveI : NeZero m := ⟨hm0⟩
  let e' : ↥A ≃* (Multiplicative (ZMod m) × Multiplicative (ZMod m)) :=
    e.trans (MulEquiv.prodMultiplicative (G := ZMod m) (H := ZMod m))
  rw [Nat.card_congr
    (CFSG.LargeEvenClassification.Helpers.powerKernelEquivOfMulEquiv e' r).toEquiv]
  have h := CFSG.LargeEvenClassification.Helpers.cyclic_pair_power_kernel_card m m r
  rw [Nat.gcd_eq_right hdvd] at h
  simpa [pow_two] using h

end CFSG.GroupTheory
