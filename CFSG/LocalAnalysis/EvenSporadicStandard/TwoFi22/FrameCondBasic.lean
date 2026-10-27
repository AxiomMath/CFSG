module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameDefs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.Wong77.Module

theorem word_add_self (w : Word) : w + w = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (w i)

theorem word_eq_of_add_eq_zero {v w : Word} (h : v + w = 0) : v = w :=
  calc v = v + (w + w) := by rw [word_add_self, add_zero]
    _ = v + w + w := (add_assoc _ _ _).symm
    _ = w := by rw [h, zero_add]

theorem hammingNorm_add_le (v w : Word) :
    hammingNorm (v + w) ≤ hammingNorm v + hammingNorm w := by
  have h := hammingDist_triangle (v + w) w 0
  have h1 : hammingDist (v + w) w = hammingNorm v := by simp [hammingDist, hammingNorm]
  rwa [h1, hammingDist_zero_right, hammingDist_zero_right] at h

theorem hammingNorm_single (i : Fin 23) : hammingNorm (Pi.single i (1 : ZMod 2) : Word) = 1 := by
  rw [hammingNorm, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp [Pi.single_apply]

theorem hammingNorm_add_single_le (w : Word) (i : Fin 23) :
    hammingNorm (w + Pi.single i 1) ≤ hammingNorm w + 1 := by
  have := hammingNorm_add_le w (Pi.single i 1)
  rwa [hammingNorm_single] at this

namespace GoodFrame

variable {X : Type*} [Group X] (F : GoodFrame X)

@[expose] def wprod (w : Word) : X := F.φ (Multiplicative.ofAdd w)

theorem wprod_add (v w : Word) : F.wprod (v + w) = F.wprod v * F.wprod w := by
  simp [wprod, ofAdd_add]

theorem wprod_zero : F.wprod 0 = 1 := by
  simp [wprod]

theorem wprod_single (i : Fin 23) : F.wprod (Pi.single i 1) = F.pt i := rfl

theorem wprod_mul_self (w : Word) : F.wprod w * F.wprod w = 1 := by
  rw [← wprod_add, word_add_self, wprod_zero]

theorem wprod_comm (v w : Word) : F.wprod v * F.wprod w = F.wprod w * F.wprod v := by
  rw [← wprod_add, ← wprod_add, add_comm]

theorem pt_mul_self (i : Fin 23) : F.pt i * F.pt i = 1 :=
  F.wprod_mul_self _

theorem pt_comm (i j : Fin 23) : F.pt i * F.pt j = F.pt j * F.pt i :=
  F.wprod_comm _ _

theorem wprod_allOnes : F.wprod allOnes = 1 := F.prod_ones

theorem eq_of_wprod_eq {v w : Word} (h : F.wprod v = F.wprod w)
    (hw : hammingNorm v + hammingNorm w < 7) : v = w := by
  have h1 : F.wprod (v + w) = 1 := by rw [wprod_add, h, wprod_mul_self]
  rcases F.ker_weight (v + w) h1 with h0 | h7
  · exact word_eq_of_add_eq_zero h0
  · have := hammingNorm_add_le v w
    omega

theorem pt_injective : Function.Injective F.pt := by
  intro i j h
  have hw := F.eq_of_wprod_eq (v := Pi.single i 1) (w := Pi.single j 1) h
    (by rw [hammingNorm_single, hammingNorm_single]; norm_num)
  by_contra hij
  have := congrFun hw i
  simp [hij] at this

theorem ncard_range_pt : (Set.range F.pt).ncard = 23 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ F.pt_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end GoodFrame

end CFSG.EvenSporadicStandard.TwoFi22
