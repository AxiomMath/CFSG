module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParGamma

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar

@[expose] def decMask (A : Array ℕ) : ℕ :=
  (if (A.getD 0 0).testBit 4 then 1 else 0) + (if (A.getD 2 0).testBit 6 then 2 else 0) +
    (if (A.getD 0 0).testBit 6 then 4 else 0) + (if (A.getD 0 0).testBit 7 then 8 else 0)

theorem decMask_eProdBits : ∀ mask < 16, decMask (eProdBits mask) = mask := by decide

theorem testBit_eq_of_toMat_eq {A B : Array ℕ} (h : toMat 8 8 A = toMat 8 8 B) {i j : ℕ}
    (hi : i < 8) (hj : j < 8) : (A.getD i 0).testBit j = (B.getD i 0).testBit j := by
  have h1 := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply] at h1
  cases h2 : (A.getD i 0).testBit j <;> cases h3 : (B.getD i 0).testBit j <;>
    simp_all [bz]

theorem decMask_congr {A B : Array ℕ} (h : toMat 8 8 A = toMat 8 8 B) :
    decMask A = decMask B := by
  simp only [decMask, testBit_eq_of_toMat_eq h (i := 0) (j := 4) (by norm_num) (by norm_num),
    testBit_eq_of_toMat_eq h (i := 2) (j := 6) (by norm_num) (by norm_num),
    testBit_eq_of_toMat_eq h (i := 0) (j := 6) (by norm_num) (by norm_num),
    testBit_eq_of_toMat_eq h (i := 0) (j := 7) (by norm_num) (by norm_num)]

section E16


theorem card_E16_ge : 16 ≤ Nat.card E16 := by
  have hinj : Function.Injective (fun m : Fin 16 => (⟨eProdSU m, eProdSU_mem_E16 m⟩ : E16)) := by
    intro a b hab
    have h1 : ((eProdSU a : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        ((eProdSU b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      have := congrArg (fun x : E16 =>
        (((x : SU42b) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) hab
      exact this
    rw [coe_eProdSU, coe_eProdSU] at h1
    have h2 := decMask_congr h1
    rw [decMask_eProdBits a a.2, decMask_eProdBits b b.2] at h2
    exact Fin.ext h2
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

end E16

theorem row_eBits_zero_zero (u : Fin 8 → ZMod 2) : (toMat 8 8 (eBits 0) *ᵥ u) 0 = u 0 + u 4 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_eight, toMat_apply]
  simp +decide [bz]

theorem row_eBits_zero_one (u : Fin 8 → ZMod 2) : (toMat 8 8 (eBits 0) *ᵥ u) 1 = u 1 + u 5 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_eight, toMat_apply]
  simp +decide [bz]

theorem row_eBits_one_two (u : Fin 8 → ZMod 2) : (toMat 8 8 (eBits 1) *ᵥ u) 2 = u 2 + u 6 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_eight, toMat_apply]
  simp +decide [bz]

theorem row_eBits_one_three (u : Fin 8 → ZMod 2) : (toMat 8 8 (eBits 1) *ᵥ u) 3 = u 3 + u 7 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_eight, toMat_apply]
  simp +decide [bz]

theorem fix_coords {u : Fin 8 → ZMod 2} (hu : ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u) :
    u 4 = 0 ∧ u 5 = 0 ∧ u 6 = 0 ∧ u 7 = 0 := by
  have h0 := hu 0 (by norm_num)
  have h1 := hu 1 (by norm_num)
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h1 2
  have e3 := congrFun h1 3
  rw [row_eBits_zero_zero] at e0
  rw [row_eBits_zero_one] at e1
  rw [row_eBits_one_two] at e2
  rw [row_eBits_one_three] at e3
  exact ⟨add_eq_left.mp e0, add_eq_left.mp e1, add_eq_left.mp e2, add_eq_left.mp e3⟩

@[expose] def extFour (v : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun i => if h : i.val < 4 then v ⟨i.val, h⟩ else 0

theorem eq_extFour {u : Fin 8 → ZMod 2} (hu : ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u) :
    u = extFour (fun k => u ⟨k.val, by omega⟩) := by
  obtain ⟨h4, h5, h6, h7⟩ := fix_coords hu
  funext i
  fin_cases i <;> simp [extFour, h4, h5, h6, h7]

theorem ncard_fix_le :
    {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}.ncard ≤ 16 := by
  calc {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}.ncard
      ≤ (Set.range extFour).ncard := Set.ncard_le_ncard (fun u hu => ⟨_, (eq_extFour hu).symm⟩)
    _ = Nat.card (Set.range extFour) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Fin 4 → ZMod 2) := Finite.card_range_le _
    _ = 16 := by simp

end CFSG.EvenSmallLie.UnitarySix.Child5
