
module

public import Certificates.Data.Kernel.L34W.ModK
public import Certificates.Data.GrSLitL34Sec5SWFusCheck
public import CFSG.Certificates.Kernel.L34W.ModelSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealBBase
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem bitC_eq (m l : ℕ) : bitC m l = m.testBit l := by
  unfold bitC
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq (m >>> l % 2) 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (m / 2 ^ l % 2) 1
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem bNot_eq (b : Bool) : bNot b = !b := by cases b <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem val_sub_cast {a c : ℕ} (ha : a < 4) (hc : c < 4) :
    ((a : ZMod 4) - (c : ZMod 4)).val = (a + 4 - c) % 4 := by
  interval_cases a <;> interval_cases c <;> decide

theorem getD_mask (m : ℕ) {n : ℕ} (hn : n < 16) : (kbOfMask m).getD n false = m.testBit n := by
  simp only [kbOfMask, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn,
    Option.map_some, Option.getD_some]

theorem eqC_eq (m x y : ℕ) : eqC m x y = eqKB (kbOfMask m) (dec x) (dec y) := by
  have h1 : ((dec x).2.1 - (dec y).2.1).val = (x / 4 % 4 + 4 - y / 4 % 4) % 4 :=
    val_sub_cast (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  have h2 : ((dec x).2.2 - (dec y).2.2).val = (x % 4 + 4 - y % 4) % 4 :=
    val_sub_cast (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  unfold eqKB inKB kIdx
  rw [h1, h2, getD_mask m (by omega)]
  unfold eqC
  rw [bitC_eq]
  rfl

theorem dec_zero : dec 0 = oneM := by
  simp [dec, oneM]

variable {T : ℕ → ℕ}

theorem isInvC_eq (hT : T1Of T) (m : ℕ) {x : ℕ} (hx : x < 1024) :
    isInvC T m x = isInvKB (kbOfMask m) (dec x) := by
  unfold isInvC isInvKB
  rw [bAnd_eq, eqC_eq, eqC_eq, dec_mulC hT hx hx, dec_zero, bNot_eq]

theorem commC_eq (hT : T1Of T) (m : ℕ) {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    commC T m x y = commKB (kbOfMask m) (dec x) (dec y) := by
  unfold commC commKB
  rw [eqC_eq, dec_mulC hT hx hy, dec_mulC hT hy hx]

theorem dec_mem_allM {x : ℕ} (hx : x < 1024) : dec x ∈ allM := mem_allM (dec_lt hx)

theorem twoC_spec (hT : T1Of T) {m a b c d : ℕ} (h : twoC T m a b c d = true) :
    ∃ x₁ ∈ allM, ∃ x₂ ∈ allM, ∃ x₃ ∈ allM, ∃ x₄ ∈ allM,
      isInvKB (kbOfMask m) x₁ = true ∧ isInvKB (kbOfMask m) x₂ = true ∧
      isInvKB (kbOfMask m) x₃ = true ∧ isInvKB (kbOfMask m) x₄ = true ∧
      eqKB (kbOfMask m) x₂ x₁ = false ∧ commKB (kbOfMask m) x₁ x₂ = true ∧
      commKB (kbOfMask m) x₃ x₁ = true ∧ commKB (kbOfMask m) x₃ x₂ = true ∧
      commKB (kbOfMask m) x₄ x₁ = true ∧ commKB (kbOfMask m) x₄ x₂ = true ∧
      commKB (kbOfMask m) x₃ x₄ = false := by
  unfold twoC at h
  simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, ⟨⟨ia, ib⟩, ic, id⟩, ⟨eba, cab⟩, ⟨cca, ccb⟩, ⟨cda, cdb⟩, ccd⟩ := h
  have ha' := Nat.blt_eq.mp ha
  have hb' := Nat.blt_eq.mp hb
  have hc' := Nat.blt_eq.mp hc
  have hd' := Nat.blt_eq.mp hd
  refine ⟨dec a, dec_mem_allM ha', dec b, dec_mem_allM hb', dec c, dec_mem_allM hc', dec d,
    dec_mem_allM hd', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [← isInvC_eq hT m ha']
  · rwa [← isInvC_eq hT m hb']
  · rwa [← isInvC_eq hT m hc']
  · rwa [← isInvC_eq hT m hd']
  · rwa [← eqC_eq]
  · rwa [← commC_eq hT m ha' hb']
  · rwa [← commC_eq hT m hc' ha']
  · rwa [← commC_eq hT m hc' hb']
  · rwa [← commC_eq hT m hd' ha']
  · rwa [← commC_eq hT m hd' hb']
  · rwa [← commC_eq hT m hc' hd']

end CFSG.KC.L34W

end
