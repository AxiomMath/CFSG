module

public import CFSG.GF2Type.SmithTypeE.DMod.CliffordTv
public import Certificates.Data.Kernel.SmithD6.WtCheck
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.KD.SmithD6

theorem evL_getD : ∀ c : Fin 32, evL.getD c.val 0 = evens[c.val]! := by decide

theorem evL_length : evL.length = 32 := rfl

theorem testBit_exC (s : ℕ) (T : ℕ) :
    (exC s).testBit T = decide (∃ c : Fin 32, (evF c).val = T ∧ s.testBit c.val = true) := by
  rw [exC, testBit_exGo, evL_length]
  by_cases h : ∃ c : Fin 32, (evF c).val = T ∧ s.testBit c.val = true
  · rw [decide_eq_true h, List.any_eq_true]
    obtain ⟨c, hc, hs⟩ := h
    refine ⟨c.val, List.mem_range.2 c.isLt, ?_⟩
    rw [evL_getD c, Nat.zero_add, hs, Bool.and_true, beq_iff_eq]
    exact hc
  · rw [decide_eq_false h, Bool.eq_false_iff]
    intro hany
    obtain ⟨j, hj, hj'⟩ := List.any_eq_true.1 hany
    have hj32 : j < 32 := List.mem_range.1 hj
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.zero_add] at hj'
    refine h ⟨⟨j, hj32⟩, ?_, hj'.2⟩
    rw [← hj'.1, evL_getD ⟨j, hj32⟩]
    rfl

theorem exL_apply_of_ne (v : V) {T : Fin 64} (hT : ∀ c, evF c ≠ T) : exL v T = 0 := by
  rw [exL_apply, Finset.sum_apply, Finset.sum_eq_zero]
  intro c _
  simp [Pi.single_apply, Ne.symm (hT c)]

theorem decode64_exC (s : ℕ) : decode64 (exC s) = exL (decode32 s) := by
  funext T
  rw [decode64_apply, testBit_exC]
  by_cases hT : ∃ c, evF c = T
  · obtain ⟨c, rfl⟩ := hT
    rw [exL_apply_evF, decode32_apply_bit]
    congr 1
    by_cases hs : s.testBit c.val = true
    · rw [hs]
      exact decide_eq_true ⟨c, rfl, hs⟩
    · rw [Bool.eq_false_iff.2 hs]
      exact decide_eq_false fun ⟨d, hd, hs'⟩ => hs (by rwa [evF_injective (Fin.ext hd)] at hs')
  · have hT' : ∀ c, evF c ≠ T := fun c hc => hT ⟨c, hc⟩
    rw [exL_apply_of_ne _ hT']
    have : ¬ ∃ c : Fin 32, (evF c).val = T.val ∧ s.testBit c.val = true :=
      fun ⟨c, hc, _⟩ => hT' c (Fin.ext hc)
    rw [decide_eq_false this]
    rfl

end CFSG.GF2Type.SmithTypeE.DMod

end
