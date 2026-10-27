module

public import Certificates.Data.Kernel.Tower.Cnt
public import CFSG.Certificates.Kernel.Tower.Cls14Sound

public section

namespace Certificates.KernelTower

theorem hmL_mem {HL c : Nat} : ∀ m, bitS (hmL HL m) c = true → ∃ j < m, l16 HL j = c := by
  intro m
  induction m with
  | zero =>
    intro h
    have h0 : bitS 0 c = true := h
    rw [bitS_zero'] at h0
    exact absurd h0 Bool.false_ne_true
  | succ m ih =>
    intro h
    have e : hmL HL (m + 1) = Nat.lor (hmL HL m) (Nat.shiftLeft 1 (l16 HL m)) := rfl
    rw [e, bitS_lor] at h
    rcases h with h | h
    · obtain ⟨j, hj, hjc⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hjc⟩
    · exact ⟨m, Nat.lt_succ_self m, bitS_one_shl h⟩

theorem cntB_of_mask {n m HL : Nat} {f : Nat → Bool} (hlt : ∀ j < m, l16 HL j < n)
    (hf : ∀ j < m, f (l16 HL j) = true)
    (hinc : ∀ j, j + 1 < m → l16 HL j < l16 HL (j + 1))
    (hmask : ∀ c < n, f c = true → bitS (hmL HL m) c = true) : cntB n f = m := by
  classical
  have hmono : ∀ i j, i < j → j < m → l16 HL i < l16 HL j := by
    intro i j hij hj
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero i)
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hinc j hj)
      · rw [h]
        exact hinc j hj
  have hS : ((Finset.range n).filter fun q => f q = true) = (Finset.range m).image (l16 HL) := by
    ext c
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hc, hfc⟩
      obtain ⟨j, hj, hjc⟩ := hmL_mem m (hmask c hc hfc)
      exact ⟨j, Finset.mem_range.2 hj, hjc⟩
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      exact ⟨hlt j hj, hf j hj⟩
  rw [cntB_eq_card, hS, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd hij (Nat.ne_of_lt (hmono i j h hj))
  · exact h
  · exact absurd hij (Nat.ne_of_gt (hmono j i h hi))

theorem czHB_czOK {n LB CZ nl : Nat} (hn : n < 32768) (h : czHB (histB n LB) CZ nl = true) :
    czOK n LB CZ 0 nl = true := by
  rw [czOK, allFrom, allB_true_iff]
  intro l hl
  have e := Nat.eq_of_beq_eq_true (allB_true_iff.1 h l hl)
  rw [cls16_lane, cls16_hist LB n hn] at e
  have e0 : Nat.add 0 l = l := Nat.zero_add l
  rw [e0, ← e]
  exact Nat.beq_refl _

end Certificates.KernelTower
