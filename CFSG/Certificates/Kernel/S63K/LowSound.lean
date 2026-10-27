module

public import Certificates.Data.Kernel.S63K.Low
public import Certificates.Data.D4HexBase
import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

namespace CFSG.KC.S63K

theorem lowK_spec : ∀ {cs : List Char} {k D : Nat}, lowK cs k D = true →
    ∀ j (hj : j < cs.length), (cs[j]'hj).toNat < 128 ∧ lowV (cs[j]'hj).toNat < 16 ∧
      lowV (cs[j]'hj).toNat = dg D (k + j)
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: cs, k, D, h, j, hj => by
    simp only [lowK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases j with
    | zero => exact ⟨h1, h2, by simpa only [List.getElem_cons_zero, Nat.add_zero, dg] using h3⟩
    | succ j =>
      have := lowK_spec h4 j (by simpa using hj)
      rw [show k + (j + 1) = k + 1 + j by omega]
      simpa using this

theorem hexVal_low {c : Nat} (hc : c < 128) (hv : lowV c < 16) :
    CFSG.D4Hex.hexVal (UInt8.ofNat c) = lowV c := by
  have e : (UInt8.ofNat c).toNat = c := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  unfold CFSG.D4Hex.hexVal
  rw [e]
  unfold lowV at hv ⊢
  by_cases a : c < 48
  · simp [Nat.blt_eq.mpr a] at hv
  · simp only [Bool.cond_eq_ite, Nat.blt_eq, a, if_false] at hv ⊢
    by_cases b : c < 58
    · simp [b]
    · simp only [b, if_false] at hv ⊢
      by_cases d : c < 97
      · simp [d] at hv
      · simp only [d, if_false] at hv ⊢
        by_cases f : c < 103
        · simp [f]
        · simp [f] at hv

theorem byte_low {cs : List Char} {D : Nat} (h : lowK cs 0 D = true) {j : Nat} (hj : j < cs.length) :
    CFSG.D4Hex.hexVal ((String.ofList cs).toUTF8.get! j) = dg D j := by
  have hs := lowK_spec h
  have ha : ∀ c ∈ cs.take cs.length, c.toNat < 128 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take hc)
    exact (hs i hi).1
  rw [CFSG.KS.Text.get!_toUTF8 ha hj hj, hexVal_low (hs j hj).1 (hs j hj).2.1, (hs j hj).2.2,
    Nat.zero_add]

theorem hexAtW_low {cs : List Char} {D : Nat} (h : lowK cs 0 D = true) {o : Nat}
    (ho : o + 2 < cs.length) : CFSG.D4Hex.hexAtW (String.ofList cs).toUTF8 o 3 = dec3 D o := by
  simp only [CFSG.D4Hex.hexAtW, Nat.add_zero]
  rw [byte_low h (by omega), byte_low h (by omega), byte_low h (by omega)]
  rfl

end CFSG.KC.S63K

end
