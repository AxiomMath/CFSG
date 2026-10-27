module

public import Certificates.Data.Kernel.SmithEKCW
public import CFSG.LargeExtraspecial.S14SMICheck
public import CFSG.Certificates.Kernel.SmithEK.TSound
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.SmithE

theorem cwBit_eq (B v : Nat) : Nat.beq (Nat.land (Nat.shiftRight B v) 1) 1 = B.testBit v := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight B v) 1 = B / 2 ^ v % 2 := by
    change (B >>> v) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ v) with h | h <;> rw [h] <;> rfl

theorem cwK_cons (B e : Nat) (E : List Nat) (c : List Nat) (Cs : List (List Nat)) :
    cwK B (e :: E) (c :: Cs) = (Nat.blt e 2048 &&
      Nat.beq (Nat.land (Nat.shiftRight B (Nat.xor (applyL c e) e)) 1) 1 && cwK B E Cs) := rfl

theorem cwK_sound (B : Nat) : ∀ (E : List Nat) (Cs : List (List Nat)), cwK B E Cs = true →
    E.length = Cs.length ∧ ∀ k < Cs.length,
      E.getD k 0 < 2048 ∧ B.testBit (applyL (Cs.getD k []) (E.getD k 0) ^^^ E.getD k 0) = true
  | [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | [], _ :: _, h => absurd h (by simp [cwK])
  | _ :: _, [], h => absurd h (by simp [cwK])
  | e :: E, c :: Cs, h => by
    rw [cwK_cons, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, cwBit_eq] at h
    obtain ⟨hl, hk⟩ := cwK_sound B E Cs h.2
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    cases k with
    | zero => exact ⟨h.1.1, h.1.2⟩
    | succ k => exact hk k (by simpa using hk')

theorem chkCommWt_of {Cs : List (List Nat)} {E W : List Nat} (hl : Cs.length = 693)
    (hT : ∀ k < 693, tvCols k = (Cs.getD k []).toArray) (hW : ∀ v ∈ W, isWt v = true)
    (h : cwK (wBits W) E Cs = true) : CFSG.LargeExtraspecial.S14.SMI.chkCommWt = true := by
  obtain ⟨-, hs⟩ := cwK_sound _ _ _ h
  unfold CFSG.LargeExtraspecial.S14.SMI.chkCommWt
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 693 := List.mem_range.1 hk
  obtain ⟨h1, h2⟩ := hs k (by omega)
  rw [tvArr_get hk', hT k hk']
  unfold CFSG.LargeExtraspecial.S14.SMI.commWt
  rw [List.any_eq_true]
  refine ⟨E.getD k 0, List.mem_range.2 h1, ?_⟩
  rw [applyCols_toArray]
  rw [wBits_testBit, List.contains_iff_mem] at h2
  exact hW _ h2

end CFSG.SmithE.K
