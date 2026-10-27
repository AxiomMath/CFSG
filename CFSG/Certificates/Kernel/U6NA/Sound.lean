module

public import Certificates.Data.Kernel.U6NA
public import Certificates.Data.U6NA
public import CFSG.Certificates.Kernel.U6ThreeSound
public import CFSG.Certificates.Kernel.F4NA.Sound

public section

namespace CFSG.KC.U6NA

open CFSG.KC.U6Three CFSG.KC.F4NA CFSG.KC.Loop CFSG.RankThree.PartOne.F106

private theorem blk_key : ∀ a b c : ZMod 3,
    decide (a + b + c = 0) = Nat.beq ((a.val + b.val + c.val) % 3) 0 := by
  decide

theorem blkN_enc (x : U6Mon) : decide (x.blk = 0) = blkN (enc x) := by
  have h0 : x.d0.val = dig (enc x) 0 := d_val x 0
  have h1 : x.d1.val = dig (enc x) 1 := d_val x 1
  have h2 : x.d2.val = dig (enc x) 2 := d_val x 2
  rw [U6Mon.blk, blk_key, h0, h1, h2]
  all_goals rfl

private theorem tor_key : ∀ a b : ZMod 3,
    decide (a = 0 ∧ b = 0) = (Nat.beq a.val 0 && Nat.beq b.val 0) := by
  decide

theorem torN_enc (x : U6Mon) : decide (x.t0 = 0 ∧ x.t1 = 0) = torN (enc x) := by
  rw [tor_key, torN, dig_enc_6, dig_enc_7]

def enc2 (p : ZMod 2 × ZMod 2) : Nat := p.1.val + 2 * p.2.val

private theorem enc2_add : ∀ p q : ZMod 2 × ZMod 2, enc2 (p + q) = Nat.xor (enc2 p) (enc2 q) := by
  decide

private theorem dec_key : ∀ p : ZMod 2 × ZMod 2, decide (p = 0) = Nat.beq (enc2 p) 0 := by
  decide

private theorem term_key : ∀ (t₀ t₁ a : ZMod 3) (i : Fin 6),
    enc2 (if i = u6Perm ![t₀, t₁] i then U6Mon.penc a else 0) =
      tm (if i.val < 3 then t₀.val else t₁.val) a.val := by
  decide +kernel

theorem trN_enc (x : U6Mon) : x.trB = trN (enc x) := by
  have ht : x.t = ![x.t0, x.t1] := rfl
  rw [U6Mon.trB, U6Mon.trSum, dec_key, Fin.sum_univ_six, enc2_add, enc2_add, enc2_add, enc2_add,
    enc2_add, ht, term_key, term_key, term_key, term_key, term_key, term_key, d_val, d_val, d_val,
    d_val, d_val, d_val, ← dig_enc_6, ← dig_enc_7]
  all_goals rfl

theorem recMask_sound : ∀ (l : List (Nat × List Nat × Nat × Nat)) (i : Nat),
    bt (recMask l) i = true → ∃ r ∈ l, r.1 = i
  | [], i, h => by
    have e0 : recMask ([] : List (Nat × List Nat × Nat × Nat)) = 0 := rfl
    rw [bt_eq, e0, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | r :: l, i, h => by
    have e : recMask (r :: l) = recMask l ||| 1 <<< r.1 := rfl
    rw [bt_eq, e, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨s, hs, es⟩ := recMask_sound l i (by rw [bt_eq]; exact h)
      exact ⟨s, List.mem_cons_of_mem _ hs, es⟩
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
      exact ⟨r, List.mem_cons_self, h⟩

theorem cov6_sound {TP : Nat} {l : List (Nat × List Nat × Nat × Nat)}
    (h : cov6B TP (recMask l) = true) :
    ∀ i < 729, torN (tabN TP i) = false → ∃ r ∈ l, r.1 = i := by
  intro i hi ht
  have h1 := allBelow_sound h (by norm_num) i hi
  rw [ht] at h1
  exact recMask_sound l i h1

end CFSG.KC.U6NA

end
