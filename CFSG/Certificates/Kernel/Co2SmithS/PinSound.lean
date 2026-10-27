module

public import Certificates.Data.Kernel.Co2SmithS.Pin
public import CFSG.Certificates.Kernel.Co1BTrSound
public import CFSG.Certificates.Kernel.VecKRegs
public import CFSG.Certificates.Kernel.Co2SmithS.RowsSound

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co2Smith.Native

theorem ofBits8_lt (f : Nat → Bool) : ofBits 8 f < 2 ^ 8 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [ofBits, testBit_ofBitsFold]
    simp [Nat.not_lt.2 hk]

theorem testBit_bit (c s q : Nat) (p : Nat) :
    ((c >>> s &&& 1) <<< q).testBit p = (decide (p = q) && c.testBit s) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : p = q
  · subst h
    simp [Nat.testBit_and, Nat.testBit_shiftRight]
  · by_cases h' : p ≥ q
    · have : p - q ≠ 0 := by omega
      simp only [h', decide_true, Bool.true_and, Nat.testBit_and, Nat.testBit_shiftRight, h,
        decide_false, Bool.false_and]
      rw [testBit_one_eq]
      simp [this]
    · simp [h', h]

theorem xr_eq (c i : Nat) :
    ofBits 8 (fun j => j % 2 == i % 2 && c.testBit (4 * (j / 2) + i / 2)) = xr c i := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [ofBits, testBit_ofBitsFold]
  unfold xr
  simp only [Nat.testBit_or, testBit_bit]
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  by_cases hp : p < 8
  · interval_cases p <;> rcases hi with hi | hi <;> simp [hi] <;> omega
  · have h1 : p ≠ i % 2 := by omega
    have h2 : p ≠ 2 + i % 2 := by omega
    have h3 : p ≠ 4 + i % 2 := by omega
    have h4 : p ≠ 6 + i % 2 := by omega
    simp [hp, h1, h2, h3, h4]

theorem xr_lt (c i : Nat) : xr c i < 2 ^ 8 := by
  rw [← xr_eq]
  exact ofBits8_lt _

theorem xRows_eq (c : Nat) : xRows c = unpackR 8 (xK c) := by
  rw [xRows, unpackR]
  congr 1
  funext i
  rw [← rowF_eq, xK]
  have h := rowF_orN 8 (f := fun i => xr c i) (fun _ _ => xr_lt c _) i.isLt
  rw [show (fun i => Nat.shiftLeft (xr c i) (Nat.mul 8 i)) = fun i => xr c i <<< (8 * i) from rfl, h,
    xr_eq]

theorem wRows8_eq {S : Nat → Nat} (hS : ∀ k < 8, (stdRows ())[k]! = unpackR 8 (S k)) :
    ∀ w : List Nat, (∀ k ∈ w, k < 8) → wRows8 w = unpackR 8 (wK8 S w)
  | [], _ => (CFSG.KC.VecK.unpackR_idF 8).symm
  | k :: w, hw => by
    have e : wRows8 (k :: w) = mulRows 8 (stdRows ())[k]! (wRows8 w) := rfl
    rw [e, hS k (hw k (List.mem_cons_self ..)),
      wRows8_eq hS w fun j hj => hw j (List.mem_cons_of_mem _ hj), mulRows_unpackW]
    rfl

theorem powRows8_eq (M : Nat) : ∀ e, powRows 8 (unpackR 8 M) e = unpackR 8 (pow8 M e)
  | 0 => (CFSG.KC.VecK.unpackR_idF 8).symm
  | e + 1 => by
    have h : powRows 8 (unpackR 8 M) (e + 1) = mulRows 8 (powRows 8 (unpackR 8 M) e) (unpackR 8 M) :=
      rfl
    rw [h, powRows8_eq M e, mulRows_unpackW]
    rfl

theorem fixesAll8_eq (X : Nat) : fixesAll8 (unpackR 8 X) = fixK8 X := by
  unfold fixesAll8 fixK8 colAct8
  rw [transposeRows_unpackR]
  simp only [vecMulN_unpackR]

theorem pinOK_eq {S : Nat → Nat} (hS : ∀ k < 8, (stdRows ())[k]! = unpackR 8 (S k))
    (hb : ∀ r ∈ pinRels, ∀ k ∈ r.1, k < 8) (c : Nat) : pinOK c = pinK S c := by
  unfold pinOK pinK
  refine all_congr' fun r hr => ?_
  rw [xRows_eq, wRows8_eq hS r.1 (hb r hr), mulRows_unpackW, powRows8_eq, fixesAll8_eq]

theorem pinUniqueOK_of {S : Nat → Nat} (hS : ∀ k < 8, (stdRows ())[k]! = unpackR 8 (S k))
    (hb : ∀ r ∈ pinRels, ∀ k ∈ r.1, k < 8)
    (h : ∀ c < 65536, (!pinK S c || c == 24505) = true) : pinUniqueOK () = true := by
  unfold pinUniqueOK
  rw [List.all_eq_true]
  intro c hc
  rw [pinOK_eq hS hb]
  exact h c (List.mem_range.1 hc)

end CFSG.KC.Co2SmithS

end
