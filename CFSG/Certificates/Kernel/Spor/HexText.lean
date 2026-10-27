module

public import Certificates.Data.Kernel.Spor.Text
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.HexText

open CFSG.KS.PackFld
open CFSG.KS.Text (hexV)

@[expose] noncomputable def numA (cs : List Char) (o : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => numA cs o c * 16 + hexV (Char.toNat cs[o + c]!)

theorem nrec_dec {p : Prop} [Decidable p] (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (decide p) = if p then t else e := by
  by_cases hp : p
  · rw [decide_eq_true hp]
    exact (iteT hp).symm
  · rw [decide_eq_false hp]
    exact (iteF hp).symm

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem hexV_ite (c : Nat) : hexV c = if c < 48 then 16 else if c < 58 then c - 48 else
    if c < 65 then 16 else if c < 71 then c - 55 else 16 := by
  unfold hexV
  rw [blt_dec, blt_dec, blt_dec, blt_dec, nrec_dec, nrec_dec, nrec_dec, nrec_dec]
  rfl

theorem hexV_dig {c : Nat} (h : hexV c < 16) :
    (48 ≤ c ∧ c < 58 ∧ hexV c = c - 48) ∨ (65 ≤ c ∧ c < 71 ∧ hexV c = c - 55) := by
  rw [hexV_ite] at h ⊢
  by_cases h1 : c < 48
  · rw [iteT h1] at h
    omega
  · rw [iteF h1] at h ⊢
    by_cases h2 : c < 58
    · rw [iteT h2] at h ⊢
      omega
    · rw [iteF h2] at h ⊢
      by_cases h3 : c < 65
      · rw [iteT h3] at h
        omega
      · rw [iteF h3] at h ⊢
        by_cases h4 : c < 71
        · rw [iteT h4] at h ⊢
          omega
        · rw [iteF h4] at h
          omega

theorem byte_val {x : Nat} (hx : x < 128) (h : hexV x < 16) :
    (if (UInt8.ofNat x).toNat < 58 then (UInt8.ofNat x).toNat - 48 else (UInt8.ofNat x).toNat - 55) =
      hexV x := by
  have e : (UInt8.ofNat x).toNat = x := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [e]
  rcases hexV_dig h with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · rw [c, iteT b]
  · rw [c, iteF (by omega : ¬ x < 58)]

theorem get!_data (x : ByteArray) (i : Nat) : x.get! i = x.data[i]! := by
  cases x
  rfl

theorem get!_append_left (x y : ByteArray) (i : Nat) (h : i < x.size) :
    (x ++ y).get! i = x.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append]
  have ha : i < x.data.size := by simpa using h
  rw [getElem!_pos (x.data ++ y.data) i (by simp; omega), getElem!_pos x.data i ha,
    Array.getElem_append_left]

theorem get!_append_right (x y : ByteArray) (i : Nat) :
    (x ++ y).get! (x.size + i) = y.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append, ← ByteArray.size_data]
  generalize x.data = a
  generalize y.data = b
  by_cases hb : i < b.size
  · rw [getElem!_pos (a ++ b) _ (by simp; omega), getElem!_pos b i hb, Array.getElem_append_right]
    · congr 1
      omega
    · omega
  · rw [getElem!_neg (a ++ b) _ (by simp; omega), getElem!_neg b i hb]

theorem utf8_single {c : Char} (hc : c.toNat < 128) :
    [c].utf8Encode = [UInt8.ofNat c.toNat].toByteArray := by
  rw [List.utf8Encode_singleton]
  congr 1
  have h : c.val.toNat ≤ 127 := by
    have : c.toNat = c.val.toNat := rfl
    omega
  simp only [String.utf8EncodeChar, h, ↓reduceIte]
  rfl

theorem utf8_get : ∀ (cs : List Char) (D : Nat),
    (∀ k < D, k < cs.length ∧ (cs[k]!).toNat < 128) →
    ∀ k < D, cs.utf8Encode.get! k = UInt8.ofNat (cs[k]!).toNat
  | [], D, hD, k, hk => absurd (hD k hk).1 (Nat.not_lt_zero k)
  | c :: cs, D, hD, k, hk => by
    have hc : c.toNat < 128 := by
      have := (hD 0 (by omega)).2
      simpa using this
    have hs : [UInt8.ofNat c.toNat].toByteArray.size = 1 := by simp
    rw [List.utf8Encode_cons, utf8_single hc]
    cases k with
    | zero =>
      rw [get!_append_left _ _ _ (by rw [hs]; omega), get!_data]
      simp
    | succ k =>
      have e := get!_append_right [UInt8.ofNat c.toNat].toByteArray cs.utf8Encode k
      rw [hs, Nat.add_comm] at e
      rw [e]
      rw [utf8_get cs (D - 1) (fun k' hk'' => by
        have := hD (k' + 1) (by omega)
        simpa using this) k (by omega)]
      simp

theorem num_bytes {cs : List Char} {D o : Nat}
    (hasc : ∀ k < D, k < cs.length ∧ (cs[k]!).toNat < 128) (H : Nat → Nat)
    (h0 : H 0 = 0) (hs : ∀ c, H (c + 1) = H c * 16 +
      (if ((String.ofList cs).toUTF8.get! (o + c)).toNat < 58 then
        ((String.ofList cs).toUTF8.get! (o + c)).toNat - 48 else
        ((String.ofList cs).toUTF8.get! (o + c)).toNat - 55)) :
    ∀ c, o + c ≤ D → (∀ s < c, hexV (Char.toNat cs[o + s]!) < 16) → H c = numA cs o c := by
  intro c
  induction c with
  | zero => intro _ _; exact h0
  | succ c ih =>
    intro hc hdig
    have hk : o + c < D := by omega
    have hb : (String.ofList cs).toUTF8.get! (o + c) = UInt8.ofNat (cs[o + c]!).toNat := by
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
      exact utf8_get cs D hasc (o + c) hk
    rw [hs, hb, byte_val (hasc _ hk).2 (hdig c (Nat.lt_succ_self c)),
      ih (by omega) (fun s hs => hdig s (by omega))]
    rfl

end CFSG.KS.HexText

end
