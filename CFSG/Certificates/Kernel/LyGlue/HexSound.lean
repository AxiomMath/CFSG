module

public import CFSG.Sporadic.Recognition.LyonsModelInputs
public import Certificates.Data.B3Spor3Checks
import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

namespace CFSG.KC.LyGlue

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsLowHex (c : Char) : Prop :=
  (48 ≤ c.toNat ∧ c.toNat < 58) ∨ (97 ≤ c.toNat ∧ c.toNat < 103)

theorem hexVal_byte {c : Char} (h : IsLowHex c) :
    Ly0.hexVal (UInt8.ofNat c.toNat) = B3S3.hexDigit c := by
  have hlt : c.toNat < 256 := by rcases h with h | h <;> omega
  have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt hlt
  unfold Ly0.hexVal B3S3.hexDigit
  rw [hb]
  have h0 : ('0' ≤ c ∧ c ≤ '9') ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    rw [Char.le_def, Char.le_def]
    rfl
  rcases h with h | h
  · rw [if_neg (by omega), if_pos (h0.2 ⟨h.1, by omega⟩)]
  · rw [if_pos h.1, if_neg (fun hc => by have := (h0.1 hc).2; omega)]

theorem hexDigit_lt {c : Char} (h : IsLowHex c) : B3S3.hexDigit c < 16 := by
  unfold B3S3.hexDigit
  have h0 : ('0' ≤ c ∧ c ≤ '9') ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    rw [Char.le_def, Char.le_def]
    rfl
  split_ifs with hc
  · have := h0.1 hc
    omega
  · rcases h with h | h
    · exact absurd (h0.2 ⟨h.1, by omega⟩) hc
    · omega

theorem byteArray_getElem! (b : ByteArray) (j : ℕ) : b[j]! = b.get! j := by
  rw [CFSG.KS.Text.byteArray_get!_eq]
  by_cases h : j < b.size
  · rw [getElem!_pos b j h, getElem!_pos b.data j h]
    rfl
  · rw [getElem!_neg b j h, getElem!_neg b.data j h]

theorem byte_get {cs : List Char} (hd : ∀ c ∈ cs, IsLowHex c) {j : ℕ} (hj : j < cs.length) :
    (String.ofList cs).toUTF8[j]! = UInt8.ofNat (cs[j]'hj).toNat := by
  have ha : ∀ c ∈ cs.take cs.length, c.toNat < 128 := by
    intro c hc
    rw [List.take_length] at hc
    rcases hd c hc with h | h <;> omega
  rw [byteArray_getElem!]
  exact CFSG.KS.Text.get!_toUTF8 ha hj hj

theorem tabOfHex_get {cs : List Char} (hlen : cs.length = 5 * 66825)
    (hd : ∀ c ∈ cs, IsLowHex c) {i : ℕ} (hi : i < 66825) :
    ((Ly0.tabOfHex (String.ofList cs))[i]!).toNat =
      ((B3S3.hexArrs 4455 5 (String.ofList cs))[i / 4455]!)[i % 4455]! := by
  have hsz : (B3S3.hexArrs 4455 5 (String.ofList cs)).size = 15 := by
    simp [B3S3.hexArrs, hlen]
  have hq : i / 4455 < 15 := by omega
  have hr : i % 4455 < 4455 := Nat.mod_lt _ (by norm_num)
  have hdig : ∀ t < 5,
      Ly0.hexVal ((String.ofList cs).toUTF8[5 * i + t]!) =
        ((cs.map B3S3.hexDigit).toArray)[(i / 4455 * 4455 + i % 4455) * 5 + t]! ∧
      ((cs.map B3S3.hexDigit).toArray)[(i / 4455 * 4455 + i % 4455) * 5 + t]! < 16 := by
    intro t ht
    have h : 5 * i + t < cs.length := by omega
    have e : (i / 4455 * 4455 + i % 4455) * 5 + t = 5 * i + t := by
      rw [Nat.mul_comm (i / 4455), Nat.div_add_mod]
      ring
    rw [byte_get hd h, hexVal_byte (hd _ (List.getElem_mem h)), e,
      getElem!_pos _ _ (by simpa using h)]
    simp only [List.getElem_toArray, List.getElem_map]
    exact ⟨trivial, hexDigit_lt (hd _ (List.getElem_mem h))⟩
  obtain ⟨d0, v0⟩ := hdig 0 (by norm_num)
  simp only [Nat.add_zero] at d0 v0
  obtain ⟨d1, v1⟩ := hdig 1 (by norm_num)
  obtain ⟨d2, v2⟩ := hdig 2 (by norm_num)
  obtain ⟨d3, v3⟩ := hdig 3 (by norm_num)
  obtain ⟨d4, v4⟩ := hdig 4 (by norm_num)
  unfold Ly0.tabOfHex
  rw [getElem!_pos _ i (by simp; exact hi), Array.getElem_ofFn]
  simp only
  rw [getElem!_pos _ (i / 4455) (by rw [hsz]; exact hq)]
  unfold B3S3.hexArrs
  simp only [Array.getElem_ofFn]
  rw [getElem!_pos _ (i % 4455) (by simpa using hr), Array.getElem_ofFn]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  rw [String.toList_ofList, d0, d1, d2, d3, d4, UInt32.toNat_ofNat']
  simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at v0 v1 v2 v3 v4 ⊢
  apply Nat.mod_eq_of_lt
  omega

end CFSG.KC.LyGlue

end
