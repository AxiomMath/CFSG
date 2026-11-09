module

public import CFSG.Certificates.Kernel.Spor.RowSound
public import CFSG.Certificates.Kernel.Misc.HexDropSound
import all CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.HexText
open CFSG.KS.Text (hexV)

@[expose] def RowsW (cs : List Char) (d n w : Nat) (F : Nat → Nat) (a b : Nat) : Prop :=
  ∀ j, a ≤ j → j < b → ∀ i < n, pg w (mask w) (F j) i = numA cs (d * (n * j + i)) d ∧
    ∀ s < d, d * (n * j + i) + s < cs.length ∧ hexV (Char.toNat cs[d * (n * j + i) + s]!) < 16

theorem dropL3 (cs : List Char) (x y z : Nat) :
    dropL x (dropL y (dropL z cs)) = cs.drop (z + y + x) := by
  simp only [dropL_eq, List.drop_drop]
  all_goals (congr 1; omega)

open CFSG.KS.PackFld in
theorem rowsW_of_run {cs : List Char} {d n w a b x y z : Nat} {F : Nat → Nat} (hd : 0 < d)
    (hn : 0 < n) (hab : a ≤ b) (hxyz : z + y + x = d * (n * a))
    (h : run d n w b F (dropL x (dropL y (dropL z cs))) a 0 0 0 0 = true) :
    RowsW cs d n w F a b := by
  rw [dropL3, hxyz] at h
  have T := tables (cs := cs) (F := F) (w := w) (N := b) (d := d) hd hn (b - a) a (by omega) h
  intro j h1 h2 i hi
  obtain ⟨hA, hF⟩ := T j h1 h2
  refine ⟨?_, (hA i hi).2⟩
  rw [pg_of_fld hF (by simp only [hi, ↓reduceIte]; exact (hA i hi).1)]
  simp only [hi, ↓reduceIte]

theorem rowsW_cat {cs : List Char} {d n w a b c : Nat} {F : Nat → Nat}
    (h₁ : RowsW cs d n w F a b) (h₂ : RowsW cs d n w F b c) : RowsW cs d n w F a c := by
  intro j hj1 hj2
  by_cases h : j < b
  · exact h₁ j hj1 h
  · exact h₂ j (by omega) hj2

theorem hexTable_of_rowsW {cs : List Char} {d n w N : Nat} {F : Nat → Nat} (hd : 0 < d)
    (hn : 0 < n) (hR : RowsW cs d n w F 0 N) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d n (n * j) (String.ofList cs) =
      unpack n w (F j) := by
  have bound : ∀ j < N, ∀ i < n, ∀ s < d, d * (n * j + i) + s < d * n * N := by
    intro j hj i hi s hs
    have h1 : n * j + i + 1 ≤ n * N := by
      have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      omega
    have h2 := Nat.mul_le_mul_left d h1
    rw [Nat.mul_succ] at h2
    rw [Nat.mul_assoc]
    omega
  have hpos : ∀ k < d * n * N, k < cs.length ∧ hexV (Char.toNat cs[k]!) < 16 := by
    intro k hk
    have hq : k / d < n * N := by
      rw [Nat.div_lt_iff_lt_mul hd]
      rw [Nat.mul_comm (n * N) d, ← Nat.mul_assoc]
      exact hk
    have hjj : k / d / n < N := by
      rw [Nat.div_lt_iff_lt_mul hn]
      rw [Nat.mul_comm N n]
      exact hq
    have ek : k = d * (n * (k / d / n) + k / d % n) + k % d := by
      rw [Nat.div_add_mod (k / d) n, Nat.div_add_mod k d]
    obtain ⟨-, hB⟩ := hR (k / d / n) (Nat.zero_le _) hjj (k / d % n) (Nat.mod_lt _ hn)
    obtain ⟨hl, hx⟩ := hB (k % d) (Nat.mod_lt _ hd)
    rw [← ek] at hl hx
    exact ⟨hl, hx⟩
  have hasc : ∀ k < d * n * N, k < cs.length ∧ (cs[k]!).toNat < 128 := by
    intro k hk
    refine ⟨(hpos k hk).1, ?_⟩
    rcases hexV_dig (hpos k hk).2 with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  intro j hj
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem_ofFn]
    rw [(hR j (Nat.zero_le _) hj i hi).1]
    exact num_bytes (o := d * (n * j + i)) hasc
      (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8 (d * (n * j + i)) c)
      rfl (fun c => rfl) d (by have := bound j hj i hi (d - 1) (by omega); omega)
      (fun s hs => (hpos _ (bound j hj i hi s hs)).2)

theorem hexTable_rows_of {cs : List Char} {d w N r k : Nat} {F : Nat → Nat}
    (hs : ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d 32 (32 * j) (String.ofList cs) =
      unpack 32 w (F j)) (hk : r * k + r ≤ N) :
    CFSG.Monster.B.Co2.Native.hexTable d (32 * r) (32 * r * k) (String.ofList cs) =
      CFSG.KS.Row.rowArr (32 * r) w F (r * k) := by
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Row.rowArr]
  · intro i h1 _
    have hi : i < 32 * r := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    have hj : r * k + i / 32 < N := by omega
    have hm : i % 32 < 32 := Nat.mod_lt i (by omega)
    have e := congrArg (fun a : Array Nat => a[i % 32]?) (hs (r * k + i / 32) hj)
    simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem?_ofFn, hm, dite_true,
      Option.some.injEq] at e
    simp only [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Row.rowArr, Array.getElem_ofFn,
      CFSG.KS.Row.rg]
    have ei : 32 * r * k + i = 32 * (r * k + i / 32) + i % 32 := by
      have := Nat.div_add_mod i 32
      rw [Nat.mul_add, ← Nat.mul_assoc]
      omega
    have e5 : Nat.shiftRight i 5 = i / 32 := Nat.shiftRight_eq_div_pow i 5
    have e31 : Nat.land i 31 = i % 32 := Nat.and_two_pow_sub_one_eq_mod i 5
    rw [ei, e5, e31]
    exact e

end CFSG.KC.Misc.HexFlat

end
