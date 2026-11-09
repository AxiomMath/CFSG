module

public import CFSG.Certificates.Kernel.Misc.HexDropSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import all CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.HexText
open CFSG.KS.Text (hexV)

@[expose] def RowsD (cs : List Char) (d n w : Nat) (F : Nat → Nat) (a b : Nat) : Prop :=
  ∀ j, a ≤ j → j < b → ∀ i < n, pg w (mask w) (F j) i = numA cs (d * (n * j + i)) d ∧
    ∀ s < d, d * (n * j + i) + s < cs.length ∧ hexV (Char.toNat cs[d * (n * j + i) + s]!) < 16

theorem dropL_dropL_eq (cs : List Char) (x y : Nat) : dropL x (dropL y cs) = cs.drop (y + x) := by
  simp only [dropL_eq, List.drop_drop]
  all_goals (congr 1; omega)

open CFSG.KS.PackFld in
theorem rowsD_of_run {cs : List Char} {d n w a b x y : Nat} {F : Nat → Nat} (hd : 0 < d)
    (hn : 0 < n) (hab : a ≤ b) (hxy : y + x = d * (n * a))
    (h : run d n w b F (dropL x (dropL y cs)) a 0 0 0 0 = true) : RowsD cs d n w F a b := by
  rw [dropL_dropL_eq, hxy] at h
  have T := tables (cs := cs) (F := F) (w := w) (N := b) (d := d) hd hn (b - a) a
    (by omega) h
  intro j h1 h2 i hi
  obtain ⟨hA, hF⟩ := T j h1 h2
  refine ⟨?_, (hA i hi).2⟩
  rw [pg_of_fld hF (by simp only [hi, ↓reduceIte]; exact (hA i hi).1)]
  simp only [hi, ↓reduceIte]

theorem rowsD_cat {cs : List Char} {d n w a b c : Nat} {F : Nat → Nat}
    (h₁ : RowsD cs d n w F a b) (h₂ : RowsD cs d n w F b c) : RowsD cs d n w F a c := by
  intro j hj1 hj2
  by_cases h : j < b
  · exact h₁ j hj1 h
  · exact h₂ j (by omega) hj2

private theorem pos_lt {d n N j i s : Nat} (hj : j < N) (hi : i < n) (hs : s < d) :
    d * (n * j + i) + s < d * n * N := by
  have h1 : n * j + i + 1 ≤ n * N := by
    have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ] at this
    omega
  have h2 := Nat.mul_le_mul_left d h1
  rw [Nat.mul_succ] at h2
  rw [Nat.mul_assoc]
  omega

theorem hexTable_sound_rowsD {cs : List Char} {d n w N : Nat} {F : Nat → Nat} (hd : 0 < d)
    (hn : 0 < n) (hR : RowsD cs d n w F 0 N) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d n (n * j) (String.ofList cs) =
      unpack n w (F j) := by
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
    obtain ⟨hl, hx⟩ := hpos k hk
    refine ⟨hl, ?_⟩
    rcases hexV_dig hx with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  intro j hj
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem_ofFn]
    obtain ⟨e1, e2⟩ := hR j (Nat.zero_le _) hj i hi
    rw [e1]
    exact num_bytes (o := d * (n * j + i)) hasc
      (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8 (d * (n * j + i)) c)
      rfl (fun c => rfl) d (by have := pos_lt (d := d) (s := d - 1) hj hi (by omega); omega)
      (fun s hs => (e2 s hs).2)

end CFSG.KC.Misc.HexFlat

end
