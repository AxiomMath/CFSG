module

public import Certificates.Data.Kernel.Spor.HexAt
public import CFSG.Certificates.Kernel.Spor.RowSound
import CFSG.Certificates.Kernel.Misc.HexDropSound
import all CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

namespace CFSG.KC.Misc.HexAt

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.HexFlat

private theorem hexAtK_zero {cs : List Char} {d n w N : Nat} {F : Nat → Nat} :
    hexAtK cs 0 d n w N F = hexFlat cs d n w N F := by
  cases cs <;> rfl

private theorem hexAtK_succ_cons {cs : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (c : Char) (t : List Char) (hc : cs = c :: t) :
    hexAtK cs (off + 1) d n w N F =
      bAnd(Nat.blt (Char.toNat c) 128, hexAtK t off d n w N F) := by
  subst hc
  dsimp only [hexAtK]
  rw [show Nat.beq (off + 1) 0 = false from rfl]
  rw [show Nat.sub (off + 1) 1 = off from rfl]
  rw [CFSG.KS.PackFld.strictB_eqP]

private theorem hexAtK_succ_nil {off d n w N : Nat} {F : Nat → Nat} :
    hexAtK [] (off + 1) d n w N F = false := by
  dsimp only [hexAtK]
  rw [show Nat.beq (off + 1) 0 = false from rfl]

private theorem hexAtK_split {cs : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (h : hexAtK cs off d n w N F = true) :
    (∀ k < off, k < cs.length ∧ (cs[k]!).toNat < 128) ∧
      hexFlat (cs.drop off) d n w N F = true := by
  induction off generalizing cs with
  | zero =>
      refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
      rwa [hexAtK_zero] at h
  | succ off ih =>
      cases cs with
      | nil =>
          rw [hexAtK_succ_nil] at h
          exact absurd h Bool.false_ne_true
      | cons c t =>
          rw [hexAtK_succ_cons c t rfl] at h
          rw [bAnd_iff] at h
          obtain ⟨hc, ht⟩ := h
          obtain ⟨hpre, hflat⟩ := ih ht
          refine ⟨fun k hk => ?_, ?_⟩
          · cases k with
            | zero =>
                exact ⟨Nat.zero_lt_succ _, by simpa using Nat.blt_eq.mp hc⟩
            | succ k =>
                have hk' : k < off := by omega
                have := hpre k hk'
                exact ⟨by simpa using this.1, by simpa using this.2⟩
          · simpa using hflat

private theorem hexAtK_ascii {cs : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (h : hexAtK cs off d n w N F = true) :
    ∀ k < off + d * n * N, k < cs.length ∧ (cs[k]!).toNat < 128 := by
  obtain ⟨hpre, hflat⟩ := hexAtK_split h
  obtain ⟨hasc, -⟩ := CFSG.KC.Misc.HexFlat.decode hflat
  intro k hk
  rcases Nat.lt_or_ge k off with hko | hko
  · exact hpre k hko
  · have hk' : k - off < d * n * N := by omega
    obtain ⟨hlen, hlt⟩ := hasc (k - off) hk'
    rw [List.length_drop] at hlen
    rw [CFSG.KC.Misc.HexFlat.getElem!_drop, Nat.add_sub_cancel' hko] at hlt
    exact ⟨by omega, hlt⟩

theorem hexAtK_sound {cs : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (h : hexAtK cs off d n w N F = true) :
    ∀ j < N, ∀ i < n, CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8
      (off + d * (n * j + i)) d = pg w (mask w) (F j) i := by
  obtain ⟨-, hflat⟩ := hexAtK_split h
  have hd : 0 < d := by
    unfold hexFlat at hflat
    simp only [bAnd_iff] at hflat
    exact Nat.blt_eq.mp hflat.1
  obtain ⟨-, hF⟩ := CFSG.KC.Misc.HexFlat.decode hflat
  have hdig := CFSG.KC.Misc.HexFlat.digits_of hflat
  have hasc := hexAtK_ascii h
  intro j hj i hi
  obtain ⟨hval, -⟩ := hF j hj i hi
  have h1 : n * j + i + 1 ≤ n * N := by
    have h := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ] at h
    omega
  have hq : d * (n * j + i) + d ≤ d * n * N := by
    calc d * (n * j + i) + d = d * (n * j + i + 1) := (Nat.mul_succ d (n * j + i)).symm
      _ ≤ d * (n * N) := Nat.mul_le_mul_left d h1
      _ = d * n * N := (Nat.mul_assoc d n N).symm
  rw [hval, CFSG.KC.Misc.HexFlat.numA_drop cs off (d * (n * j + i)) d]
  refine CFSG.KS.HexText.num_bytes (cs := cs) (D := off + d * n * N)
    (o := off + d * (n * j + i)) hasc
    (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8
      (off + d * (n * j + i)) c) rfl (fun c => rfl) d
    (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hq off) ?_
  intro s hs
  have hs' : d * (n * j + i) + s < d * n * N := by omega
  have := hdig (d * (n * j + i) + s) hs'
  rw [CFSG.KC.Misc.HexFlat.getElem!_drop] at this
  simpa only [Nat.add_assoc] using this

theorem hexTable_rowsAt {cs : List Char} {d w R e b : Nat} {G : Nat → Nat}
    (hx : hexAtK cs (d * e) d 32 w R (offF G b) = true) :
    CFSG.Monster.B.Co2.Native.hexTable d (32 * R) e (String.ofList cs) =
      CFSG.KS.Row.rowArr (32 * R) w G b := by
  have hs := hexAtK_sound hx
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Row.rowArr]
  · intro x h1 _
    have hx' : x < 32 * R := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    have e1 := hs (x / 32) (by omega) (x % 32) (Nat.mod_lt x (by omega))
    simp only [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Row.rowArr, Array.getElem_ofFn,
      CFSG.KS.Row.rg]
    have ei : d * (e + x) = d * e + d * (32 * (x / 32) + x % 32) := by
      rw [Nat.div_add_mod]
      exact Nat.mul_add d e x
    have e5 : Nat.shiftRight x 5 = x / 32 := Nat.shiftRight_eq_div_pow x 5
    have e31 : Nat.land x 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5
    rw [ei, e5, e31, e1]
    rfl

theorem hexAt_unpack {cs : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (hx : hexAtK cs off d n w N F = true) {j : Nat} (hj : j < N) :
    Array.ofFn (n := n) (fun i => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8
      (off + d * (n * j + i.val)) d) = CFSG.KS.Raw.unpack n w (F j) := by
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 _
    have hi : i < n := by simpa using h1
    simp only [Array.getElem_ofFn, CFSG.KS.Raw.unpack]
    exact hexAtK_sound hx j hj i hi

end CFSG.KC.Misc.HexAt

end
