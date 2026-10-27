module

public import Certificates.Data.Kernel.Spor.Row
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.Row

open CFSG.KS.Raw CFSG.Monster.B.Co2.Native

@[expose] noncomputable def rowArr (n w : Nat) (F : Nat → Nat) (o : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => rg w (CFSG.KS.mask w) F o i.val

theorem size_rowArr (n w : Nat) (F : Nat → Nat) (o : Nat) : (rowArr n w F o).size = n := by
  simp [rowArr]

theorem rowArr_get {n w o i : Nat} {F : Nat → Nat} (hi : i < n) :
    (rowArr n w F o)[i]! = rg w (CFSG.KS.mask w) F o i := by
  rw [rowArr, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem rpermK_sound {n w o o' : Nat} {F G : Nat → Nat}
    (h : rpermK n w (CFSG.KS.mask w) F o G o' = true) :
    invCand n (rowArr n w F o) = rowArr n w G o' ∧
      isInvA n (rowArr n w F o) (rowArr n w G o') = true := by
  have hc : ∀ i < n, rg w (CFSG.KS.mask w) F o i < n ∧
      rg w (CFSG.KS.mask w) G o' (rg w (CFSG.KS.mask w) F o i) = i := by
    intro i hi
    have := CFSG.KS.allN_spec h i hi
    rw [CFSG.KS.PackFld.strictB_eqP, CFSG.KS.bAnd_iff, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hinv : isInvA n (rowArr n w F o) (rowArr n w G o') = true := by
    unfold isInvA
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [rowArr_get hi, rowArr_get (hc i hi).1, (hc i hi).2]
    simp [(hc i hi).1]
  refine ⟨?_, hinv⟩
  have hr := CFSG.Monster.B.Co2.rep_permOfArr hinv
  have hi := CFSG.KS.Raw.rep_invCand hr.1
  have hsz : (invCand n (rowArr n w F o)).size = n := by
    have e : ∀ (l : List Nat) (r : Array Nat),
        (l.foldl (fun r i => r.set! (rowArr n w F o)[i]! i) r).size = r.size := by
      intro l
      induction l with
      | nil => intro r; rfl
      | cons a l ih => intro r; rw [List.foldl_cons, ih]; simp
    rw [CFSG.KS.Raw.invCand_eq_foldl, e, Array.size_replicate]
  apply Array.ext
  · rw [hsz, size_rowArr]
  · intro j h1 _
    have hj : j < n := by rwa [hsz] at h1
    rw [← getElem!_pos _ j h1, ← getElem!_pos _ j (by rw [size_rowArr]; exact hj),
      hi.apply hj, hr.2.apply hj]

theorem hexTable_rows {cs : List Char} {d w N r k : Nat} {F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d 32 w N F = true) (hk : r * k + r ≤ N) :
    hexTable d (32 * r) (32 * r * k) (String.ofList cs) = rowArr (32 * r) w F (r * k) := by
  have hs := CFSG.KC.Misc.HexFlat.hexTable_sound hx
  apply Array.ext
  · simp [hexTable, rowArr]
  · intro i h1 _
    have hi : i < 32 * r := by simpa [hexTable] using h1
    have hj : r * k + i / 32 < N := by omega
    have hm : i % 32 < 32 := Nat.mod_lt i (by omega)
    have e := congrArg (fun a : Array Nat => a[i % 32]?) (hs (r * k + i / 32) hj)
    simp only [hexTable, unpack, Array.getElem?_ofFn, hm, dite_true, Option.some.injEq] at e
    simp only [hexTable, rowArr, Array.getElem_ofFn, rg]
    have ei : 32 * r * k + i = 32 * (r * k + i / 32) + i % 32 := by
      have := Nat.div_add_mod i 32
      rw [Nat.mul_add, ← Nat.mul_assoc]
      omega
    have e5 : Nat.shiftRight i 5 = i / 32 := Nat.shiftRight_eq_div_pow i 5
    have e31 : Nat.land i 31 = i % 32 := Nat.and_two_pow_sub_one_eq_mod i 5
    rw [ei, e5, e31]
    exact e

end CFSG.KS.Row

end
