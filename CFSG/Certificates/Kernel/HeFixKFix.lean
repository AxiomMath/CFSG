module

public import Certificates.Data.Kernel.HeFixK
public import CFSG.Certificates.Kernel.HeAutKLoops
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.HeFixK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.HeAutK

theorem pg_lt_of_canonK {n w m nw p i : Nat} (hp : canonK n w m nw p = true) (hi : i < n) :
    pg w m p i < n := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  simpa [Nat.blt_eq] using allN_spec hp.2.2 i hi

theorem unpack_getElem! {n w p i : Nat} (hi : i < n) : (unpack n w p)[i]! = pg w (mask w) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem countP_fix (n w p : Nat) :
    (List.range n).countP (fun i => (unpack n w p)[i]! == i) = fixK n w p := by
  have key : ∀ k ≤ n, (List.range k).countP (fun i => (unpack n w p)[i]! == i) =
      cntR (fun i => Nat.beq (pg w (mask w) p i) i) 0 k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.countP_append, ih (by omega), cntR_succ]
      congr 1
      simp only [List.countP_singleton, unpack_getElem! (by omega : k < n), Nat.zero_add]
      by_cases e : pg w (mask w) p k = k
      · have h1 : Nat.beq (pg w (mask w) p k) k = true := by
          rw [e]
          exact Nat.beq_refl k
        rw [h1]
        simp [e]
      · have h1 : Nat.beq (pg w (mask w) p k) k = false := by
          cases h : Nat.beq (pg w (mask w) p k) k
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) e
        rw [h1]
        simp [e]
  rw [key n (Nat.le_refl n), fixK]
  cases p <;> rfl

end CFSG.KC.HeFixK

end
