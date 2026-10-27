module

public import Certificates.Data.Kernel.SchreierFam.All3
public import CFSG.Certificates.Kernel.SporSch.TitsEnum5Sound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Sporadic.Schreier.RuEnum
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.TitsChain

public section

namespace CFSG.KS.SchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier CFSG.Certificates.Native

variable {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat}

theorem prod3A_eq (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h3 : 3 ≤ nb) {a b c : Nat}
    (ha : a < rcnt (LR 0)) (hb1 : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) (pcomp n w (mask w)
      (trAt n (n * w) LR TR 0 a) (trAt n (n * w) LR TR 1 b)) (trAt n (n * w) LR TR 2 c)) = true ∧
    prod3A n (rawLevels n S base) a b c = unpack n w (pcomp n w (mask w) (pcomp n w (mask w)
      (trAt n (n * w) LR TR 0 a) (trAt n (n * w) LR TR 1 b)) (trAt n (n * w) LR TR 2 c)) := by
  obtain ⟨k0, E0, -⟩ := (lev_trAt hb hp hl (i := 0) (by omega)).2 a ha
  obtain ⟨k1, E1, -⟩ := (lev_trAt hb hp hl (i := 1) (by omega)).2 b hb1
  obtain ⟨k2, E2, -⟩ := (lev_trAt hb hp hl (i := 2) (by omega)).2 c hc
  obtain ⟨hn, -, -, r0⟩ := canonK_facts k0
  obtain ⟨-, -, -, r1⟩ := canonK_facts k1
  obtain ⟨-, -, -, r2⟩ := canonK_facts k2
  refine ⟨canonK_pcomp (canonK_pcomp k0 k1) k2, ?_⟩
  apply Array.ext
  · simp [prod3A, CFSG.Monster.B.Co2.Native.compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [prod3A, CFSG.Monster.B.Co2.Native.compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi), unpack_getT hi]
    unfold prod3A
    rw [CFSG.Monster.B.Co2.compA_get hi, E2 i hi, CFSG.Monster.B.Co2.compA_get (r2 i hi),
      E1 _ (r2 i hi), E0 _ (r1 _ (r2 i hi)), PackFld.pg_pcomp (by omega) hi,
      PackFld.pg_pcomp (by omega) (r2 i hi)]

theorem all3_of_K (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h3 : 3 ≤ nb) {p : Array Nat → Bool}
    {Q : Nat → Bool}
    (hQ : ∀ G, canonK n w (mask w) (n * w) G = true → Q G = true → p (unpack n w G) = true)
    (h : all3K n w (mask w) (n * w) LR TR Q = true) : all3 n (rawLevels n S base) p = true := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  unfold all3
  rw [c0, c1, c2]
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb1 =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => ?_
  obtain ⟨hcan, e⟩ := prod3A_eq hb hp hl h3 ha hb1 hc
  rw [e]
  exact hQ _ hcan (allN_spec (allN_spec (allN_spec h a ha) b hb1) c hc)

end CFSG.KS.SchreierFam
