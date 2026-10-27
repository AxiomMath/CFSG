module

public import Certificates.Data.Kernel.Spor.WordChunk
public import Certificates.Data.Kernel.Spor.Prim
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

theorem wordAccK_append (n w m acc : Nat) (S SI : Nat → Nat) :
    ∀ a b : List Int, wordAccK n w m acc S SI (a ++ b) =
      wordAccK n w m (wordAccK n w m acc S SI b) S SI a
  | [], _ => rfl
  | z :: a, b => by
    have e : ∀ (x : Nat) (l : List Int), wordAccK n w m x S SI (z :: l) =
        strictN (wordAccK n w m x S SI l) (fun T => strictN (icode z) (fun c =>
          pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
            S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
            SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := fun _ _ => rfl
    rw [List.cons_append, e, e, wordAccK_append n w m acc S SI a b]

theorem wordK_eq_wordAccK (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Int) :
    wordK n w m idn S SI wd = wordAccK n w m idn S SI wd := rfl

theorem chunk_step {n w m idn : Nat} {S SI : Nat → Nat} {wd : List Int} {L : Nat} {V : Nat → Nat}
    {i : Nat} (h : chunkK n w m idn S SI wd L V i = true)
    (hnext : i + L < wd.length → wordAccK n w m idn S SI (wd.drop (i + L)) = V (i + L)) :
    wordAccK n w m idn S SI (wd.drop i) = V i := by
  have hc := Nat.eq_of_beq_eq_true h
  have hd : (wd.drop i).drop L = wd.drop (i + L) := by
    rw [List.drop_drop]
  rw [← List.take_append_drop L (wd.drop i), wordAccK_append, hd]
  by_cases hb : i + L < wd.length
  · have hbt : Nat.blt (Nat.add i L) wd.length = true := by
      rw [Nat.blt_eq]
      exact hb
    rw [hbt] at hc
    rw [hnext hb]
    exact hc
  · have hbf : Nat.blt (Nat.add i L) wd.length = false := by
      cases e : Nat.blt (Nat.add i L) wd.length
      · rfl
      · exact absurd (Nat.blt_eq.mp e) hb
    rw [hbf] at hc
    rw [List.drop_eq_nil_of_le (by omega)]
    exact hc

theorem wordK_of_chunks {n w m idn : Nat} {S SI : Nat → Nat} {wd : List Int} {L NC : Nat}
    {V : Nat → Nat} (hlen : wd.length ≤ NC * L) (hNC : 0 < NC)
    (h : ∀ c < NC, chunkK n w m idn S SI wd L V (c * L) = true) :
    wordK n w m idn S SI wd = V 0 := by
  have key : ∀ d c, NC = c + d + 1 →
      wordAccK n w m idn S SI (wd.drop (c * L)) = V (c * L) := by
    intro d
    induction d with
    | zero =>
      intro c hc
      refine chunk_step (h c (by omega)) fun hb => absurd hb ?_
      have : c * L + L = NC * L := by rw [hc]; ring
      omega
    | succ d ih =>
      intro c hc
      refine chunk_step (h c (by omega)) fun _ => ?_
      have e : c * L + L = (c + 1) * L := by ring
      rw [e]
      exact ih (c + 1) (by omega)
  have h0 := key (NC - 1) 0 (by omega)
  rw [Nat.zero_mul, List.drop_zero] at h0
  rw [wordK_eq_wordAccK]
  exact h0

theorem wordEqK_of_chunks {n w kS : Nat} {S SI : Nat → Nat} {wd : List Int} {L NC : Nat}
    {V : Nat → Nat} (hsz : szOK n w = true) (hl : lettersK kS wd = true)
    (hlen : wd.length ≤ NC * L) (hNC : 0 < NC)
    (h : ∀ c < NC, chunkK n w (mask w) (pidn n w) S SI wd L V (c * L) = true) :
    CFSG.KS.Prim.wordEqK n w (mask w) (pidn n w) S SI kS wd (V 0) = true := by
  unfold CFSG.KS.Prim.wordEqK
  rw [hsz, hl, wordK_of_chunks hlen hNC h, Nat.beq_refl]

end CFSG.KS.Raw

end
