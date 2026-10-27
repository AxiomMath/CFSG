module

public import CFSG.Certificates.Kernel.Spor.RawSchOSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

theorem schK_of_sch7OL {n w kS kO BP i TS NSi N1 N2 N3 N4 N5 N6 CH : Nat}
    {S SI LR TR TRI : Nat → Nat} {W : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 7) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 7) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (h23 : lv12K w (mask w) S SI kS BP (i + 1) (stepsAt n w S kS BP (i + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1)) = true)
    (h34 : lv12K w (mask w) S SI kS BP (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1)) = true)
    (h45 : lv12K w (mask w) S SI kS BP (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1)) = true)
    (h56 : lv12K w (mask w) S SI kS BP (i + 1 + 1 + 1 + 1)
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hTO : allN kO (fun j => anyLt (stCnt TS) (fun a => Nat.beq (stAt TS a) j)) = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7) i TS
      (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7)
      (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (hc3 : rcnt (LR (i + 1 + 1 + 1)) ≤ N3 * CH)
    (hs3 : ∀ s < N3, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7)
      (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1)) (s * CH) CH = true)
    (hc4 : rcnt (LR (i + 1 + 1 + 1 + 1)) ≤ N4 * CH)
    (hs4 : ∀ s < N4, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7)
      (i + 1 + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1)) (s * CH) CH = true)
    (hc5 : rcnt (LR (i + 1 + 1 + 1 + 1 + 1)) ≤ N5 * CH)
    (hs5 : ∀ s < N5, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7)
      (i + 1 + 1 + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1)) (s * CH) CH = true)
    (hc6 : rcnt (LR (i + 1 + 1 + 1 + 1 + 1 + 1)) ≤ N6 * CH)
    (hs6 : ∀ s < N6, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7)
      (i + 1 + 1 + 1 + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1 + 1)) (s * CH) CH =
        true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 7) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  refine schK_of_schOL_orig hh hl (by omega) hinv (fun k hk => ?_) hTS hTO hc hs
    (fun k hk => ?_) h₀ cnt
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · exact h12
    · exact h23
    · exact h34
    · exact h45
    · exact h56
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨N1, hc1, hs1⟩
    · exact ⟨N2, hc2, hs2⟩
    · exact ⟨N3, hc3, hs3⟩
    · exact ⟨N4, hc4, hs4⟩
    · exact ⟨N5, hc5, hs5⟩
    · exact ⟨N6, hc6, hs6⟩

end CFSG.KS.Raw.Orb

end
