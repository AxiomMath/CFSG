module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LargeFrameExits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Recog

theorem q8TwinRecogEx_of_thm1RTwinLiftSet
    (h : ∀ n, CIT3Below n → TightBelow n → Thm1RTwinLiftSetBelow (n + 1)) :
    QuaternionBridge.Q8TwinRecogEx ExSpD4 := by
  intro Y _ _ hF hnab hB hTB R S t hd hq hg hΩ hA _ htw
  have ht1 : t ≠ 1 := by
    intro h1
    have := hd.order
    rw [h1, orderOf_one] at this
    omega
  rcases h (Nat.card Y) hB hTB Y (Nat.lt_succ_self _) R S t hd hq hg (oddCore_eq_bot_of_fstar hnab)
      hΩ hA htw with h1 | h2 | h3
  · exact absurd h1 (not_tightInO2_of_fstar hnab ht1)
  · exact Or.inr (h2.exSpD4 hnab)
  · exact Or.inl (h3.hasLift htw)

theorem q8TwinRecogExLie_of_thm1RTwinLiftSet
    (h : ∀ n, CIT3Below n → TightBelow n → Thm1RTwinLiftSetBelow (n + 1)) :
    QuaternionBridge.Q8TwinRecogEx (fun Y _ _ => QuaternionBridge.ExLie Y) := by
  intro Y _ _ hF hnab hB hTB R S t hd hq hg hΩ hA _ htw
  have ht1 : t ≠ 1 := by
    intro h1
    have := hd.order
    rw [h1, orderOf_one] at this
    omega
  rcases h (Nat.card Y) hB hTB Y (Nat.lt_succ_self _) R S t hd hq hg (oddCore_eq_bot_of_fstar hnab)
      hΩ hA htw with h1 | h2 | h3
  · exact absurd h1 (not_tightInO2_of_fstar hnab ht1)
  · exact Or.inr (h2.exLie hnab)
  · exact Or.inl (h3.hasLift htw)

theorem tightCentTwinLift_of_thm1RTwinLiftSet
    (h : ∀ n, CIT3Below n → TightBelow n → Thm1RTwinLiftSetBelow (n + 1)) (n : ℕ) :
    TightCentTwinLift n :=
  QuaternionBridge.tightCentTwinLift_of_q8RecogLie (q8TwinRecogExLie_of_thm1RTwinLiftSet h) n

theorem q8TwinRecogLarge_of_thm1RTwinLiftSet
    (h : ∀ n, CIT3Below n → TightBelow n → Thm1RTwinLiftSetBelow (n + 1)) : Q8TwinRecogLarge :=
  q8TwinRecogLarge_of_recogEx (q8TwinRecogEx_of_thm1RTwinLiftSet h)

end Recog

section Large

theorem residualCFrameLarge_of_twinLiftSet
    (htwin : ∀ n, CIT3Below n → TightBelow n → Thm1RTwinLiftSetBelow (n + 1)) (hA : FrameAEmpty)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hliftS : ∀ n, TightLargeLiftS n) : TA3.ResidualCFrameLarge :=
  residualCFrameLarge_of_recog_aEmpty (q8TwinRecogLarge_of_thm1RTwinLiftSet htwin) hA htw hsmall
    hliftS (tightCentTwinLift_of_thm1RTwinLiftSet htwin)

end Large

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
