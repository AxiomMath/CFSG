module

public import CFSG.ClassicalInvolution.Asc77.AscE186Close
public import CFSG.ClassicalInvolution.Asc77.AscE186Main
public import CFSG.ClassicalInvolution.Asc77.AscE186Thm2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem e18_6_of_wfree (p f : ℕ) [Fact p.Prime]
    (hcent : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
      (S : Sylow 2 G) (R W H : Subgroup G), MinCex p f Ω K S R W H → E186Cent2 Ω K H)
    (hmin : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
      (S : Sylow 2 G) (R W H : Subgroup G), MinCex p f Ω K S R W H →
        EBelowCent p f (Nat.card G)) : E18_6 p f :=
  e18_6 p f
    (fun G _ _ Ω K S R W H c _ _ hN hNH =>
      MinCex.eq_bot_of_odd c (hcent G Ω K S R W H c) (hmin G Ω K S R W H c) hN hNH)
    (fun G _ _ Ω K S R W H c _ _ hNc hN2 hNH hmeet =>
      MinCex.eq_bot_of_central c (hcent G Ω K S R W H c) (hmin G Ω K S R W H c)
        (e18_2_of_l6_9_l6_11 p f (l6_9_proved p f) (l6_11_proved p f)) hNc hN2 hNH hmeet)
    (thm2 p f)

end CFSG.ClassicalInvolution.Asc77.AscE186
