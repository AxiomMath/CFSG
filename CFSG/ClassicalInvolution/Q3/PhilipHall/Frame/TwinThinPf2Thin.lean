module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2FixE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfShared

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

theorem TwinThinPf.centralizes_of_e64_proved {G : Type} [Group G] {P : Set (Subgroup G)}
    (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub) {y : G}
    (hy : y ∈ Subgroup.normalizer (pSpan P : Set G)) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    {L : Subgroup G} (hL : L ∈ P) (hyL : ∀ l ∈ L, y * l = l * y)
    (htrans : ∀ L' ∈ P, ∃ x ∈ pSpan P, CFSG.ClassicalInvolution.Generic.conjSub x L = L') :
    ∀ x ∈ pSpan P, y * x = x * y :=
  TwinThinPf.centralizes_of_e64 I TwinThinPf.fixTrivial_e64_proved hy hy3 hL hyL htrans

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
