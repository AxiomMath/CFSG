module

public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem two_sixteen_dich (hV : ∀ v : V, v ^ 2 = 1) {G A E : Subgroup (MulAut V)} (hA : IsOff A)
    (hAG : A ≤ G) (hEG : E ≤ G) (hsub : CFSG.Open.IsSubnormal E G)
    (htype : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection E (commV E) (commV E ⊓ fixV E) (2 * m + 1)) :
    ⁅E, A⁆ = ⊥ ∨ (A ≤ Subgroup.normalizer (E : Set (MulAut V)) ∧
      (fixV A).relIndex (commV E) = (cenIn A (commV E)).relIndex A) := by
  by_cases hcomm : ⁅E, A⁆ = ⊥
  · exact Or.inl hcomm
  right
  rcases htype with ⟨k, hk, hnat⟩ | ⟨m, hm1, hnat⟩
  · have h := two_sixteen_sl hV hk hA hAG hEG hsub hnat hcomm
    exact ⟨h.1, h.2.2.2.2⟩
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1' : m = 1 := by omega
      subst hm1'
      have h := two_sixteen_three hV hA hAG hsub hnat hcomm
      exact ⟨h.1, h.2.2.2.2⟩
    · obtain ⟨hAN, -, β, θX, -, -, -, -, hrel⟩ :=
        two_sixteen_alt hV hm2 hA hAG hEG hsub hnat hcomm
      exact ⟨hAN, hrel⟩

end CFSG.CGT.PushingUpLit.BHS7
