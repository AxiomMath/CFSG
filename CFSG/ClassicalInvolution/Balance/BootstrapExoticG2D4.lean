module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_g2d4 (hΩ : InClass p f Ω) (h9 : p ^ f = 9)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  rcases hi with hi | hi
  · exact exists_member_leviBlockImage_of_g2 (by rw [h9]; norm_num)
      (eq_three_and_two_of_pow_eq_nine h9).1 D i hi
  · exact exists_member_leviBlockImage_of_trialityD4 hΩ h9 D i hi

end CFSG.ClassicalInvolution.Balance
