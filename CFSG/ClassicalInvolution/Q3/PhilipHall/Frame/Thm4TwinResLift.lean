module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform

namespace Thm4Twin


variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)} {J L : Subgroup G}

theorem TwinT4Min.false_of_lifts {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hn : Nat.card G < n)
    (hm : TwinT4Min 3 G Δ J L)
    (hO : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hl : HasLifts Δ) : False := by
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => by
    obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
    exact isPGroup_of_oddCent hm.hyp.hyp hK hz (hO K hK z hz) (hm.hyp.twoGroup K hK)
  have hex : ExactSylow Δ :=
    ExactSylow.of_oddCoreIn_eq_bot fun K hK _ u h => hO K hK u h.inv
  exact hm.notComm (commutes_of_thm4U_exact h4 hn hm.hyp.odd hm.hyp.hyp h2 hl hex hm.hyp.aEmpty
    hm.memJ hm.memL hm.notConj)

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
