module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutRed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Excl
public import CFSG.Sporadic.J4.QTOutAuto

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Blueprint CFSG.ComponentClassification CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem outer_odd_J
    : Odd (Nat.card (OuterAutomorphisms.Outer J)) := by
  have hM := j4Facts.mat
  have hF := j4Facts
  let S : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  refine J4Out.odd_card_outer_of_sylow J S (fun α _ hα => ?_)
  have hαP : ∀ x ∈ P0, α x ∈ P0 := by
    intro x hx
    have h := hα x (by rw [Sylow.coe_ofCard]; exact hx)
    rwa [Sylow.coe_ofCard] at h
  obtain ⟨k, hk⟩ := aut_of_maps_P0 hF α hαP
  exact ⟨k, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hk x]⟩

theorem j4OuterOdd
    : J4OuterOddProp :=
  @J4Out.odd_card_outer_of_mulEquiv (NativeSporadic.Carrier .J4) J _ _
    (seedEquiv j4Facts.mat) outer_odd_J

theorem j4ExclusionProp_proved
    : J4ExclusionProp := j4ExclusionProp_of_outerOdd j4OuterOdd

theorem sporadicExclusion_J4_proved
    : SporadicExclusion .J4 :=
  sporadicExclusion_J4_of_outerOdd j4OuterOdd

end CFSG.QuasithinUnique.Setup.X1
