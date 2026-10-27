module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecS3
public import CFSG.ClassicalInvolution.Q3.TL4StarSecSpin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

theorem starNbr_of_dstarConnected {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (hΦ : ConjInvariant Φ) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (hD : ¬ Disconnected.DConnected Φ) (hc : T3.DStarConnected Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L :=
  starNbr_of_exists hΦ htr (exists_starNbr_of_dstarConn (fun K hK J hJ => hc K hK J hJ) hD)


theorem secIdStarNbrId3_of_lieS4
    (h4 : ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
      (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdLieS4 Φ →
        ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L) :
    SecIdStarNbrId3 := by
  intro X _ _ Φ hR _ _ htr ⟨hD, h⟩
  have hΦ := hR.hyp.conjInvariant
  rcases h with h | h | h | h | h | h | h
  · exact starNbr_of_lieS3 hR htr h
  · exact h4 X Φ hR htr h
  · exact starNbr_of_exitS3 hΦ htr h
  · exact starNbr_of_dstarConnected hΦ htr hD h.2
  · exact starNbr_of_dstarConnected hΦ htr hD h.2
  · exact starNbr_of_dstarConnected hΦ htr hD h.2.2
  · exact starNbr_of_dstarConnected hΦ htr hD h.2.2

theorem secIdStarNbrId3_proved : SecIdStarNbrId3 :=
  secIdStarNbrId3_of_lieS4 fun _ _ _ _ hR htr h => starNbr_of_lieS4 hR htr h

end CFSG.ClassicalInvolution.Q3.TL4
