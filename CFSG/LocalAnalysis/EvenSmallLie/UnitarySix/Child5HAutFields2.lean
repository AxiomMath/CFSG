module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutFields
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAPerm

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem Λ_comm_CA₄' (hΘ : ThetaSpec t e Θ) :
    ∀ l ∈ (sec3DData e t).Λ, ∀ n ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
      ⁅l, n⁆ ∈ (sec3DData e t).withT (sec3DData e t).A₃ :=
  Λ_comm_CA₄_of hΘ centralizer_A4_dec

theorem center_CA₄' (hΘ : ThetaSpec t e Θ) :
    ∀ n ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
      (∀ m ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
        ⁅n, m⁆ ∈ (sec3DData e t).withT (sec3DData e t).A₃) →
      n ^ 3 ∈ (sec3DData e t).withT (sec3DData e t).A₃ :=
  center_CA₄_of hΘ centralizer_A4_dec

end CFSG.EvenSmallLie.UnitarySix.Child5
