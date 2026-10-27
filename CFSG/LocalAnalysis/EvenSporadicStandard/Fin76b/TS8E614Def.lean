module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSporadicStandard.Fin76b

structure EFacts614 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  card_aut : Nat.card (MulAut ↥E) = 1920
  cent_dvd : ∀ ψ : MulAut ↥E, ψ * ψ = 1 →
    32 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set (MulAut ↥E)))

end CFSG.EvenSporadicStandard.Fin76b
