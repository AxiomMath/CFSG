module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem pockets_sup_eq {G : Type} [Group G] [Finite G] (hP5 : Asc82FactPockets5) {L : Subgroup G}
    (hL : IsPSp43 L) {z : G} (hz : orderOf z = 2) {K1 K2 : Subgroup G} (h1 : Sl23PocketIn L z K1)
    (h2 : Sl23PocketIn L z K2) (hne : K1 ≠ K2) :
    K1 ⊔ K2 = oTwoRes (L ⊓ centralizer ({z} : Set G)) ∧
      (K1 ⊔ K2).relIndex (L ⊓ centralizer ({z} : Set G)) = 2 := by
  obtain ⟨K1', K2', -, -, -, huniq, -, hsup', hrel', -⟩ := hP5 G L hL z ⟨hz, K1, h1⟩
  rcases huniq K1 h1 with e1 | e1 <;> rcases huniq K2 h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · rw [e1, e2]
    exact ⟨hsup'.symm, hrel'⟩
  · rw [e1, e2, sup_comm]
    exact ⟨hsup'.symm, hrel'⟩
  · exact absurd (e1.trans e2.symm) hne

end CFSG.OddStandard.SmallF3.Omega
