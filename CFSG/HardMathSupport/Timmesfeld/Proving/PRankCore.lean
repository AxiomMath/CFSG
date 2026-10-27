module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem le_pRank_of_elemAbelian_card {p k : ℕ} [Finite G] (hp : 2 ≤ p) {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) :
    k ≤ pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hcard

theorem le_GLBCore_of_le_normalizer {p k : ℕ} [Finite G] {P Q K : Subgroup G}
    (hQP : Q ≤ P) (hk : k ≤ pRank p Q) (hK : K ≤ Subgroup.normalizer (Q : Set G)) :
    K ≤ GLBCore p k P :=
  hK.trans (le_sSup ⟨Q, hQP, hk, rfl⟩)

end CFSG.HardMathSupport.Timmesfeld.Proving
