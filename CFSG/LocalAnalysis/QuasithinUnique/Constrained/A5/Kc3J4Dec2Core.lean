
module


public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadX0Base
public import CFSG.Sporadic.J4.QT2LocX0Main
public import CFSG.Sporadic.J4.QT2LocX0NMain

public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem five_sq_not_dvd_card_J : ¬ 5 ^ 2 ∣ Nat.card J := by
  rw [card_J j4Facts]
  norm_num

theorem card_centralizer_of_orderOf_five
    (hK0 : Subgroup.centralizer ({fiveElt} : Set J) ≤ X0Sub) {x : J} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set J)) = 6720 := by
  obtain ⟨n, hn⟩ := exists_conj_fiveElt_sq_J4
  obtain ⟨g, hg⟩ := exists_conj_five five_sq_not_dvd_card_J orderOf_fiveElt_J4 hn hx
  have h1 := card_centralizer_singleton_conj g x
  rw [hg] at h1
  rw [← h1]
  have h2 : Subgroup.centralizer ({fiveElt} : Set J) = X0Sub :=
    le_antisymm hK0 X0Sub_le_centralizer_J4
  rw [h2]
  exact card_X0Sub_J4

end CFSG.QuasithinUnique.A5.Dec2
