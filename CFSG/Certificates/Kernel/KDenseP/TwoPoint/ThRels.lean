module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Pairs

public section

namespace CFSG.KC.KDenseP.TwoPoint

open CFSG.Monster.AxisCount CFSG.Monster.Existence TauCeti

@[expose] def thRelsL : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(0, true), (3, false), (2, false), (3, false), (2, false), (3, false), (2, false), (3, false),
      (2, false)],
    [(2, true), (4, true), (2, true), (4, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(1, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (4, true),
      (1, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (4, true),
      (1, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (4, true),
      (1, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (4, true)],
    [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true)],
    [(5, false), (0, false), (5, true), (0, true)],
    [(5, false), (1, false), (5, true), (1, true)],
    [(5, false), (2, false), (5, true), (2, true)],
    [(5, true), (3, true), (5, true), (3, true)],
    [(4, false), (5, false), (4, true), (5, true), (5, false), (5, false), (5, false), (4, false),
      (5, true), (5, true), (5, true)],
    [(6, true), (6, true), (6, true)],
    [(6, false), (0, false), (6, true), (0, true)],
    [(6, false), (1, false), (6, true), (1, true)],
    [(6, false), (2, false), (6, true), (2, true)],
    [(6, false), (3, false), (6, true), (3, true)],
    [(6, false), (4, false), (6, true), (4, true)],
    [(6, false), (5, true), (6, true), (5, false), (5, false)],
    [(7, true), (7, true), (2, false), (0, false)],
    [(7, false), (0, false), (7, true), (0, true)],
    [(7, false), (2, false), (7, true), (2, true)],
    [(7, false), (4, false), (7, true), (4, true)],
    [(3, true), (4, true), (7, false), (3, true), (7, true), (3, true), (4, true), (7, false),
      (3, true), (7, true)],
    [(7, false), (1, false), (2, false), (0, false), (1, true), (7, true), (1, false), (0, true),
      (2, true), (1, true), (4, false)],
    [(3, false), (7, false), (3, true), (1, false), (2, false), (0, false), (1, true), (3, false),
      (7, true), (3, true), (1, false), (0, true), (2, true), (1, true), (2, false), (4, false),
      (3, false), (7, false), (3, true), (1, false), (2, false), (0, false), (1, true), (4, false),
      (7, false)],
    [(7, false), (6, true), (7, true), (6, true)],
    [(4, false), (5, false), (5, false), (7, false), (5, true), (5, true), (4, true), (5, false),
      (5, false), (7, true), (5, true), (5, true)],
    [(0, true), (2, true), (5, false), (7, false), (5, false), (7, false), (5, false), (7, false)],
    [(7, true), (5, true), (7, true), (5, true), (7, true), (5, true), (5, false), (7, false),
      (5, true), (7, true), (5, false), (7, false), (5, true), (7, true), (5, false), (7, false),
      (5, true), (7, true), (5, false), (7, false), (5, true), (7, true)],
    [(3, true), (5, false), (5, false), (7, true), (5, true), (5, true), (3, true), (5, false),
      (5, false), (7, true), (5, true), (5, true), (3, true), (5, false), (5, false), (7, true),
      (5, true), (5, true), (3, true), (5, false), (5, false), (7, true), (5, true), (5, true),
      (5, false), (5, false), (4, false), (3, false), (2, false), (3, true), (4, true), (5, true),
      (5, true), (5, true), (4, false), (3, false), (2, false), (3, true), (4, true), (5, false),
      (3, false), (2, false), (3, true), (2, false), (0, false)]]

theorem thRelatorList_letters :
    (Sporadic.Thompson.relatorList.map Relator.toWord).map
      (List.map fun (letter : Fin 8 × Bool) => (letter.1.val, letter.2)) = thRelsL := by
  simp only [Sporadic.Thompson.relatorList, Sporadic.Thompson.relatorsOne,
    Sporadic.Thompson.relatorsTwo, Sporadic.Thompson.relatorsThree, Sporadic.Thompson.relatorsFour,
    Sporadic.Thompson.relatorsFive, Sporadic.Thompson.relatorsSix, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, Relator.commInvInv, Relator.conj, Relator.div,
    Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  rfl

theorem thRelatorLetters_eq : Sporadic.Thompson.presentation.relatorLetters = thRelsL := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def]
  exact thRelatorList_letters

@[expose] def thRK (idx : List ℕ) : Pairs := idx.map fun i => (thRelW thRelsL[i]!, [])

theorem thR_eq (idx : List ℕ) : thR idx = thRK idx := by
  rw [thR, thRK, thRelatorLetters_eq]

end CFSG.KC.KDenseP.TwoPoint

end
