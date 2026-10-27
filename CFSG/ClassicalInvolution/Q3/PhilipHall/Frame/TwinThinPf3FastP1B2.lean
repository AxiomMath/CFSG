module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FilterN

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

private def g4P1 : List (ℕ × ℕ) :=
  [(17, 267069840090634), (65, 257867905664908), (65, 267069840090634), (5, 257867905664908)]

private def perms1P1 : List (List ℕ × List ℕ) :=
  [([0, 2, 5, 7, 6, 4, 3, 1], [0, 7, 1, 6, 5, 2, 4, 3]),
    ([0, 4, 1, 5, 6, 2, 7, 3], [0, 2, 5, 7, 1, 3, 4, 6]),
    ([0, 5, 7, 2, 6, 3, 1, 4], [0, 6, 3, 5, 7, 1, 4, 2]),
    ([0, 7, 3, 4, 6, 1, 5, 2], [0, 5, 7, 2, 3, 6, 4, 1]),
    ([1, 3, 4, 6, 7, 5, 2, 0], [7, 0, 6, 1, 2, 5, 3, 4]),
    ([1, 4, 6, 3, 7, 2, 0, 5], [6, 0, 5, 3, 1, 7, 2, 4]),
    ([1, 5, 0, 4, 7, 3, 6, 2], [2, 0, 7, 5, 3, 1, 6, 4]),
    ([1, 6, 2, 5, 7, 0, 4, 3], [5, 0, 2, 7, 6, 3, 1, 4])]

private def perms2P1 : List (List ℕ × List ℕ) :=
  [([2, 0, 7, 5, 4, 6, 1, 3], [1, 6, 0, 7, 4, 3, 5, 2]),
    ([2, 5, 1, 6, 4, 3, 7, 0], [7, 2, 0, 5, 4, 1, 3, 6]),
    ([2, 6, 3, 7, 4, 0, 5, 1], [5, 7, 0, 2, 4, 6, 1, 3]),
    ([2, 7, 5, 0, 4, 1, 3, 6], [3, 5, 0, 6, 4, 2, 7, 1]),
    ([3, 1, 6, 4, 5, 7, 0, 2], [6, 1, 7, 0, 3, 4, 2, 5]),
    ([3, 4, 0, 7, 5, 2, 6, 1], [2, 7, 5, 0, 1, 4, 6, 3]),
    ([3, 6, 4, 1, 5, 0, 2, 7], [5, 3, 6, 0, 2, 4, 1, 7]),
    ([3, 7, 2, 6, 5, 1, 4, 0], [7, 5, 2, 0, 6, 4, 3, 1])]

private def perms3P1 : List (List ℕ × List ℕ) :=
  [([4, 0, 5, 1, 2, 6, 3, 7], [1, 3, 4, 6, 0, 2, 5, 7]),
    ([4, 1, 3, 6, 2, 7, 5, 0], [7, 1, 4, 2, 0, 6, 3, 5]),
    ([4, 3, 7, 0, 2, 5, 1, 6], [3, 6, 4, 1, 0, 5, 7, 2]),
    ([4, 6, 1, 3, 2, 0, 7, 5], [5, 2, 4, 3, 0, 7, 1, 6]),
    ([5, 0, 2, 7, 3, 6, 4, 1], [1, 7, 2, 4, 6, 0, 5, 3]),
    ([5, 1, 4, 0, 3, 7, 2, 6], [3, 1, 6, 4, 2, 0, 7, 5]),
    ([5, 2, 6, 1, 3, 4, 0, 7], [6, 3, 1, 4, 5, 0, 2, 7]),
    ([5, 7, 0, 2, 3, 1, 6, 4], [2, 5, 3, 4, 7, 0, 6, 1])]

private def perms4P1 : List (List ℕ × List ℕ) :=
  [([6, 1, 5, 2, 0, 7, 3, 4], [4, 1, 3, 6, 7, 2, 0, 5]),
    ([6, 2, 7, 3, 0, 4, 1, 5], [4, 6, 1, 3, 5, 7, 0, 2]),
    ([6, 3, 1, 4, 0, 5, 7, 2], [4, 2, 7, 1, 3, 5, 0, 6]),
    ([6, 4, 3, 1, 0, 2, 5, 7], [4, 3, 5, 2, 1, 6, 0, 7]),
    ([7, 0, 4, 3, 1, 6, 2, 5], [1, 4, 6, 3, 2, 7, 5, 0]),
    ([7, 2, 0, 5, 1, 4, 6, 3], [2, 4, 1, 7, 5, 3, 6, 0]),
    ([7, 3, 6, 2, 1, 5, 0, 4], [6, 4, 3, 1, 7, 5, 2, 0]),
    ([7, 5, 2, 0, 1, 3, 4, 6], [3, 4, 2, 5, 6, 1, 7, 0])]

private theorem chk1_P1 :
    FilterN.filterN g4P1 dataP1.rels (dataP1.candsF.map Prod.fst) perms1P1 masksN = true := by
  decide +kernel

private theorem chk2_P1 :
    FilterN.filterN g4P1 dataP1.rels (dataP1.candsF.map Prod.fst) perms2P1 masksN = true := by
  decide +kernel

private theorem chk3_P1 :
    FilterN.filterN g4P1 dataP1.rels (dataP1.candsF.map Prod.fst) perms3P1 masksN = true := by
  decide +kernel

private theorem chk4_P1 :
    FilterN.filterN g4P1 dataP1.rels (dataP1.candsF.map Prod.fst) perms4P1 masksN = true := by
  decide +kernel

theorem filter_ok_P1 : ∀ g ∈ dataP1.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ dataP1.rels, eqPF (evalF (dataP1.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r)
      oneF) →
      ∃ e ∈ dataP1.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ :=
  FilterN.filter_ok_of dataP1 g4P1 (perms1P1 ++ perms2P1 ++ perms3P1 ++ perms4P1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [FilterN.filterN_append, FilterN.filterN_append, FilterN.filterN_append,
      chk1_P1, chk2_P1, chk3_P1, chk4_P1]; rfl)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
