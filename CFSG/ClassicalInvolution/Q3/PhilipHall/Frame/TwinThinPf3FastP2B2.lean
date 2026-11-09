module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FilterN

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

private def g4P2 : List (ℕ × ℕ) :=
  [(17, 267069840090634), (65, 257867905664908), (34, 206444460491416), (130, 132828985085608)]

private def perms1P2 : List (List ℕ × List ℕ) :=
  [([0, 2, 6, 4, 1, 3, 7, 5], [0, 4, 1, 5, 3, 7, 2, 6]),
    ([0, 3, 6, 5, 7, 4, 1, 2], [0, 6, 7, 1, 5, 3, 2, 4]),
    ([0, 4, 6, 2, 3, 7, 5, 1], [0, 7, 3, 4, 1, 6, 2, 5]),
    ([0, 7, 6, 1, 5, 2, 3, 4], [0, 3, 5, 6, 7, 4, 2, 1]),
    ([1, 2, 7, 4, 6, 5, 0, 3], [6, 0, 1, 7, 3, 5, 4, 2]),
    ([1, 3, 7, 5, 0, 2, 6, 4], [4, 0, 5, 1, 7, 3, 6, 2]),
    ([1, 5, 7, 3, 2, 6, 4, 0], [7, 0, 4, 3, 6, 1, 5, 2]),
    ([1, 6, 7, 0, 4, 3, 2, 5], [3, 0, 6, 5, 4, 7, 1, 2])]

private def perms2P2 : List (List ℕ × List ℕ) :=
  [([2, 0, 4, 6, 3, 1, 5, 7], [1, 5, 0, 4, 2, 6, 3, 7]),
    ([2, 1, 4, 7, 5, 6, 3, 0], [7, 1, 0, 6, 2, 4, 5, 3]),
    ([2, 5, 4, 3, 7, 0, 1, 6], [5, 6, 0, 3, 2, 1, 7, 4]),
    ([2, 6, 4, 0, 1, 5, 7, 3], [3, 4, 0, 7, 2, 5, 1, 6]),
    ([3, 0, 5, 6, 4, 7, 2, 1], [1, 7, 6, 0, 4, 2, 3, 5]),
    ([3, 1, 5, 7, 2, 0, 4, 6], [5, 1, 4, 0, 6, 2, 7, 3]),
    ([3, 4, 5, 2, 6, 1, 0, 7], [6, 5, 3, 0, 1, 2, 4, 7]),
    ([3, 7, 5, 1, 0, 4, 6, 2], [4, 3, 7, 0, 5, 2, 6, 1])]

private def perms3P2 : List (List ℕ × List ℕ) :=
  [([4, 0, 2, 6, 7, 3, 1, 5], [1, 6, 2, 5, 0, 7, 3, 4]),
    ([4, 3, 2, 5, 1, 6, 7, 0], [7, 4, 2, 1, 0, 3, 5, 6]),
    ([4, 6, 2, 0, 5, 7, 3, 1], [3, 7, 2, 6, 0, 4, 1, 5]),
    ([4, 7, 2, 1, 3, 0, 5, 6], [5, 3, 2, 4, 0, 6, 7, 1]),
    ([5, 1, 3, 7, 6, 2, 0, 4], [6, 1, 5, 2, 7, 0, 4, 3]),
    ([5, 2, 3, 4, 0, 7, 6, 1], [4, 7, 1, 2, 3, 0, 6, 5]),
    ([5, 6, 3, 0, 2, 1, 4, 7], [3, 5, 4, 2, 6, 0, 1, 7]),
    ([5, 7, 3, 1, 4, 6, 2, 0], [7, 3, 6, 2, 4, 0, 5, 1])]

private def perms4P2 : List (List ℕ × List ℕ) :=
  [([6, 1, 0, 7, 3, 4, 5, 2], [2, 1, 7, 4, 5, 6, 0, 3]),
    ([6, 2, 0, 4, 5, 1, 3, 7], [2, 5, 1, 6, 3, 4, 0, 7]),
    ([6, 4, 0, 2, 7, 5, 1, 3], [2, 6, 3, 7, 1, 5, 0, 4]),
    ([6, 5, 0, 3, 1, 2, 7, 4], [2, 4, 5, 3, 7, 1, 0, 6]),
    ([7, 0, 1, 6, 2, 5, 4, 3], [1, 2, 4, 7, 6, 5, 3, 0]),
    ([7, 3, 1, 5, 4, 0, 2, 6], [5, 2, 6, 1, 4, 3, 7, 0]),
    ([7, 4, 1, 2, 0, 3, 6, 5], [4, 2, 3, 5, 1, 7, 6, 0]),
    ([7, 5, 1, 3, 6, 4, 0, 2], [6, 2, 7, 3, 5, 1, 4, 0])]

private theorem chk1_P2 :
    FilterN.filterN g4P2 dataP2.rels (dataP2.candsF.map Prod.fst) perms1P2 masksN = true := by
  decide +kernel

private theorem chk2_P2 :
    FilterN.filterN g4P2 dataP2.rels (dataP2.candsF.map Prod.fst) perms2P2 masksN = true := by
  decide +kernel

private theorem chk3_P2 :
    FilterN.filterN g4P2 dataP2.rels (dataP2.candsF.map Prod.fst) perms3P2 masksN = true := by
  decide +kernel

private theorem chk4_P2 :
    FilterN.filterN g4P2 dataP2.rels (dataP2.candsF.map Prod.fst) perms4P2 masksN = true := by
  decide +kernel

private theorem hg_P2 : [ofWr dataP2.a, ofWr dataP2.b, ofWr dataP2.c, ofWr dataP2.d] =
    g4P2.map fun x => FilterN.decP x.1 x.2 := by
  decide +kernel

private theorem hp_P2 : dataP2.goodPerms.map
    (fun g => ((ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q)) =
      perms1P2 ++ perms2P2 ++ perms3P2 ++ perms4P2 := by
  decide +kernel

private theorem hwp_P2 : ∀ pq ∈ perms1P2 ++ perms2P2 ++ perms3P2 ++ perms4P2,
    pq.1.length = 8 ∧ (∀ a ∈ pq.1, a < 8) ∧ pq.2.length = 8 ∧ ∀ a ∈ pq.2, a < 8 := by
  decide +kernel

private theorem hwm_P2 : ∀ l ∈ masksN, l.length = 8 ∧ ∀ a ∈ l, a < 2 := by
  decide +kernel

theorem filter_ok_P2 : ∀ g ∈ dataP2.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ dataP2.rels, eqPF (evalF (dataP2.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r)
      oneF) →
      ∃ e ∈ dataP2.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ :=
  FilterN.filter_ok_of dataP2 g4P2 (perms1P2 ++ perms2P2 ++ perms3P2 ++ perms4P2)
    hg_P2 hp_P2 hwp_P2 hwm_P2
    (by rw [FilterN.filterN_append, FilterN.filterN_append, FilterN.filterN_append,
      chk1_P2, chk2_P2, chk3_P2, chk4_P2]; rfl)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
