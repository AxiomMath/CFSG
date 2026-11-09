module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FilterN

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

private def g4P3 : List (ℕ × ℕ) :=
  [(17, 267069840090634), (65, 257867905664908), (130, 206444460491416), (10, 132828985085608)]

private def perms1P3 : List (List ℕ × List ℕ) :=
  [([0, 2, 6, 4, 1, 3, 7, 5], [0, 4, 1, 5, 3, 7, 2, 6]),
    ([0, 3, 6, 5, 7, 4, 1, 2], [0, 6, 7, 1, 5, 3, 2, 4]),
    ([0, 4, 6, 2, 3, 7, 5, 1], [0, 7, 3, 4, 1, 6, 2, 5]),
    ([0, 7, 6, 1, 5, 2, 3, 4], [0, 3, 5, 6, 7, 4, 2, 1]),
    ([1, 2, 7, 4, 6, 5, 0, 3], [6, 0, 1, 7, 3, 5, 4, 2]),
    ([1, 3, 7, 5, 0, 2, 6, 4], [4, 0, 5, 1, 7, 3, 6, 2]),
    ([1, 5, 7, 3, 2, 6, 4, 0], [7, 0, 4, 3, 6, 1, 5, 2]),
    ([1, 6, 7, 0, 4, 3, 2, 5], [3, 0, 6, 5, 4, 7, 1, 2])]

private def perms2P3 : List (List ℕ × List ℕ) :=
  [([2, 0, 4, 6, 3, 1, 5, 7], [1, 5, 0, 4, 2, 6, 3, 7]),
    ([2, 1, 4, 7, 5, 6, 3, 0], [7, 1, 0, 6, 2, 4, 5, 3]),
    ([2, 5, 4, 3, 7, 0, 1, 6], [5, 6, 0, 3, 2, 1, 7, 4]),
    ([2, 6, 4, 0, 1, 5, 7, 3], [3, 4, 0, 7, 2, 5, 1, 6]),
    ([3, 0, 5, 6, 4, 7, 2, 1], [1, 7, 6, 0, 4, 2, 3, 5]),
    ([3, 1, 5, 7, 2, 0, 4, 6], [5, 1, 4, 0, 6, 2, 7, 3]),
    ([3, 4, 5, 2, 6, 1, 0, 7], [6, 5, 3, 0, 1, 2, 4, 7]),
    ([3, 7, 5, 1, 0, 4, 6, 2], [4, 3, 7, 0, 5, 2, 6, 1])]

private def perms3P3 : List (List ℕ × List ℕ) :=
  [([4, 0, 2, 6, 7, 3, 1, 5], [1, 6, 2, 5, 0, 7, 3, 4]),
    ([4, 3, 2, 5, 1, 6, 7, 0], [7, 4, 2, 1, 0, 3, 5, 6]),
    ([4, 6, 2, 0, 5, 7, 3, 1], [3, 7, 2, 6, 0, 4, 1, 5]),
    ([4, 7, 2, 1, 3, 0, 5, 6], [5, 3, 2, 4, 0, 6, 7, 1]),
    ([5, 1, 3, 7, 6, 2, 0, 4], [6, 1, 5, 2, 7, 0, 4, 3]),
    ([5, 2, 3, 4, 0, 7, 6, 1], [4, 7, 1, 2, 3, 0, 6, 5]),
    ([5, 6, 3, 0, 2, 1, 4, 7], [3, 5, 4, 2, 6, 0, 1, 7]),
    ([5, 7, 3, 1, 4, 6, 2, 0], [7, 3, 6, 2, 4, 0, 5, 1])]

private def perms4P3 : List (List ℕ × List ℕ) :=
  [([6, 1, 0, 7, 3, 4, 5, 2], [2, 1, 7, 4, 5, 6, 0, 3]),
    ([6, 2, 0, 4, 5, 1, 3, 7], [2, 5, 1, 6, 3, 4, 0, 7]),
    ([6, 4, 0, 2, 7, 5, 1, 3], [2, 6, 3, 7, 1, 5, 0, 4]),
    ([6, 5, 0, 3, 1, 2, 7, 4], [2, 4, 5, 3, 7, 1, 0, 6]),
    ([7, 0, 1, 6, 2, 5, 4, 3], [1, 2, 4, 7, 6, 5, 3, 0]),
    ([7, 3, 1, 5, 4, 0, 2, 6], [5, 2, 6, 1, 4, 3, 7, 0]),
    ([7, 4, 1, 2, 0, 3, 6, 5], [4, 2, 3, 5, 1, 7, 6, 0]),
    ([7, 5, 1, 3, 6, 4, 0, 2], [6, 2, 7, 3, 5, 1, 4, 0])]

private theorem chk1_P3 :
    FilterN.filterN g4P3 dataP3.rels (dataP3.candsF.map Prod.fst) perms1P3 masksN = true := by
  decide +kernel

private theorem chk2_P3 :
    FilterN.filterN g4P3 dataP3.rels (dataP3.candsF.map Prod.fst) perms2P3 masksN = true := by
  decide +kernel

private theorem chk3_P3 :
    FilterN.filterN g4P3 dataP3.rels (dataP3.candsF.map Prod.fst) perms3P3 masksN = true := by
  decide +kernel

private theorem chk4_P3 :
    FilterN.filterN g4P3 dataP3.rels (dataP3.candsF.map Prod.fst) perms4P3 masksN = true := by
  decide +kernel

private theorem hg_P3 : [ofWr dataP3.a, ofWr dataP3.b, ofWr dataP3.c, ofWr dataP3.d] =
    g4P3.map fun x => FilterN.decP x.1 x.2 := by
  decide +kernel

private theorem hp_P3 : dataP3.goodPerms.map
    (fun g => ((ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q)) =
      perms1P3 ++ perms2P3 ++ perms3P3 ++ perms4P3 := by
  decide +kernel

private theorem hwp_P3 : ∀ pq ∈ perms1P3 ++ perms2P3 ++ perms3P3 ++ perms4P3,
    pq.1.length = 8 ∧ (∀ a ∈ pq.1, a < 8) ∧ pq.2.length = 8 ∧ ∀ a ∈ pq.2, a < 8 := by
  decide +kernel

private theorem hwm_P3 : ∀ l ∈ masksN, l.length = 8 ∧ ∀ a ∈ l, a < 2 := by
  decide +kernel

theorem filter_ok_P3 : ∀ g ∈ dataP3.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ dataP3.rels, eqPF (evalF (dataP3.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r)
      oneF) →
      ∃ e ∈ dataP3.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ :=
  FilterN.filter_ok_of dataP3 g4P3 (perms1P3 ++ perms2P3 ++ perms3P3 ++ perms4P3)
    hg_P3 hp_P3 hwp_P3 hwm_P3
    (by rw [FilterN.filterN_append, FilterN.filterN_append, FilterN.filterN_append,
      chk1_P3, chk2_P3, chk3_P3, chk4_P3]; rfl)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
