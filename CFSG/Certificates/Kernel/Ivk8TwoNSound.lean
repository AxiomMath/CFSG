module

public import Certificates.Data.Kernel.Ivk8TwoN
public import CFSG.Certificates.Kernel.YoshQ.TwinSound
public import CFSG.Certificates.Kernel.Misc.RuBaseSound

public section

namespace CFSG.KC.Ivk8N

open CFSG.KC.Enum CFSG.KC.YoshQ Certificates.Ivk8Two CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native Certificates.Odd87F3 Certificates.Ivk8Weak

variable {n w : Nat}

theorem headD_map {α β : Type} (f : α → β) (L : List α) (a : α) :
    (L.map f).headD (f a) = f (L.headD a) := by
  cases L <;> rfl

theorem map_invT_tabN (d : Dims n w) (L : List Nat) :
    (L.map (tabN n w)).map (invT n) = (L.map (invN n w)).map (tabN n w) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun x _ => invT_tabN' d x

theorem evalT_tabN' (d : Dims n w) (gs gis : List Nat) :
    ∀ wd : List Int, evalT n (gs.map (tabN n w)) (gis.map (tabN n w)) wd =
      tabN n w (evalN n w gs gis wd)
  | [] => idT_tabN' d
  | z :: wd => by
    simp only [evalT, evalN]
    rw [evalT_tabN' d gs gis wd, idT_tabN' d, List.getD_map, List.getD_map]
    by_cases hz : 0 < z <;> simp only [hz, ↓reduceIte] <;> exact compT_tabN' d _ _

theorem invOK_eq_tblEq (hn : n < 2 ^ 32) (P R : Table) :
    invOK n P R = tblEq n (compT n R P) (idT n) := by
  unfold invOK tblEq
  apply Bool.eq_iff_iff.2
  rw [CFSG.KC.Misc.RuBase.allIn_iff, CFSG.KC.Misc.RuBase.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have e1 : ap (compT n R P) i = ap R (ap P i) := by
    unfold ap compT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e1, (CFSG.KC.Misc.RuBase.tr_idT hn).2 i hi]

theorem invOK_tabN (d : Dims n w) (x y : Nat) :
    invOK n (tabN n w x) (tabN n w y) = eqN n w (pmN n w y x) (pidn n w) := by
  rw [invOK_eq_tblEq d.n_lt32, compT_tabN' d, idT_tabN' d, tblEq_tabN' d]

theorem subprodsT_tabN (d : Dims n w) :
    ∀ L : List Nat, subprodsT n (L.map (tabN n w)) = (subprodsN n w L).map (tabN n w)
  | [] => by
    simp only [List.map_nil, subprodsT, subprodsN, List.map_cons]
    rw [idT_tabN' d]
  | t :: L => by
    simp only [List.map_cons, subprodsT, subprodsN, List.map_append]
    rw [subprodsT_tabN d L, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => compT_tabN' d t x

theorem allDistinct_tabN (d : Dims n w) :
    ∀ L : List Nat, allDistinct n (L.map (tabN n w)) = allDistinctN n w L
  | [] => rfl
  | t :: L => by
    simp only [List.map_cons, allDistinct, allDistinctN, List.all_map, Function.comp_def,
      tblEq_tabN' d]
    rw [allDistinct_tabN d L]

theorem twoTables_tabN (d : Dims n w) (gs : List Nat) (wa w₁ w₂ w₃ wx wy : List Int) :
    twoTables n (gs.map (tabN n w)) wa w₁ w₂ w₃ wx wy =
      (twoTablesN n w gs wa w₁ w₂ w₃ wx wy).map (tabN n w) := by
  unfold twoTables twoTablesN
  simp only [map_invT_tabN d, evalT_tabN' d, List.map_cons, List.map_nil]

theorem twoProds_tabN (d : Dims n w) (ts : List Nat) :
    twoProds n (ts.map (tabN n w)) = (twoProdsN n w ts).map (tabN n w) := by
  unfold twoProds twoProdsN
  dsimp only
  rw [map_invT_tabN d, ← List.map_take, subprodsT_tabN d, List.flatMap_map, List.map_flatMap,
    List.flatMap_map]
  refine List.flatMap_congr fun a _ => ?_
  rw [evalT_tabN' d, List.map_map, List.map_map]
  exact List.map_congr_left fun x _ => compT_tabN' d _ x

theorem twoOKT_tabN (d : Dims n w) (gs : List Nat) (wa w₁ w₂ w₃ wx wy : List Int) :
    twoOKT n (gs.map (tabN n w)) wa w₁ w₂ w₃ wx wy = twoOKN n w gs wa w₁ w₂ w₃ wx wy := by
  unfold twoOKT twoOKN invOKN
  simp only [twoTables_tabN d, map_invT_tabN d, List.all_map, Function.comp_def, invT_tabN' d,
    invOK_tabN d, evalT_tabN' d, tblEq_tabN' d, idT_tabN' d, headD_map, twoProds_tabN d,
    List.length_map, allDistinct_tabN d]

end CFSG.KC.Ivk8N

end
