module

public import Certificates.Data.Kernel.AE6FN
public import CFSG.Certificates.Kernel.YoshQ.TwinSound
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

namespace CFSG.KC.AE6F

open CFSG.KC.Enum CFSG.KC.YoshQ Certificates.AE6Model CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native Certificates.S7Twin

set_option maxRecDepth 100000

variable {n : Nat}

theorem dims : Dims 360 9 := ⟨by decide, by decide, by decide, by decide⟩

theorem toTable_one (hn : n < 2 ^ 32) : toTable (1 : Equiv.Perm (Fin n)) = idT n :=
  (CFSG.KS.Tbl.toTable_ext hn (by simp [idT]) (Rep.idT hn)).symm

theorem toTable_mul (hn : n < 2 ^ 32) (g h : Equiv.Perm (Fin n)) :
    toTable (g * h) = compT n (toTable g) (toTable h) :=
  (CFSG.KS.Tbl.compT_eq_toTable hn (rep_toTable hn g) (rep_toTable hn h)).symm

theorem toTable_inv (hn : n < 2 ^ 32) (g : Equiv.Perm (Fin n)) :
    toTable g⁻¹ = invT n (toTable g) :=
  (CFSG.KS.Tbl.toTable_ext hn (CFSG.KS.Tbl.invT_size _ _)
    (CFSG.KS.Tbl.invT_rep hn (rep_toTable hn g))).symm

variable {G WL : List Nat}

theorem toTable_aeWord
    (hG : ∀ l, toTable ((curtisPerms ()).getD l 1) = tabN 360 9 (G.getD l (pidn 360 9))) :
    ∀ w : List Nat, toTable (aeWord (curtisPerms ()) w) = tabN 360 9 (awN G w)
  | [] => by
    rw [aeWord, List.map_nil, List.prod_nil, toTable_one (by norm_num), idT_tabN' dims]
    rfl
  | i :: w => by
    have ih := toTable_aeWord hG w
    rw [aeWord, List.map_cons, List.prod_cons, toTable_mul (by norm_num), hG i] at *
    rw [ih, compT_tabN' dims]
    rfl

theorem getD_map_pair {α : Type} (L : List α) (f g : α → Nat) (m a b : Nat) :
    (L.map fun i => (tabN 360 9 (f i), tabN 360 9 (g i))).getD m (tabN 360 9 a, tabN 360 9 b) =
      (tabN 360 9 ((L.map fun i => (f i, g i)).getD m (a, b)).1,
        tabN 360 9 ((L.map fun i => (f i, g i)).getD m (a, b)).2) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases L[m]? <;> rfl

theorem foldl_tabN (F : Nat → Nat) :
    ∀ (w : List Nat) (a : Nat), w.foldl (fun acc k => compT 360 acc (tabN 360 9 (F k)))
      (tabN 360 9 a) = tabN 360 9 (w.foldl (fun acc k => pmN 360 9 acc (F k)) a)
  | [], _ => by rw [List.foldl_nil, List.foldl_nil]
  | k :: w, a => by
    rw [List.foldl_cons, List.foldl_cons, compT_tabN' dims]
    exact foldl_tabN F w _

theorem tableEval_tabN {α : Type} (L : List α) (f g : α → Nat) (w : List Nat) :
    tableEval (L.map fun i => (tabN 360 9 (f i), tabN 360 9 (g i))) w =
      tabN 360 9 (evalHN (L.map fun i => (f i, g i)) w) := by
  unfold tableEval evalHN
  rw [idT_tabN' dims]
  have e : (fun acc k => compT 360 acc (if k % 2 = 0 then
      ((L.map fun i => (tabN 360 9 (f i), tabN 360 9 (g i))).getD (k / 2)
        (tabN 360 9 (pidn 360 9), tabN 360 9 (pidn 360 9))).1 else
      ((L.map fun i => (tabN 360 9 (f i), tabN 360 9 (g i))).getD (k / 2)
        (tabN 360 9 (pidn 360 9), tabN 360 9 (pidn 360 9))).2)) =
      fun acc k => compT 360 acc (tabN 360 9 (if k % 2 = 0 then
        ((L.map fun i => (f i, g i)).getD (k / 2) (pidn 360 9, pidn 360 9)).1 else
        ((L.map fun i => (f i, g i)).getD (k / 2) (pidn 360 9, pidn 360 9)).2)) := by
    funext acc k
    by_cases h : k % 2 = 0 <;> simp only [getD_map_pair, h, ↓reduceIte]
  rw [e, foldl_tabN]

theorem memT_tabN (L : List Nat) (x : Nat) :
    memT 360 (L.map (tabN 360 9)) (tabN 360 9 x) = memN L x := by
  unfold memT memN
  rw [List.any_map]
  congr 1
  funext t
  exact tblEq_tabN' dims x t

structure Gens (G : List Nat) : Prop where
  get : ∀ l, toTable ((curtisPerms ()).getD l 1) = tabN 360 9 (G.getD l (pidn 360 9))
  all : (curtisPerms ()).map toTable = G.map (tabN 360 9)

theorem fBasic_eq (hG : Gens G) : fBasic () = fBasicN G := by
  have hall : ((curtisPerms ()).all fun g => sqOneT 360 (toTable g)) =
      G.all fun g => eqN 360 9 (pmN 360 9 g g) (pidn 360 9) := by
    have e := congrArg (fun L => L.all (sqOneT 360)) hG.all
    simp only [List.all_map, Function.comp_def] at e
    rw [e]
    unfold sqOneT
    simp only [compT_tabN' dims, idT_tabN' dims, tblEq_tabN' dims]
  unfold fBasic fBasicN z0
  simp only [hall, toTable_aeWord hG.get, compT_tabN' dims, idT_tabN' dims, tblEq_tabN' dims]

theorem fTwinChecks_eq (hG : Gens G) : fTwinChecks () = fTwinChecksN G := by
  unfold fTwinChecks fTwinChecksN fTwinPairs fTwinPairsN
  simp only [List.map_map, List.all_map, List.any_map, Function.comp_def,
    toTable_mul (by norm_num : (360 : Nat) < 2 ^ 32), toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_aeWord hG.get, hG.get, spanQ, spanQN, conjT, conjN, memT, memN, List.any_cons,
    List.any_nil, compT_tabN' dims,
    invT_tabN' dims, idT_tabN' dims, tblEq_tabN' dims]

theorem fCycChecks_eq (hG : Gens G) : fCycChecks () = fCycChecksN G := by
  unfold fCycChecks fCycChecksN fCycTabs fCycTabsN fCycs
  simp only [List.map_map, Function.comp_def, toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_aeWord hG.get, hG.get, commT, commN, compT_tabN' dims, invT_tabN' dims,
    idT_tabN' dims, getD_map_pair, tblEq_tabN' dims]

theorem fDiagChecks_eq (hG : Gens G) (hW : allTables (wQ ()) = WL.map (tabN 360 9)) :
    fDiagChecks () = fDiagChecksN G WL := by
  unfold fDiagChecks fDiagChecksN fCycTabs fCycTabsN fCycs diagWordTable z0
  simp only [hW, List.map_map, Function.comp_def,
    toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32), toTable_aeWord hG.get, hG.get,
    compT_tabN' dims, invT_tabN' dims, idT_tabN' dims, getD_map_pair, tableEval_tabN,
    memT_tabN, tblEq_tabN' dims]

end CFSG.KC.AE6F

end
