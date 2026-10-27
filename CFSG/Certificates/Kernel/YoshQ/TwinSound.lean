module

public import Certificates.Data.Kernel.YoshQ.Twin
public import CFSG.Certificates.Kernel.YoshQ.TabNSound

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b

structure Dims (n w : Nat) : Prop where
  w_pos : 0 < w
  w_le : w ≤ 32
  n_lt : n < 16777216
  n_succ : n + 1 < 2 ^ w

theorem Dims.n_lt32 {n w : Nat} (d : Dims n w) : n < 2 ^ 32 :=
  Nat.lt_trans d.n_lt (by decide)

theorem Dims.n_le {n w : Nat} (d : Dims n w) : n ≤ 2 ^ w := by
  have := d.n_succ
  omega

variable {n w : Nat}

theorem compT_tabN' (d : Dims n w) (x y : Nat) :
    compT n (tabN n w x) (tabN n w y) = tabN n w (pmN n w x y) :=
  compT_tabN d.w_le d.n_lt32 x y

theorem tblEq_tabN' (d : Dims n w) (x y : Nat) :
    tblEq n (tabN n w x) (tabN n w y) = eqN n w x y :=
  tblEq_tabN d.w_pos d.w_le x y

theorem invT_tabN' (d : Dims n w) (x : Nat) : invT n (tabN n w x) = tabN n w (invN n w x) :=
  invT_tabN d.w_le d.n_le x

theorem idT_tabN' (d : Dims n w) : idT n = tabN n w (pidn n w) :=
  idT_tabN d.n_lt d.n_succ d.w_le

theorem conjT_tabN (d : Dims n w) (m t : Nat) :
    CFSG.EvenSporadicStandard.M12Std.Yosh.conjT n (tabN n w m) (tabN n w t) =
      tabN n w (cjN n w m t) := by
  unfold CFSG.EvenSporadicStandard.M12Std.Yosh.conjT cjN
  rw [compT_tabN' d, invT_tabN' d, compT_tabN' d]

theorem commutatorT_tabN (d : Dims n w) (a b : Nat) :
    commutatorT n (tabN n w a) (tabN n w b) = tabN n w (comN n w a b) := by
  unfold commutatorT comN
  rw [compT_tabN' d, invT_tabN' d, invT_tabN' d, compT_tabN' d, compT_tabN' d]

theorem commTT_tabN (d : Dims n w) (x y : Nat) :
    commTT n (tabN n w x) (tabN n w y) = ctN n w x y := by
  unfold commTT ctN
  rw [compT_tabN' d, compT_tabN' d, tblEq_tabN' d]

theorem memTab_tabN (d : Dims n w) (L : List Nat) (t : Nat) :
    memTab n (L.map (tabN n w)) (tabN n w t) = memN n w L t := by
  unfold memTab memN
  rw [List.any_map]
  congr 1
  funext s
  simp only [Function.comp, tblEq_tabN' d]

theorem commIn_tabN (d : Dims n w) (c a b : Nat) :
    commIn n (tabN n w c) (tabN n w a) (tabN n w b) = commInN n w c a b := by
  unfold commIn commInN
  rw [commutatorT_tabN d, idT_tabN' d, tblEq_tabN' d, tblEq_tabN' d]

theorem sqIn_tabN (d : Dims n w) (c a : Nat) :
    sqIn n (tabN n w c) (tabN n w a) = sqInN n w c a := by
  unfold sqIn sqInN
  rw [compT_tabN' d, idT_tabN' d, tblEq_tabN' d, tblEq_tabN' d]

theorem invoOK_tabN (d : Dims n w) (x : Nat) :
    CFSG.Sporadic.Th.Native.invoOK n (tabN n w x) = invoN n w x := by
  unfold CFSG.Sporadic.Th.Native.invoOK invoN apN
  simp only [ap_tabN d.w_le]

theorem involOK_tabN (d : Dims n w) (x : Nat) : involOK n (tabN n w x) = involN n w x := by
  unfold involOK involN
  rw [invoOK_tabN d, idT_tabN' d, tblEq_tabN' d]

theorem evalT_tabN (d : Dims n w) {m : Nat} {T Ti : Fin m → Table} {G Gi : Fin m → Nat}
    (hT : ∀ i, T i = tabN n w (G i)) (hTi : ∀ i, Ti i = tabN n w (Gi i)) :
    ∀ wd : List (Fin m × Bool), evalT n T Ti wd = tabN n w (evalN n w G Gi wd)
  | [] => idT_tabN' d
  | (i, b) :: wd => by
    have ih := evalT_tabN d hT hTi wd
    have e1 : evalT n T Ti ((i, b) :: wd) = compT n (letterT T Ti (i, b)) (evalT n T Ti wd) := rfl
    have e2 : evalN n w G Gi ((i, b) :: wd) = pmN n w (letterN G Gi (i, b)) (evalN n w G Gi wd) :=
      rfl
    rw [e1, e2, ih]
    cases b
    · rw [show letterT T Ti (i, false) = Ti i from rfl, hTi, compT_tabN' d]
      rfl
    · rw [show letterT T Ti (i, true) = T i from rfl, hT, compT_tabN' d]
      rfl

theorem getElem!_map_tabN {GS : List Nat} {j : Nat} (hj : j < GS.length) :
    ((GS.map (tabN n w)).toArray)[j]! = tabN n w (GS.getD j 0) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getElem?_eq_getElem hj]

theorem getElem!_map_invT_tabN (d : Dims n w) {GS : List Nat} {j : Nat} (hj : j < GS.length) :
    (((GS.map (tabN n w)).toArray).map (invT n))[j]! = tabN n w (invN n w (GS.getD j 0)) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [Array.getElem_map]
  rw [← getElem!_pos _ j (by simpa using hj), getElem!_map_tabN hj, invT_tabN' d]

theorem modelT_tabN (d : Dims n w) {k : Nat} {GS : List Nat} (hk : k ≤ GS.length)
    (wd : List (Fin k × Bool)) :
    modelT n k ((GS.map (tabN n w)).toArray) wd = tabN n w (modelTN n w k GS wd) := by
  unfold modelT modelTN
  exact evalT_tabN d (fun i => getElem!_map_tabN (by omega))
    (fun i => getElem!_map_invT_tabN d (by omega)) wd

theorem dims16 : Dims 16 5 := ⟨by decide, by decide, by decide, by decide⟩

theorem toList_map_tabN (L : List Nat) : ((L.map (tabN n w)).toArray).toList = L.map (tabN n w) :=
  rfl

structure NData (α k : Nat) (GS NL : List Nat) : Prop where
  gens : nGens α k = (GS.map (tabN 16 5)).toArray
  len : GS.length = 9
  enum : nEnum α k = (NL.map (tabN 16 5)).toArray

section NModel

variable {α k : Nat} {GS NL : List Nat}

theorem NData.nT_eq (h : NData α k GS NL) (wd : List (Fin 9 × Bool)) :
    nT α k wd = tabN 16 5 (nTN GS wd) := by
  unfold nT nTN
  rw [h.gens]
  exact modelT_tabN dims16 (by rw [h.len]) wd

theorem NData.nwT_eq (h : NData α k GS NL) (W : List Int) :
    nwT α k W = tabN 16 5 (nTN GS (swN W)) := h.nT_eq _

theorem NData.wgens_eq (h : NData α k GS NL) (Ws : List (List Int)) :
    wgens α k Ws = ((Ws.map fun W => nTN GS (swN W)).map (tabN 16 5)).toArray := by
  unfold wgens
  have e : nwT α k = fun W => tabN 16 5 (nTN GS (swN W)) := funext h.nwT_eq
  rw [e, List.map_map]
  rfl

theorem NData.conjugatesTo_eq (h : NData α k GS NL) (a b : Nat) :
    conjugatesTo α k (tabN 16 5 a) (tabN 16 5 b) = conjToN NL a b := by
  unfold conjugatesTo conjToN
  rw [h.enum, List.any_toArray, List.any_map]
  congr 1
  funext m
  simp only [Function.comp, conjT_tabN dims16, tblEq_tabN' dims16]

theorem NData.chainRun_eq (h : NData α k GS NL) :
    ∀ (wd : List (Fin 9 × Bool)) (cs : List (List Int × Bool)),
      chainRun α k wd cs = chainRunN GS NL α wd cs
  | _, [] => rfl
  | wd, (W, dir) :: rest => by
    simp only [chainRun, chainRunN]
    rw [h.nT_eq, h.nT_eq, h.conjugatesTo_eq, h.chainRun_eq _ rest]

theorem NData.isSqN_eq (h : NData α k GS NL) (t : Nat) :
    isSqN α k (tabN 16 5 t) = isSqNN NL t := by
  unfold isSqN isSqNN
  rw [h.enum, List.any_toArray, List.any_map]
  congr 1
  funext z
  simp only [Function.comp, compT_tabN' dims16, tblEq_tabN' dims16]

theorem filter_map_tabN (p : Table → Bool) (L : List Nat) :
    (L.map (tabN n w)).filter p = (L.filter (p ∘ tabN n w)).map (tabN n w) :=
  List.filter_map

theorem NData.isCommN_eq (h : NData α k GS NL) (t : Nat) :
    isCommN α k (tabN 16 5 t) = isCommNN NL t := by
  unfold isCommN isCommNN
  rw [h.enum, List.filter_toArray, List.any_toArray, filter_map_tabN, List.any_map]
  have e : (commTT 16 (tabN 16 5 t) ∘ tabN 16 5) = ctN 16 5 t := by
    funext x
    simp only [Function.comp, commTT_tabN dims16]
  rw [e]
  simp only [Function.comp_def, List.any_toArray, List.any_map, commutatorT_tabN dims16,
    tblEq_tabN' dims16]

theorem NData.witnessOK_eq (h : NData α k GS NL) (t : Nat) :
    witnessOK α k (tabN 16 5 t) = witnessNN NL t := by
  unfold witnessOK witnessNN
  rw [h.isSqN_eq, h.isCommN_eq]

theorem NData.goodReps_eq (h : NData α k GS NL) : goodReps α k = goodRepsN GS NL α k := by
  unfold goodReps goodRepsN
  simp only [h.chainRun_eq]

theorem NData.badReps_eq (h : NData α k GS NL) : badReps α k = badRepsN GS NL α k := by
  unfold badReps badRepsN
  simp only [h.chainRun_eq]

theorem NData.classTabs_eq (h : NData α k GS NL) (t : Nat) :
    classTabs α k (tabN 16 5 t) = (classN NL t).map (tabN 16 5) := by
  unfold classTabs classN
  rw [h.enum, toList_map_tabN]
  simp only [List.map_map, Function.comp_def, conjT_tabN dims16]

theorem NData.goodTabs_eq (h : NData α k GS NL) :
    goodTabs α k = (goodTabsN GS NL α k).map (tabN 16 5) := by
  unfold goodTabs goodTabsN
  rw [h.goodReps_eq, List.map_flatMap]
  congr 1
  funext wd
  rw [h.nT_eq, h.classTabs_eq]

theorem NData.badTabs_eq (h : NData α k GS NL) :
    badTabs α k = (badTabsN GS NL α k).map (tabN 16 5) := by
  unfold badTabs badTabsN
  rw [h.badReps_eq, List.map_flatMap]
  congr 1
  funext wd
  rw [h.nT_eq, h.classTabs_eq]

theorem NData.fusionChainsCheck_eq (h : NData α k GS NL) :
    fusionChainsCheck α k = fusionChainsN GS NL α k := by
  unfold fusionChainsCheck fusionChainsN
  simp only [h.chainRun_eq, h.nT_eq, h.witnessOK_eq]

theorem NData.fusionCoverCheck_eq (h : NData α k GS NL) :
    fusionCoverCheck α k = fusionCoverN GS NL α k := by
  unfold fusionCoverCheck fusionCoverN
  simp only [h.enum, toList_map_tabN, h.goodTabs_eq, h.badTabs_eq, List.all_map,
    filter_map_tabN, List.length_map, Function.comp_def, involOK_tabN dims16, memTab_tabN dims16]

end NModel

theorem all_map_tabN (p : Table → Bool) (L : List Nat) :
    (L.map (tabN n w)).all p = L.all fun x => p (tabN n w x) := by
  rw [List.all_map, Function.comp_def]

theorem any_map_tabN (p : Table → Bool) (L : List Nat) :
    (L.map (tabN n w)).any p = L.any fun x => p (tabN n w x) := by
  rw [List.any_map, Function.comp_def]

theorem filter_map_tabN' (p : Table → Bool) (L : List Nat) :
    (L.map (tabN n w)).filter p = (L.filter fun x => p (tabN n w x)).map (tabN n w) := by
  rw [List.filter_map, Function.comp_def]

theorem normCenRest_eq (d : Dims n w) (G GE L LE : List Nat) (c : Nat) :
    ((((((LE.map (tabN n w)).toArray.any (fun y => tblEq n (tabN n w c) y) &&
      (GE.map (tabN n w)).toArray.all (fun x => (G.map (tabN n w)).toArray.any
        (fun x' => tblEq n x x'))) &&
      (G.map (tabN n w)).toArray.all (fun m' => (LE.map (tabN n w)).toArray.all (fun y =>
        (LE.map (tabN n w)).toArray.any (fun y' => tblEq n (compT n m' y) (compT n y' m')) &&
          (LE.map (tabN n w)).toArray.any
            (fun y'' => tblEq n (compT n y m') (compT n m' y''))))) &&
      (L.map (tabN n w)).toArray.all (fun T => !((GE.map (tabN n w)).toArray.all
        (fun y => commTT n T y)) || (LE.map (tabN n w)).toArray.any (fun y => tblEq n T y))) &&
      (LE.map (tabN n w)).toArray.all (fun T => !((GE.map (tabN n w)).toArray.all
        (fun y => commTT n T y)) || tblEq n T (idT n) || tblEq n T (tabN n w c)))) =
      normCenRestN n w G GE L LE c := by
  unfold normCenRestN
  simp only [List.any_toArray, List.all_toArray, all_map_tabN, any_map_tabN, tblEq_tabN' d,
    compT_tabN' d, commTT_tabN d, idT_tabN' d]

theorem ueEnumCheck_eq (GE GS : List Nat) (c : Nat) (lE lS : List Nat) :
    ueEnumCheck (GE.map (tabN 16 5)).toArray (GS.map (tabN 16 5)).toArray (tabN 16 5 c)
      (lE.map (tabN 16 5)).toArray (lS.map (tabN 16 5)).toArray = ueN GE GS c lE lS := by
  unfold ueEnumCheck ueN
  simp only [toList_map_tabN, List.any_toArray, List.all_toArray, all_map_tabN, any_map_tabN,
    filter_map_tabN', memTab_tabN dims16, CFSG.EvenSporadicStandard.M12Std.Yosh.conjT,
    conjT_tabN dims16, sqIn_tabN dims16, commIn_tabN dims16, commutatorT_tabN dims16,
    List.map_map, Function.comp_def, compT_tabN' dims16, invT_tabN' dims16, List.all_map,
    List.length_map, cjN]

theorem esEnumCheck_eq (GE GS : List Nat) (c : Nat) (lE lS GN : List Nat) :
    esEnumCheck (GE.map (tabN 16 5)).toArray (GS.map (tabN 16 5)).toArray (tabN 16 5 c)
      (lE.map (tabN 16 5)).toArray (lS.map (tabN 16 5)).toArray (GN.map (tabN 16 5)).toArray =
      esN GE GS c lE lS GN := by
  unfold esEnumCheck esN
  simp only [toList_map_tabN, List.any_toArray, List.all_toArray, all_map_tabN, any_map_tabN,
    memTab_tabN dims16, conjT_tabN dims16, commTT_tabN dims16, tblEq_tabN' dims16,
    idT_tabN' dims16]

theorem conjIn_eq (NL : List Nat) (a b : Nat) :
    conjIn (NL.map (tabN 16 5)).toArray (tabN 16 5 a) (tabN 16 5 b) = conjToN NL a b := by
  unfold conjIn conjToN
  simp only [List.any_toArray, any_map_tabN, conjT_tabN dims16, tblEq_tabN' dims16]

theorem l6Core_eq (NL good : List Nat) (e : Nat) (LE : List Nat) :
    l6Core (NL.map (tabN 16 5)).toArray (good.map (tabN 16 5)) (tabN 16 5 e) (LE.map (tabN 16 5)) =
      l6N NL good e LE := by
  unfold l6Core l6N
  simp only [toList_map_tabN, any_map_tabN, all_map_tabN, filter_map_tabN', List.length_map,
    commTT_tabN dims16, memTab_tabN dims16, conjIn_eq]

theorem l7Fusion_eq (NL good : List Nat) (e u : Nat) (LE : List Nat)
    (ht : tsubOK (((LE.filter (memN 16 5 good)).map (tabN 16 5)).toArray) 128 = true) :
    l7Fusion (NL.map (tabN 16 5)).toArray (good.map (tabN 16 5)) (tabN 16 5 e) (tabN 16 5 u)
      (LE.map (tabN 16 5)) = l7FusionN NL good e u LE := by
  unfold l7Fusion l7FusionN
  simp only [toList_map_tabN, any_map_tabN, all_map_tabN, filter_map_tabN', List.length_map,
    commTT_tabN dims16, memTab_tabN dims16, conjIn_eq, compT_tabN' dims16, ht, Bool.and_true]

theorem l7Sylow_eq (c e u : Nat) (LE LS : List Nat) :
    l7Sylow (tabN 16 5 c) (tabN 16 5 e) (tabN 16 5 u) (LE.map (tabN 16 5)) (LS.map (tabN 16 5)) =
      l7SylowN c e u LE LS := by
  unfold l7Sylow l7SylowN
  simp only [any_map_tabN, all_map_tabN, filter_map_tabN', List.length_map, commTT_tabN dims16,
    memTab_tabN dims16, compT_tabN' dims16, tblEq_tabN' dims16, idT_tabN' dims16,
    sqIn_tabN dims16, commIn_tabN dims16, List.all_cons, List.all_nil]

theorem l7A_eq (bad : List Nat) (c : Nat) (GA LA LE LS : List Nat)
    (hA : tenum (GA.map (tabN 16 5)).toArray = (LA.map (tabN 16 5)).toArray)
    (ht : tsubOK (GA.map (tabN 16 5)).toArray 16 = true) :
    l7A (bad.map (tabN 16 5)) (tabN 16 5 c) (GA.map (tabN 16 5)).toArray (LE.map (tabN 16 5))
      (LS.map (tabN 16 5)) = l7AN bad c GA LA LE LS := by
  unfold l7A l7AN
  rw [hA, ht]
  simp only [toList_map_tabN, List.any_toArray, List.all_toArray, any_map_tabN, all_map_tabN,
    commTT_tabN dims16, memTab_tabN dims16, compT_tabN' dims16, tblEq_tabN' dims16,
    idT_tabN' dims16, commIn_tabN dims16, Bool.true_and]

theorem l7V_eq (NL GV : List Nat) :
    l7V (NL.map (tabN 16 5)).toArray (GV.map (tabN 16 5)).toArray = l7VN NL GV := by
  unfold l7V l7VN
  simp only [List.all_toArray, all_map_tabN, commTT_tabN dims16, compT_tabN' dims16,
    tblEq_tabN' dims16, idT_tabN' dims16]

theorem l8Fact_eq (NL : List Nat) (e : Nat) :
    l8Fact (NL.map (tabN 16 5)).toArray (tabN 16 5 e) = l8FactN NL e := by
  unfold l8Fact l8FactN
  simp only [toList_map_tabN, any_map_tabN, all_map_tabN, filter_map_tabN', List.length_map,
    commTT_tabN dims16, compT_tabN' dims16, tblEq_tabN' dims16, idT_tabN' dims16,
    conjT_tabN dims16, memTab, memN, List.any_cons, List.any_nil]

theorem l8ZN_eq (NL : List Nat) (c y0 : Nat) (LE : List Nat) :
    l8ZN (NL.map (tabN 16 5)).toArray (tabN 16 5 c) (tabN 16 5 y0) (LE.map (tabN 16 5)) =
      l8ZNN NL c y0 LE := by
  unfold l8ZN l8ZNN
  simp only [List.all_toArray, all_map_tabN, commIn_tabN dims16, compT_tabN' dims16,
    tblEq_tabN' dims16, idT_tabN' dims16]

end CFSG.KC.YoshQ

end
