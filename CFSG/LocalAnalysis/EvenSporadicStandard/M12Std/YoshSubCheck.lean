module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFusionCheck

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def tenum (gens : Array Table) : Array Table := (mulClosureS 16 16 gens 4000).1

@[expose] def tsubOK (gens : Array Table) (size : ℕ) : Bool :=
  enumOK 16 16 gens (mulClosureS 16 16 gens 4000) size

@[expose] def nwT (α k : ℕ) (W : List Int) : Table := nT α k (swN W)

@[expose] def wgens (α k : ℕ) (Ws : List (List Int)) : Array Table := (Ws.map (nwT α k)).toArray


noncomputable abbrev tsub (gens : Array Table) : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (tp 16 '' {x | x ∈ gens})

theorem tsub_spec {gens : Array Table} {size : ℕ} (h : tsubOK gens size = true) :
    EnumSpec 16 gens (tenum gens) ∧ (tenum gens).size = size :=
  enumOK_spec (by norm_num) h

theorem card_tsub {gens : Array Table} {size : ℕ} (h : tsubOK gens size = true) :
    Nat.card (tsub gens) = size := by
  obtain ⟨hs, hsz⟩ := tsub_spec h
  rw [hs.card, hsz]

theorem tp_eq_of_rep {T : Table} {g : Equiv.Perm (Fin 16)} (hp : permOK 16 T = true)
    (hT : Rep 16 T g) : tp 16 T = g :=
  rep_unique (rep_tp hp) hT

theorem tsub_le_of_rep {gens : Array Table} {K : Subgroup (Equiv.Perm (Fin 16))}
    (hperm : ∀ T ∈ gens, permOK 16 T = true) (h : ∀ T ∈ gens, ∃ g ∈ K, Rep 16 T g) :
    tsub gens ≤ K := by
  rw [Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨g, hg, hrep⟩ := h T hT
  rw [tp_eq_of_rep (hperm T hT) hrep]
  exact hg

theorem mem_wgens {α k : ℕ} {Ws : List (List Int)} {T : Table} :
    T ∈ wgens α k Ws ↔ ∃ W ∈ Ws, nwT α k W = T := by
  unfold wgens
  rw [List.mem_toArray, List.mem_map]


@[expose] def eWords : List (List Int) := [[1], [2], [3], [4], [5], [6]]

@[expose] def sWords : List (List Int) := [[1], [2], [3], [4], [5], [6], [7], [-8, 7, 8], [9]]

@[expose] def cWord : List Int := [1, 1]

@[expose] def eWord : List Int := [6]

@[expose] def ueEnumCheck (gE gS : Array Table) (cT : Table) (LE LS : Array Table) : Bool :=
  let lE := LE.toList
  let lS := LS.toList
  let Y := lS.filter fun y => !memTab 16 lE y && sqIn 16 cT y
  let Ys := Y.map fun y => (y, lE.map fun x => commIn 16 cT x y)
  gE.all (memTab 16 lS) &&
  lS.all (fun s => gE.all fun g => memTab 16 lE (conjT 16 s g)) &&
  memTab 16 lE cT &&
  lE.all (sqIn 16 cT) &&
  lE.all (fun a => lE.all fun b => commIn 16 cT a b) &&
  gS.any (fun a => gS.any fun b => !memTab 16 lE (commutatorT 16 a b)) &&
  Y.all (fun y => decide ((lE.filter fun x => commIn 16 cT x y).length ≤ 32)) &&
  Ys.all (fun p => Ys.all fun q => p.2 != q.2 || memTab 16 lE (compT 16 (invT 16 p.1) q.1))

@[expose] def ueCheckG (gE gS : Array Table) (cT : Table) : Bool :=
  tsubOK gE 128 && tsubOK gS 1024 && ueEnumCheck gE gS cT (tenum gE) (tenum gS)

@[expose] def ueCheck (α k : ℕ) : Bool :=
  ueCheckG (wgens α k eWords) (wgens α k sWords) (nwT α k cWord)

@[expose] def esEnumCheck (gE gS : Array Table) (cT : Table) (LE LS : Array Table)
    (gN : Array Table) : Bool :=
  gS.all (commTT 16 cT) &&
  LS.toList.all (fun y => !gS.all (commTT 16 y) || tblEq 16 y (idT 16) || tblEq 16 y cT) &&
  LE.toList.all (fun y => !gE.all (commTT 16 y) || tblEq 16 y (idT 16) || tblEq 16 y cT) &&
  gN.all (fun T => gE.all fun g => memTab 16 LE.toList (conjT 16 T g))

@[expose] def esCheck (α k : ℕ) : Bool :=
  esEnumCheck (wgens α k eWords) (wgens α k sWords) (nwT α k cWord) (tenum (wgens α k eWords))
    (tenum (wgens α k sWords)) (nGens α k)

end CFSG.EvenSporadicStandard.M12Std.Yosh
