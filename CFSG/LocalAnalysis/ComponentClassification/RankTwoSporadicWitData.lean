module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

section Decode

variable (tk : Array ℕ) (n : ℕ)

@[expose] def rdArrCert (p : ℕ) : ArrCert × ℕ :=
  let m := tk[p]!
  let g := tk[p + 1]!
  let pts := rdList (rdArr tk n) m (p + 2)
  let edges := rdList (fun q => (Array.ofFn (n := g) fun i => tk[q + i.val]!, q + g)) m pts.2
  let par := rdList (fun q => (tk[q]!, q + 1)) m edges.2
  let lab := rdList (fun q => (tk[q]!, q + 1)) m par.2
  (⟨pts.1.toArray, edges.1.toArray, par.1.toArray, lab.1.toArray⟩, lab.2)

structure WitData where
  cS : ArrCert
  wcs : Array (Array ArrCert)
  words : List (List ℕ)

@[expose] def rdWitData : WitData :=
  let s := rdArrCert tk n 0
  let w := rdListC tk (rdListC tk (rdArrCert tk n)) s.2
  let ws := rdListC tk (rdListC tk fun q => (tk[q]!, q + 1)) w.2
  ⟨s.1, (w.1.map List.toArray).toArray, ws.1⟩

end Decode

@[expose] def decodeWit (n : ℕ) (s : String) : WitData := rdWitData (decodeNats s) n

@[expose] def natTokens (w m D : ℕ) : Array ℕ :=
  ((List.range m).map fun i => D / 2 ^ (w * i) % 2 ^ w).toArray

@[expose] def wordG (n : ℕ) (gens : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  prodA n (w.map fun i => gens[i]!)

@[expose] def wordPt (gens : Array (Array ℕ)) (w : List ℕ) (x : ℕ) : ℕ :=
  w.foldr (fun i y => (gens[i]!)[y]!) x

@[expose] def inWords (n : ℕ) (gens : Array (Array ℕ)) (ws : List (List ℕ)) (a : Array ℕ) : Bool :=
  ws.any fun w => w.all (fun i => decide (i < gens.size)) &&
    (List.range n).all fun x => a[x]! == wordPt gens w x

@[expose] def inXL (n : ℕ) (xs : Array (Array ℕ)) (a : Array ℕ) : Bool :=
  xs.toList.any fun x => eqA n a x

@[expose] def xsOK (n : ℕ) (gens xs : Array (Array ℕ)) (ws : List (List ℕ)) : Bool :=
  (List.range xs.size).all fun k => (ws.getD k []).all (fun i => decide (i < gens.size)) &&
    eqA n xs[k]! (wordG n gens (ws.getD k []))

variable {n : ℕ} {gens : Array (Array ℕ)}

theorem wordPt_eq (w : List ℕ) {x : ℕ} (hx : x < n) :
    wordPt gens w x = (wordG n gens w)[x]! := by
  induction w with
  | nil =>
    change x = (idA n)[x]!
    rw [idA_get hx]
  | cons i w ih =>
    change (gens[i]!)[wordPt gens w x]! = (compA n gens[i]! (wordG n gens w))[x]!
    rw [compA_get hx, ih]

theorem mem_closure_of_inWords {ws : List (List ℕ)}
    (hg : (allLt gens.size fun k => validA n gens[k]!) = true) {a : Array ℕ}
    (hv : validA n a = true) (h : inWords n gens ws a = true) :
    permOfArr n a ∈ closure (permsA n gens) := by
  simp only [inWords, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_range, beq_iff_eq] at h
  obtain ⟨w, -, hw, hpt⟩ := h
  have he : eqA n a (wordG n gens w) = true := by
    rw [eqA, allLt_iff]
    intro x hx
    rw [beq_iff_eq, ← wordPt_eq w hx]
    exact hpt x hx
  obtain ⟨g, hg', hr⟩ := rep_prodA (H := closure (permsA n gens))
    (l := w.map fun i => gens[i]!) (by
      intro b hb
      rw [List.mem_map] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact ⟨_, subset_closure (mem_permsA (hw i hi)),
        rep_of_validA (allLt_spec hg (hw i hi))⟩)
  rw [eq_of_eqA (rep_of_validA hv) hr he]
  exact hg'

theorem mem_closure_of_inXL {xs : Array (Array ℕ)} {ws : List (List ℕ)}
    (hg : (allLt gens.size fun k => validA n gens[k]!) = true) (hxs : xsOK n gens xs ws = true)
    {a : Array ℕ} (hv : validA n a = true) (h : inXL n xs a = true) :
    permOfArr n a ∈ closure (permsA n gens) := by
  simp only [inXL, List.any_eq_true] at h
  obtain ⟨x, hx, he⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < xs.size := by simpa using hk
  have hok := List.all_eq_true.1 hxs k (List.mem_range.2 hk')
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hw, hxe⟩ := hok
  obtain ⟨g, hg', hr⟩ := rep_prodA (H := closure (permsA n gens))
    (l := (ws.getD k []).map fun i => gens[i]!) (by
      intro b hb
      rw [List.mem_map] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact ⟨_, subset_closure (mem_permsA (hw i hi)),
        rep_of_validA (allLt_spec hg (hw i hi))⟩)
  have hxk : xs.toList[k] = xs[k]! := by
    rw [Array.getElem_toList, getElem!_pos xs k hk']
  rw [hxk] at he
  have hra := rep_of_validA hv
  have hrx : Rep n xs[k]! (permOfArr n a) := fun x => by
    have := allLt_spec he x.2
    rw [beq_iff_eq] at this
    rw [← this]
    exact hra x
  rw [eq_of_eqA hrx hr hxe]
  exact hg'

end CFSG.ComponentClassification.RankTwoSporadic.Cert
