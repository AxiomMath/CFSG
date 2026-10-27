module

public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Data.Kernel.M24G.Replay
import CFSG.Certificates.Kernel.M24G.BfsReplaySound
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import CFSG.Certificates.Kernel.M24G.IdxSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem closureNodupOK_of {L : List (Array Nat)} {par gen : List Nat} (h : L.Nodup) :
    Native.closureNodupOK (L.toArray, par.toArray, gen.toArray) = true := by
  unfold Native.closureNodupOK
  exact decide_eq_true h

open scoped CFSG.KC.M24G.FixOctEq

theorem range24_map {β : Type} (f : Nat → β) :
    (Array.range 24).map f = ((List.range 24).map f).toArray := by
  apply Array.toList_inj.1
  simp [Array.toList_range]

theorem get!_nat (x : Array Nat) (i : Nat) : x[i]! = x.toList.getD i 0 := by
  rcases x with ⟨l⟩
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem mulTab_eq (a b : Array Nat) : Native.mulTab a b = mulTabF a b := by
  unfold Native.mulTab mulTabF
  rw [range24_map]
  simp only [get!_nat]

theorem invTab_eq (a : Array Nat) : Native.invTab a = invTabF a := by
  unfold Native.invTab invTabF
  rw [range24_map]
  simp only [get!_nat]

theorem tabKey_eq (t : Array Nat) : Native.tabKey t = tabKeyF t := by
  unfold Native.tabKey tabKeyF
  rw [Array.foldl_toList]

theorem fixOctSteps_eq : Native.fixOctSteps () = fixOctStepsF := by
  unfold Native.fixOctSteps Native.fixOctComms fixOctStepsF
  simp only [List.map_cons, List.map_nil, mulTab_eq]

theorem fixOctCommCheck_eq : Native.fixOctCommCheck () = fixOctCommF := by
  unfold Native.fixOctCommCheck Native.commTab fixOctCommF
  simp only [mulTab_eq, invTab_eq]

theorem size_mulTabF (a b : Array Nat) : (mulTabF a b).size = 24 := by
  simp [mulTabF]

theorem allLt_iff' {n : Nat} {p : Nat → Bool} : Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold Native.allLt
  rw [List.all_eq_true]
  simp only [List.mem_range]

theorem get!_toArray_nat (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem get!_toArray_arr (l : List (Array Nat)) (i : Nat) :
    l.toArray[i]! = l.getD i default := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

variable {L : List (Array Nat)} {par gen : List Nat} {pos : KTree (Nat × Nat)}

theorem fixOctClosure_eq
    (h : replayOK tabKeyF fixOctStepsF Native.fixOctIdTab 11000 L par gen pos = true) :
    Native.fixOctClosure () = (L.toArray, par.toArray, gen.toArray) := by
  unfold Native.fixOctClosure
  have hk : Native.tabKey = tabKeyF := funext tabKey_eq
  rw [hk, fixOctSteps_eq]
  exact bfs_eq_of_replayOK h

theorem fixOctPerfectCheck_of
    (h : replayOK tabKeyF fixOctStepsF Native.fixOctIdTab 11000 L par gen pos = true)
    (hlen : 10752 ≤ L.length) (hc : fixOctCommF = true) :
    Native.fixOctPerfectCheck () = true := by
  obtain ⟨hpos, hhead, hpl, hgl, htree, -⟩ := replay_facts h
  have hcl := fixOctClosure_eq h
  have hsize : Native.closureSizeOK (L.toArray, par.toArray, gen.toArray) = true := by
    unfold Native.closureSizeOK
    rw [decide_eq_true_eq, List.size_toArray]
    exact hlen
  have hbase : Native.closureBaseOK (L.toArray, par.toArray, gen.toArray) = true := by
    unfold Native.closureBaseOK
    cases L with
    | nil => cases hhead
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [beq_iff_eq, get!_toArray_arr, List.getD_cons_zero, hhead]
  have hnd : Native.closureNodupOK (L.toArray, par.toArray, gen.toArray) = true := by
    refine closureNodupOK_of (List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_)
    have := posOK_inj hpos hi hj (congrArg tabKeyF e)
    omega
  have hwidth : Native.closureWidthOK (L.toArray, par.toArray, gen.toArray) = true := by
    unfold Native.closureWidthOK
    rw [allLt_iff']
    intro p hp
    rw [List.size_toArray] at hp
    have hP := replay_induction h (fun t => t.size = 24) (by decide) (fun x _ s hs => by
      simp only [fixOctStepsF, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact size_mulTabF _ _)
    rw [beq_iff_eq, get!_toArray_arr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    exact hP _ (List.getElem_mem hp)
  have htr : Native.closureTreeOK (Native.fixOctComms ())
      (L.toArray, par.toArray, gen.toArray) = true := by
    unfold Native.closureTreeOK
    rw [allLt_iff']
    intro p hp
    rw [List.size_toArray] at hp
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rfl
    · obtain ⟨q1, q2, q3⟩ := htree p hp0 hp
      have hlen2 : fixOctStepsF.length = 2 := rfl
      rw [hlen2] at q2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine Or.inr ⟨by rw [get!_toArray_nat]; exact q1, by rw [get!_toArray_nat]; exact q2, ?_⟩
      rw [get!_toArray_nat, get!_toArray_nat, get!_toArray_arr, get!_toArray_arr,
        List.getD_eq_getElem?_getD (l := L) (i := p), List.getElem?_eq_getElem hp, Option.getD_some, ← q3,
        mulTab_eq]
      rcases (by omega : gen.getD p 0 = 0 ∨ gen.getD p 0 = 1) with e | e <;> rw [e] <;> rfl
  unfold Native.fixOctPerfectCheck Native.fixOctPerfectCheckParts
  simp only [hcl]
  rw [fixOctCommCheck_eq, hc, hsize, hbase, hnd, htr, hwidth]
  rfl

end CFSG.KC.M24G
