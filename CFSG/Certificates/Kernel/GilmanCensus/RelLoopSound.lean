module

public import CFSG.Certificates.Kernel.GilmanCensus.TailOkSound
public import Certificates.Data.Kernel.GilmanCensus.RelK

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def rrA (n : Nat) (rho : Array Nat) (AR : Array IVec) (i : Nat) : IVec :=
  Array.ofFn (n := n) fun j => AR[i]![j.val]! + AR[i]![rho[j.val]!]!

theorem grpLoop_fold (n : Nat) (AR : Array IVec) (rho : Array Nat) :
    grpLoop n AR rho = (List.range' 0 AR.size).foldl (fun st i => grpStep st (rrA n rho AR i, i))
      (∅, #[]) := by
  unfold grpLoop
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun st i => grpStep st (rrA n rho AR i, i)) _ (fun i st => by
    unfold grpStep rrA
    split <;> rename_i h <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl)]
  rfl

theorem map_range_getD {α β : Type} (f : α → β) (d : α) (L : List α) :
    (List.range L.length).map (fun i => f (L.getD i d)) = L.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h1)]
    rfl

theorem rrA_toList (n : Nat) (rho : Array Nat) (AR : Array IVec) (i : Nat) :
    (rrA n rho AR i).toList = rrK rho.toList n ((LLI AR).getD i []) := by
  apply List.ext_getElem
  · simp [rrA, rrK]
  · intro j _ _
    simp only [rrA, rrK, Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [getEntI, getEntI, getElem!_eq_getD_toList]

theorem zip_range_map {α : Type} (f : Nat → α) (N : Nat) :
    ((List.range N).map f).zip (List.range ((List.range N).map f).length) =
      (List.range N).map fun i => (f i, i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem grpLoop_eq (n : Nat) (AR : Array IVec) (rho : Array Nat) :
    LLI (grpLoop n AR rho).2 = dedupK ((LLI AR).map (rrK rho.toList n)) ∧
      ∀ v : IVec, ((grpLoop n AR rho).1.getD v #[]).toList =
        idxsK v.toList ((LLI AR).map (rrK rho.toList n)) 0 := by
  have hl : ((List.range AR.size).map (rrA n rho AR)).map Array.toList =
      (LLI AR).map (rrK rho.toList n) := by
    rw [List.map_map, ← length_LLI, ← map_range_getD (rrK rho.toList n) []]
    apply List.map_congr_left
    intro i _
    exact rrA_toList n rho AR i
  have e : grpLoop n AR rho = (((List.range AR.size).map (rrA n rho AR)).zip
      (List.range ((List.range AR.size).map (rrA n rho AR)).length)).foldl grpStep (∅, #[]) := by
    rw [grpLoop_fold, zip_range_map, List.foldl_map, List.range_eq_range']
  obtain ⟨g1, g2⟩ := groups_fold ((List.range AR.size).map (rrA n rho AR))
  rw [hl] at g1 g2
  rw [e]
  exact ⟨g1, fun v => (g2 v).1⟩

@[expose] def relFA (n : Nat) (A : Array (Array Int)) (AR : Array IVec) (grp v : Array Nat) : Nat :=
  Id.run do
    let mut t : Int := 0
    for i in [0:n] do
      for j in [0:n] do
        t := t + AR[grp[0]!]![i]! * A[i]![j]! * ((v[j]! : Nat) : Int)
    return imod3 t

@[expose] def relHA (AR : Array IVec) (rr : IVec) (grp : Array Nat) : Array Nat :=
  let hv := if grp.size == 2 then rr else AR[grp[0]!]!
  #[imod3 hv[0]!, imod3 hv[2]!, imod3 hv[1]!, imod3 hv[3]!]

@[expose] def relStepA (n : Nat) (A : Array (Array Int)) (AR : Array IVec)
    (groups : HashMap IVec (Array Nat)) (st : Array (Array Nat) × Array (Array Nat) × Array (Array Nat))
    (rr : IVec) : Array (Array Nat) × Array (Array Nat) × Array (Array Nat) :=
  (st.1.push (groups.getD rr #[]),
    st.2.1.push ((#[#[1, 0, 0, 0, 0, 1], #[0, 0, 1, 0, 1, 0], #[0, 1, 0, 0, 0, 0],
      #[0, 0, 0, 1, 0, 0]] : Array (Array Nat)).map (relFA n A AR (groups.getD rr #[]))),
    st.2.2.push (relHA AR rr (groups.getD rr #[])))

theorem relLoop_fold (n : Nat) (A : Array (Array Int)) (AR : Array IVec)
    (groups : HashMap IVec (Array Nat)) (R : Array IVec) :
    relLoop n A AR groups R = R.toList.foldl (relStepA n A AR groups) (#[], #[], #[]) := by
  unfold relLoop
  dsimp only
  exact forIn_yieldA (relStepA n A AR groups) _ (fun _ _ => rfl) R (#[], #[], #[])

theorem LL_push' (a : Array (Array Nat)) (x : Array Nat) : LL (a.push x) = LL a ++ [x.toList] := by
  simp [LL]

theorem relFold_eq (n : Nat) (A : Array (Array Int)) (AR : Array IVec)
    (groups : HashMap IVec (Array Nat)) : ∀ (l : List IVec)
    (st : Array (Array Nat) × Array (Array Nat) × Array (Array Nat)),
    LL (l.foldl (relStepA n A AR groups) st).1 =
        LL st.1 ++ l.map (fun rr => (groups.getD rr #[]).toList) ∧
      LL (l.foldl (relStepA n A AR groups) st).2.1 = LL st.2.1 ++ l.map (fun rr =>
        ((#[#[1, 0, 0, 0, 0, 1], #[0, 0, 1, 0, 1, 0], #[0, 1, 0, 0, 0, 0],
          #[0, 0, 0, 1, 0, 0]] : Array (Array Nat)).map (relFA n A AR (groups.getD rr #[]))).toList) ∧
      LL (l.foldl (relStepA n A AR groups) st).2.2 =
        LL st.2.2 ++ l.map (fun rr => (relHA AR rr (groups.getD rr #[])).toList)
  | [], st => by simp
  | rr :: l, st => by
    rw [List.foldl_cons]
    obtain ⟨e1, e2, e3⟩ := relFold_eq n A AR groups l (relStepA n A AR groups st rr)
    rw [e1, e2, e3]
    simp [relStepA, LL_push']

theorem relFA_eq (n : Nat) (A : Array (Array Int)) (AR : Array IVec) (grp v : Array Nat) :
    relFA n A AR grp v = relFK n (LLI A) ((LLI AR).getD (grp.toList.getD 0 0) []) v.toList := by
  unfold relFA relFK
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun t i => (List.range' 0 n).foldl
    (fun t j => t + AR[grp[0]!]![i]! * A[i]![j]! * ((v[j]! : Nat) : Int)) t) _ (fun i t => by
      rw [List.forIn_pure_yield_eq_foldl]
      rfl)]
  simp only [Id.run_pure, Id.run_bind, getEntI, getElem!_eq_getD_toList, imod3_eq]
  rfl

theorem relF_eq (n : Nat) (A : Array (Array Int)) (AR : Array IVec) (grp : Array Nat) :
    ((#[#[1, 0, 0, 0, 0, 1], #[0, 0, 1, 0, 1, 0], #[0, 1, 0, 0, 0, 0],
      #[0, 0, 0, 1, 0, 0]] : Array (Array Nat)).map (relFA n A AR grp)).toList =
      relEmbK.map (relFK n (LLI A) ((LLI AR).getD (grp.toList.getD 0 0) [])) := by
  simp only [Array.toList_map, List.toList_toArray, List.map_cons, List.map_nil, relFA_eq, relEmbK]

theorem relHA_eq (AR : Array IVec) (rr : IVec) (grp : Array Nat) :
    (relHA AR rr grp).toList = relHK (LLI AR) rr.toList grp.toList := by
  have hh : (if (grp.size == 2) = true then rr else AR[grp[0]!]!).toList =
      if (grp.toList.length == 2) = true then rr.toList
      else (LLI AR).getD (grp.toList.getD 0 0) [] := by
    rw [Array.length_toList]
    split
    · rfl
    · rw [getRowI, getElem!_eq_getD_toList]
  unfold relHA relHK
  simp only [List.toList_toArray, getElem!_eq_getD_toListI, hh, imod3_eq]

theorem rel_eq (n : Nat) (A B : Array (Array Int)) (AR : Array IVec) (dk : DK)
    (Al Bl : List (List Int)) (hA : LLI A = Al) (hB : LLI B = Bl) (hAR : LLI AR = toI dk.AR)
    (hm : mode1OkK dk n Al = true) (ht : tailOkK dk n Bl = true) :
    ∃ dt, tailS 1 n AR #[5, 1, 4, 3, 2, 0] B true (grpLoop n AR #[5, 1, 4, 3, 2, 0]).2
      (relLoop n A AR (grpLoop n AR #[5, 1, 4, 3, 2, 0]).1 (grpLoop n AR #[5, 1, 4, 3, 2, 0]).2).1
      (relLoop n A AR (grpLoop n AR #[5, 1, 4, 3, 2, 0]).1 (grpLoop n AR #[5, 1, 4, 3, 2, 0]).2).2.1
      (relLoop n A AR (grpLoop n AR #[5, 1, 4, 3, 2, 0]).1 (grpLoop n AR #[5, 1, 4, 3, 2, 0]).2).2.2
      4 = some dt ∧ Rel dt dk := by
  simp only [mode1OkK, Bool.and_eq_true, beq_iff_eq, and_assoc] at hm
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hm
  obtain ⟨g1, g2⟩ := grpLoop_eq n AR #[5, 1, 4, 3, 2, 0]
  have hrho : (#[5, 1, 4, 3, 2, 0] : Array Nat).toList = dk.rho := by rw [m2]
  rw [hAR, hrho] at g1 g2
  generalize grpLoop n AR #[5, 1, 4, 3, 2, 0] = g at g1 g2 ⊢
  have hR : LLI g.2 = toI dk.R := by rw [g1, m4]
  rw [relLoop_fold]
  obtain ⟨e1, e2, e3⟩ := relFold_eq n A AR g.1 g.2.toList (#[], #[], #[])
  dsimp only at e1 e2 e3
  have hLL : LL (#[] : Array (Array Nat)) = [] := rfl
  have hk : ∀ rr ∈ g.2.toList, (g.1.getD rr #[]).toList =
      idxsK rr.toList ((toI dk.AR).map (rrK dk.rho n)) 0 := fun rr _ => g2 rr
  refine tailOk_tailS 1 n AR _ B g.2 _ _ _ 4 dk m1.symm m3.symm hR hAR ?_ hrho ?_ ?_ (by rw [hB]; exact ht)
  · rw [e1, m5, ← hR, LLI, List.map_map, hLL, List.nil_append]
    exact List.map_congr_left (fun rr hr => hk rr hr)
  · rw [e2, m6, ← hR, LLI, List.map_map, hLL, List.nil_append]
    refine List.map_congr_left (fun rr hr => ?_)
    exact (relF_eq n A AR _).trans (by rw [hA, hAR, hk rr hr] <;> rfl)
  · rw [e3, m7, ← hR, LLI, List.map_map, hLL, List.nil_append]
    refine List.map_congr_left (fun rr hr => ?_)
    exact (relHA_eq AR rr _).trans (by rw [hAR, hk rr hr] <;> rfl)

end Certificates.GilmanCensusK

end
