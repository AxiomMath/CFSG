module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.CandSound
public import CFSG.Certificates.Kernel.GilmanCensus.PlaneSound
public import CFSG.Certificates.Kernel.GilmanCensus.SimSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def addA (a : Array Nat) (v : List Nat) : Array Nat := (addV a.toList v).toArray

@[expose] def planeT (dk : DK) (x : List Nat) (zx L w : Nat) (y : List Nat) (D : List (List Nat))
    (J : Nat) : List Nat × List Nat × Bool :=
  let cands := ((dlK dk.d x y).filter (· != x)).flatMap (candsAt dk x zx L J)
  let badC := cands.any fun c => c.2.2.2.2.1
  if cands.length == 0 then ([0, 0, 1, 0, 1, 0, 0], [w, 0, w, 0, 0], false) else
  if cands.any (fun c => c.2.2.1) then ([0, 0, 1, 1, 0, 0, 0], [w, w, 0, 0, 0], badC) else
  let pp := patternsK dk (null3K D dk.d) cands
  let resid := pp.1.filter fun pat => pat.length > 0 && !(pat.any fun j =>
    (cands.getD j ([], 0, false, false, false, [])).2.2.2.1)
  if resid.length == 0 then ([0, 0, 1, 0, 0, 1, 0], [w, 0, 0, w, 0], badC || pp.2) else
  ([0, 0, 1, 0, 0, 0, resid.length], [w, 0, 0, 0, resid.length * w],
    badC || pp.2 || resid.any (residBad dk L J cands))

theorem planeK_eq (dk : DK) (x : List Nat) (zx L w : Nat) (y : List Nat) (D : List (List Nat)) :
    planeK dk x zx L w y D =
      let ns := (compsK dk.adj (L &&& zerosK dk y)).filter fun c => !solvableK dk c
      let eligible := ns.filter fun c => (kernelK dk c).length == 2
      if eligible.length == 0 then ([0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0], false) else
      let T := planeT dk x zx L w y D (eligible.getD 0 0)
      (T.1, T.2.1, !(ns.length == 1 && eligible.length == 1) || T.2.2) := by
  unfold planeK planeT
  dsimp only
  split
  · rfl
  repeat' split
  all_goals simp only [Bool.or_false, Bool.or_assoc]

theorem st_inc (a : Array Nat) (h : a.size = 7) (i : Nat) (k : Nat) (hi : i < 7) :
    a.modify i (fun x => x + k) =
      addA a ((List.range 7).map fun j => if j = i then k else 0) := by
  obtain ⟨l⟩ := a
  simp only [List.size_toArray] at h
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6], _ =>
    rcases i with _ | _ | _ | _ | _ | _ | _ | i
    all_goals first | rfl | omega

theorem wt_inc (a : Array Nat) (h : a.size = 5) (i : Nat) (k : Nat) (hi : i < 5) :
    a.modify i (fun x => x + k) =
      addA a ((List.range 5).map fun j => if j = i then k else 0) := by
  obtain ⟨l⟩ := a
  simp only [List.size_toArray] at h
  match l, h with
  | [a0, a1, a2, a3, a4], _ =>
    rcases i with _ | _ | _ | _ | _ | i
    all_goals first | rfl | omega

theorem addA_size (a : Array Nat) (v : List Nat) (h : v.length = a.size) : (addA a v).size = a.size := by
  unfold addA addV
  simp [h]

theorem addV_assoc : ∀ (a b c : List Nat), addV (addV a b) c = addV a (addV b c)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => by simp [addV]
  | x :: a, y :: b, z :: c => by
    simp only [addV, List.zipWith_cons_cons, List.cons.injEq] at *
    exact ⟨Nat.add_assoc x y z, addV_assoc a b c⟩

theorem addA_addA (a : Array Nat) (u v : List Nat) : addA (addA a u) v = addA a (addV u v) := by
  unfold addA
  rw [List.toList_toArray, addV_assoc]

theorem st_inc' (a : Array Nat) (h : a.size = 7) (u : List Nat) (hu : u.length = 7) (i k : Nat)
    (hi : i < 7) : (addA a u).modify i (fun x => x + k) =
      addA a (addV u ((List.range 7).map fun j => if j = i then k else 0)) := by
  rw [st_inc _ (by rw [addA_size _ _ (by rw [hu, h])]; exact h) i k hi, addA_addA]

theorem wt_inc' (a : Array Nat) (h : a.size = 5) (u : List Nat) (hu : u.length = 5) (i k : Nat)
    (hi : i < 5) : (addA a u).modify i (fun x => x + k) =
      addA a (addV u ((List.range 5).map fun j => if j = i then k else 0)) := by
  rw [wt_inc _ (by rw [addA_size _ _ (by rw [hu, h])]; exact h) i k hi, addA_addA]

theorem sim_dlLoop (dt : Data) (x y : Array Nat) :
    Sim dt (forIn [:3] (#[] : Array (Array Nat)) (dlOuter dt x y)) (dlM dt.d x y) false := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have hin : ∀ a dl, Sim dt (forIn [:3] dl (dlInner dt x y a))
      ((List.range' 0 3).foldl (dlStep dt.d x y a) dl) false := by
    intro a dl
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one]
    have := sim_forIn dt (dlStep dt.d x y a) (fun _ _ => false) (dlInner dt x y a) (fun b s => by
      unfold dlInner dlStep zAB
      split
      · dsimp only
        split <;> exact sim_pure dt _
      · exact sim_pure dt _) (List.range' 0 3) dl
    rw [orFold_false] at this
    exact this
  have := sim_forIn dt (fun dl a => (List.range' 0 3).foldl (dlStep dt.d x y a) dl) (fun _ _ => false)
    (dlOuter dt x y) (fun a s => by
      unfold dlOuter
      exact sim_bind (hin a s) (sim_pure dt _)) (List.range' 0 3) #[]
  rw [orFold_false] at this
  exact this

theorem zAB_size (d : Nat) (x y : Array Nat) (a b : Nat) : (zAB d x y a b).size = d := by
  unfold zAB line3
  simp

theorem dlF_size (d : Nat) (x y : Array Nat) : ∀ (ps : List (Nat × Nat)) (dl : Array (Array Nat)),
    (∀ z ∈ dl.toList, z.size = d) → ∀ z ∈ (dlF d x y ps dl).toList, z.size = d
  | [], _, h => h
  | ab :: ps, dl, h => by
    unfold dlF
    rw [List.foldl_cons]
    apply dlF_size d x y ps
    unfold dlStep
    split
    · split
      · intro z hz
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · exact h z hz
        · rw [hz]
          exact zAB_size d x y _ _
      · exact h
    · exact h

theorem dlM_size (d : Nat) (x y : Array Nat) : ∀ z ∈ (dlM d x y).toList, z.size = d := by
  rw [dlM_eq]
  exact dlF_size d x y _ #[] (by simp)

theorem candK_some (dk : DK) (x : List Nat) (zx L J : Nat) (z : List Nat) (K : Nat) (c : Cand)
    (h : candK dk x zx L J z K = some c) : c.2.1 = K ∧ c.2.2.2.2.2 = kernelK dk K := by
  unfold candK at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h
       subst h
       exact ⟨rfl, rfl⟩)
    | (simp only [reduceCtorEq] at h)

theorem cand_mem {dt : Data} {dk : DK} (C : Ctx dt dk) (x : List Nat) (zx L J : Nat)
    (dl : List (Array Nat)) (c : Cand) (hc : c ∈ candsL dk x zx L J (dl.map Array.toList)) :
    c.2.2.2.2.2 = kernelK dk c.2.1 ∧ c.2.1 < 2 ^ dk.N := by
  unfold candsL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨z, hzm, hz⟩ := hc
  have hz' : z ∈ dl.map Array.toList := (List.mem_filter.mp hzm).1
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz'
  rw [candsAt_eq, List.mem_filterMap] at hz
  obtain ⟨K, hK, he⟩ := hz
  have hzz := zeros_lt C w
  rw [zeros_rel C w] at hzz
  have hlt := compsK_lt dk _ hzz K hK
  obtain ⟨e1, e2⟩ := candK_some dk _ _ _ _ _ K c he
  rw [e1]
  exact ⟨e2, hlt⟩

end Certificates.GilmanCensusK

end
