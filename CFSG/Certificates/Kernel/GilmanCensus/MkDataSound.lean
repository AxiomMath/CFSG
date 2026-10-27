module

public import Certificates.Data.Kernel.GilmanCensus.MkDataK
import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.RelSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem gramB_eq (B : Array (Array Int)) (r s : IVec) :
    gramB B r s = gramK (LLI B) r.toList s.toList := by
  unfold gramB gramK
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun t i => (List.range' 0 r.size).foldl
    (fun t j => t + r[i]! * B[i]![j]! * s[j]!) t) _ (fun i t => by
      rw [List.forIn_pure_yield_eq_foldl]
      rfl)]
  simp only [Id.run_pure, getElem!_eq_getD_toListI, getRowI, Array.length_toList]
  rfl

theorem contains_snoc' {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x y : α) :
    (l ++ [x]).contains y = (y == x || l.contains y) := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_append, List.mem_singleton, Bool.or_eq_true, beq_iff_eq]
  exact Or.comm

theorem arr_beq' (s v : Array Nat) : (s == v) = (v.toList == s.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]
  exact eq_comm

theorem hset_fold (l : List (Array Nat)) : ∀ (S : HashSet (Array Nat)) (acc : List (List Nat)),
    (∀ v : Array Nat, S.contains v = acc.contains v.toList) → S.size = acc.length →
    let S' := l.foldl (fun S x => S.insert x) S
    let acc' := (l.map Array.toList).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc
    (∀ v : Array Nat, S'.contains v = acc'.contains v.toList) ∧ S'.size = acc'.length := by
  induction l with
  | nil => intro S acc h1 h2; exact ⟨h1, h2⟩
  | cons x l ih =>
    intro S acc h1 h2
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · intro v
      rw [HashSet.contains_insert, h1 v, arr_beq']
      by_cases hx : acc.contains x.toList = true
      · rw [if_pos hx]
        by_cases e : x.toList = v.toList
        · rw [e] at hx
          rw [hx]
          simp
        · have : (v.toList == x.toList) = false := by
            rw [beq_eq_false_iff_ne]
            exact fun h => e h.symm
          rw [this, Bool.false_or]
      · rw [if_neg hx, contains_snoc']
    · rw [HashSet.size_insert]
      by_cases hx : acc.contains x.toList = true
      · rw [if_pos hx, if_pos (HashSet.mem_iff_contains.mpr (by rw [h1 x]; exact hx)), h2]
      · rw [if_neg hx, if_neg (fun hm => hx (by rw [← h1 x]; exact HashSet.mem_iff_contains.mp hm)),
          List.length_append, h2]
        rfl

theorem ofFn_val_toList (m : Nat) : (Array.ofFn (n := m) (·.val)).toList = List.range m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem LL_aug (emb : Array (Array Nat)) (hv : Array Nat) (n : Nat) :
    LL (Array.ofFn (n := n) fun i => (emb.map (·[i.val]!)).push hv[i.val]!) =
      (List.range n).map fun i => (LL emb).map (·.getD i 0) ++ [hv.toList.getD i 0] := by
  apply List.ext_getElem
  · simp [LL]
  · intro i h1 h2
    simp [LL, getElem!_eq_getD_toList, Function.comp_def]

theorem coordsIn_eq (emb : Array (Array Nat)) (hv : Array Nat) (n : Nat) :
    (coordsIn emb hv n).map Array.toList = coordsInK (LL emb) hv.toList n := by
  unfold coordsIn coordsInK
  dsimp only
  have haug : ∀ r ∈ (Array.ofFn (n := n) fun i => (emb.map (·[i.val]!)).push hv[i.val]!).toList,
      r.size = emb.size + 1 := by
    intro r hr
    simp only [Array.toList_ofFn, List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    simp
  obtain ⟨h1, h2⟩ := rowRed3_eq _ _ haug
  rw [LL_aug] at h1 h2
  rw [length_LL]
  generalize rowRed3 (Array.ofFn (n := n) fun i => (emb.map (·[i.val]!)).push hv[i.val]!)
    (emb.size + 1) = p at h1 h2
  obtain ⟨red, piv⟩ := p
  simp only at h1 h2
  rw [arr_beq', ofFn_val_toList, ← h2, ← h1]
  split
  · rename_i hc
    rw [if_pos (by simp only [beq_iff_eq] at hc ⊢; exact hc.symm)]
    simp only [Option.map_some, Array.toList_map, LL, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, Array.back!, getElem!_eq_getD_toList, Array.length_toList]
  · rename_i hc
    rw [if_neg (by simp only [beq_iff_eq] at hc ⊢; exact fun e => hc e.symm)]
    rfl

theorem adj_eq (g : Nat → Nat → Int) (N : Nat) :
    (Array.ofFn (n := N) fun i =>
      (List.range N).foldl (fun m j => if (g i.val j != 0) = true then m ||| bit j else m) 0).toList =
      adjK g N := by
  apply List.ext_getElem
  · simp [adjK]
  · intro i h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, adjK, List.getElem_map, List.getElem_range]
    rfl

theorem lines_eq (d : Nat) :
    LL ((Array.ofFn (n := 3 ^ d) fun k => Array.ofFn (n := d) fun i => k.val / 3 ^ (d - 1 - i.val) % 3).filter
      fun v => firstNZ v == 1) = linesK d := by
  have e : (Array.ofFn (n := 3 ^ d) fun k => Array.ofFn (n := d) fun i => k.val / 3 ^ (d - 1 - i.val) % 3) =
      (((List.range (3 ^ d)).map fun k => (List.range d).map fun i => k / 3 ^ (d - 1 - i) % 3).map
        List.toArray).toArray := by
    apply Array.toList_inj.mp
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [Array.toList_ofFn, List.getElem_ofFn, List.toList_toArray, List.getElem_map,
        List.getElem_range]
      apply Array.toList_inj.mp
      apply List.ext_getElem
      · simp
      · intro j _ _
        simp
  rw [e, arr_filter, LL, List.toList_toArray, linesK, List.filter_map, List.map_map]
  have e1 : (Array.toList ∘ List.toArray : List Nat → List Nat) = id := by
    funext v
    simp
  have e2 : ((fun v => firstNZ v == 1) ∘ List.toArray : List Nat → Bool) = fun v => firstNZK v == 1 := by
    funext v
    simp only [Function.comp_apply, firstNZ_eq, List.toList_toArray]
  rw [e1, e2, List.map_id]

theorem idxI_eq_idxIK (v : List Int) : ∀ (R : List (List Int)) (k : Nat), idxI v R k = idxIK v R k
  | [], _ => rfl
  | r :: R, k => by
    simp only [idxI, idxIK]
    rw [idxI_eq_idxIK v R (k + 1)]

@[expose] def reflCellA (n : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (i : Nat) (st : Bool × Array Nat) (j : Nat) : Bool × Array Nat :=
  let a := 2 * G[j]![i]!
  let b := G[i]![i]!
  let ok := if (a % b != 0) = true then false else st.1
  let z : IVec := Array.ofFn (n := n) fun t => R[j]![t.val]! - (a / b) * R[i]![t.val]!
  let z := if (z.find? (· != 0)).getD 0 < 0 then z.map (- ·) else z
  match ix[z]? with
  | some k => (ok, st.2.push k)
  | none => (false, st.2.push 0)

theorem reflZ_toList (n : Nat) (r s : IVec) (q : Int) :
    (let z : IVec := Array.ofFn (n := n) fun t => s[t.val]! - q * r[t.val]!
     if (z.find? (· != 0)).getD 0 < 0 then z.map (- ·) else z).toList =
      reflZK n r.toList s.toList q := by
  have e : (Array.ofFn (n := n) fun t => s[t.val]! - q * r[t.val]!).toList =
      (List.range n).map fun t => s.toList.getD t 0 - q * r.toList.getD t 0 := by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp [getElem!_eq_getD_toListI]
  unfold reflZK
  dsimp only
  rw [← e, ← Array.find?_toList]
  split <;> simp

theorem reflCell_eq (n : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (g : Nat → Nat → Int) (hix : ∀ v : IVec, ix[v]? = idxI v.toList (LLI R) 0)
    (hG : ∀ i j, G[i]![j]! = g i j) (i : Nat) (st : Bool × Array Nat) (j : Nat) :
    (reflCellA n R G ix i st j).1 = (reflStepK (LLI R) g n i (st.1, st.2.toList) j).1 ∧
      (reflCellA n R G ix i st j).2.toList = (reflStepK (LLI R) g n i (st.1, st.2.toList) j).2 := by
  unfold reflCellA reflStepK
  dsimp only
  rw [hG j i, hG i i, hix, reflZ_toList, idxI_eq_idxIK, ← getRowI, ← getRowI]
  cases idxIK (reflZK n (R[i]!).toList (R[j]!).toList (2 * g j i / g i i)) (LLI R) 0 <;> simp

@[expose] def reflA (n : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (N : Nat) (ok : Bool) : Bool × Array (Array Nat) :=
  (List.range' 0 N).foldl (fun st i =>
    let r := (List.range' 0 N).foldl (reflCellA n R G ix i) (st.1, #[])
    (r.1, st.2.push r.2)) (ok, #[])

theorem reflRow_fold (n : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (g : Nat → Nat → Int) (hix : ∀ v : IVec, ix[v]? = idxI v.toList (LLI R) 0)
    (hG : ∀ i j, G[i]![j]! = g i j) (i : Nat) : ∀ (l : List Nat) (st : Bool × Array Nat)
    (t : Bool × List Nat), st.1 = t.1 → st.2.toList = t.2 →
    (l.foldl (reflCellA n R G ix i) st).1 = (l.foldl (reflStepK (LLI R) g n i) t).1 ∧
      (l.foldl (reflCellA n R G ix i) st).2.toList = (l.foldl (reflStepK (LLI R) g n i) t).2
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | j :: l, st, t, h1, h2 => by
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨e1, e2⟩ := reflCell_eq n R G ix g hix hG i st j
    have ht : t = (st.1, st.2.toList) := by rw [h1, h2]
    rw [ht] at ⊢
    exact reflRow_fold n R G ix g hix hG i l _ _ e1 e2

theorem refl_eq (n : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (g : Nat → Nat → Int) (hix : ∀ v : IVec, ix[v]? = idxI v.toList (LLI R) 0)
    (hG : ∀ i j, G[i]![j]! = g i j) (N : Nat) (ok : Bool) :
    (reflA n R G ix N ok).1 = (reflK (LLI R) g n N ok).1 ∧
      LL (reflA n R G ix N ok).2 = (reflK (LLI R) g n N ok).2 := by
  unfold reflA reflK reflRowK
  have : ∀ (l : List Nat) (st : Bool × Array (Array Nat)) (t : Bool × List (List Nat)),
      st.1 = t.1 → LL st.2 = t.2 →
      (l.foldl (fun st i =>
        let r := (List.range' 0 N).foldl (reflCellA n R G ix i) (st.1, #[])
        (r.1, st.2.push r.2)) st).1 = (l.foldl (fun st i =>
        let r := (List.range' 0 N).foldl (reflStepK (LLI R) g n i) (st.1, [])
        (r.1, st.2 ++ [r.2])) t).1 ∧
      LL (l.foldl (fun st i =>
        let r := (List.range' 0 N).foldl (reflCellA n R G ix i) (st.1, #[])
        (r.1, st.2.push r.2)) st).2 = (l.foldl (fun st i =>
        let r := (List.range' 0 N).foldl (reflStepK (LLI R) g n i) (st.1, [])
        (r.1, st.2 ++ [r.2])) t).2 := by
    intro l
    induction l with
    | nil => intro st t h1 h2; exact ⟨h1, h2⟩
    | cons i l ih =>
      intro st t h1 h2
      rw [List.foldl_cons, List.foldl_cons]
      obtain ⟨e1, e2⟩ := reflRow_fold n R G ix g hix hG i (List.range' 0 N) (st.1, #[]) (t.1, [])
        h1 rfl
      apply ih
      · exact e1
      · simp only [LL, Array.toList_push, List.map_append, List.map_cons, List.map_nil] at h2 ⊢
        rw [h2, e2]
  exact this _ _ _ rfl rfl

theorem rangeSum_eq (n : Nat) (f : Nat → Int) :
    Id.run (forIn [0:n] (0 : Int) fun i t => pure (ForInStep.yield (t + f i))) = sumK n f := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [List.forIn_pure_yield_eq_foldl]
  rfl

theorem dotI_eq (v w : Array Int) : dotI v w = dotIK v.toList w.toList := by
  unfold dotI dotIK
  rw [← rangeSum_eq]
  simp only [getElem!_eq_getD_toListI, Array.length_toList]
  rfl

theorem imod3_eq (x : Int) : imod3 x = imod3K x := by
  unfold imod3 imod3K
  rfl

theorem rangeSumMod_eq (n : Nat) (f : Nat → Int) :
    Id.run (do
      let s ← forIn [0:n] (0 : Int) fun i t => pure (ForInStep.yield (t + f i))
      pure (imod3 s)) = imod3K (sumK n f) := by
  rw [← rangeSum_eq]
  exact imod3_eq _

@[expose] def fhStepA (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int) (emb : Array (Array Nat))
    (st : Bool × Array (Array Nat) × Array (Array Nat)) (r : IVec) :
    Bool × Array (Array Nat) × Array (Array Nat) :=
  let norm := gramB B r r
  let h : IVec := Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / norm
  let f : IVec := if (mode == 2 || mode == 3) = true then r
    else Array.ofFn (n := n) fun j =>
      Id.run (forIn [0:n] (0 : Int) fun i t => pure (ForInStep.yield (t + r[i]! * A[i]![j.val]!)))
  let hv : Array Nat :=
    if mode == 2 || mode == 3 then
      Array.ofFn (n := n) fun i => Id.run do
        let mut t : Int := 0
        for j in [0:n] do
          t := t + A[i.val]![j]! * h[j]!
        return imod3 t
    else h.map imod3
  let F := st.2.1.push (emb.map fun v => imod3 (dotI f (v.map fun (x : Nat) => (x : Int))))
  match coordsIn emb hv n with
  | some c => (st.1, F, st.2.2.push c)
  | none => (false, F, st.2.2)

theorem fhStep_eq (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int) (emb : Array (Array Nat))
    (st : Bool × Array (Array Nat) × Array (Array Nat)) (r : IVec) :
    (fhStepA mode n A B sc emb st r).1 = (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)
        (st.1, LL st.2.1, LL st.2.2) r.toList).1 ∧
      LL (fhStepA mode n A B sc emb st r).2.1 = (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)
        (st.1, LL st.2.1, LL st.2.2) r.toList).2.1 ∧
      LL (fhStepA mode n A B sc emb st r).2.2 = (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)
        (st.1, LL st.2.1, LL st.2.2) r.toList).2.2 := by
  have hh : (Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / gramB B r r).toList =
      (List.range n).map fun i => 2 * r.toList.getD i 0 * sc.toList.getD i 0 / gramK (LLI B) r.toList r.toList := by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp [getElem!_eq_getD_toListI, gramB_eq]
  have hf : (if (mode == 2 || mode == 3) = true then r
      else Array.ofFn (n := n) fun j =>
        Id.run (forIn [0:n] (0 : Int) fun i t => pure (ForInStep.yield (t + r[i]! * A[i]![j.val]!)))).toList =
      if (mode == 2 || mode == 3) = true then r.toList
      else (List.range n).map fun j => sumK n fun i => r.toList.getD i 0 * ((LLI A).getD i []).getD j 0 := by
    split
    · rfl
    · apply List.ext_getElem
      · simp
      · intro i _ _
        simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
        rw [rangeSum_eq]
        simp only [getElem!_eq_getD_toListI, getRowI]
  have hv : (if (mode == 2 || mode == 3) = true then
      Array.ofFn (n := n) fun i => Id.run do
        let s ← forIn [0:n] (0 : Int) fun j t => pure (ForInStep.yield (t + A[i.val]![j]! *
          (Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / gramB B r r)[j]!))
        pure (imod3 s)
      else (Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / gramB B r r).map imod3).toList =
      if (mode == 2 || mode == 3) = true then
        (List.range n).map fun i => imod3K (sumK n fun j => ((LLI A).getD i []).getD j 0 *
          ((List.range n).map fun i => 2 * r.toList.getD i 0 * sc.toList.getD i 0 /
            gramK (LLI B) r.toList r.toList).getD j 0)
      else ((List.range n).map fun i => 2 * r.toList.getD i 0 * sc.toList.getD i 0 /
        gramK (LLI B) r.toList r.toList).map imod3K := by
    generalize (Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / gramB B r r) = hA at hh ⊢
    split
    · apply List.ext_getElem
      · simp
      · intro i _ _
        simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
        rw [rangeSumMod_eq]
        simp only [getElem!_eq_getD_toListI, getRowI, hh]
    · have e : imod3 = imod3K := funext imod3_eq
      rw [Array.toList_map, hh, e]
  unfold fhStepA fhStepK
  dsimp only
  have hF : LL (st.2.1.push (emb.map fun v => imod3 (dotI (if (mode == 2 || mode == 3) = true then r
      else Array.ofFn (n := n) fun j =>
        Id.run (forIn [0:n] (0 : Int) fun i t => pure (ForInStep.yield (t + r[i]! * A[i]![j.val]!))))
      (v.map fun (x : Nat) => (x : Int))))) =
      LL st.2.1 ++ [(LL emb).map fun v => imod3K (dotIK (if (mode == 2 || mode == 3) = true then
        r.toList else (List.range n).map fun j => sumK n fun i =>
          r.toList.getD i 0 * ((LLI A).getD i []).getD j 0) (v.map fun (x : Nat) => (x : Int)))] := by
    rw [← hf]
    simp [LL, dotI_eq, imod3_eq, Function.comp_def, Int.ofNat_eq_coe]
  split
  · rename_i c heq
    have hc := congrArg (Option.map Array.toList) heq
    rw [coordsIn_eq, hv, Option.map_some] at hc
    rw [hc]
    refine ⟨rfl, hF, ?_⟩
    simp [LL]
  · rename_i heq
    have hc := congrArg (Option.map Array.toList) heq
    rw [coordsIn_eq, hv, Option.map_none] at hc
    rw [hc]
    exact ⟨rfl, hF, rfl⟩

theorem hset_size (l : List (Array Nat)) :
    (∀ v : Array Nat, (l.foldl (fun S x => S.insert x) (∅ : HashSet (Array Nat))).contains v =
      (dedupK (l.map Array.toList)).contains v.toList) ∧
    (l.foldl (fun S x => S.insert x) (∅ : HashSet (Array Nat))).size =
      (dedupK (l.map Array.toList)).length :=
  hset_fold l ∅ [] (fun v => by simp) (by simp)

end Certificates.GilmanCensusK

end
