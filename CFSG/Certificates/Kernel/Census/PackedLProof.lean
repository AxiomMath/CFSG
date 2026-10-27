module

public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem strictLA_eq {β : Sort _} (l : List Nat) (k : List Nat → β) : strictLA l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | zero => exact ih (fun t => k (0 :: t))
    | succ m => exact ih (fun t => k (m.succ :: t))

theorem strictB_eqL (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictNA_eq {β : Sort _} (y : Nat) (k : Nat → β) : strictNA y k = k y := by
  cases y <;> rfl

theorem strictLBo_eq {β : Sort _} (l : List Bool) (k : List Bool → β) : strictLBo l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | false => exact ih (fun t => k (false :: t))
    | true => exact ih (fun t => k (true :: t))

theorem walkF_map (f : Nat → Nat → Bool) (g : Nat → Bool) (us cs : List Nat) :
    walkF f us (us.map g) cs = walkAll (fun u c => !(g u) || f u c) us cs := by
  induction us generalizing cs with
  | nil => cases cs <;> rfl
  | cons u us ih =>
    cases cs with
    | nil => simp only [List.map_cons, walkF, walkAll, ih]
    | cons c cs => simp only [List.map_cons, walkF, walkAll, ih]

theorem getElem!_eq_toList_getDL {α : Type _} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = a.toList.getD i default := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem range_all_getElem! {α : Type _} [Inhabited α] (a : Array α) (g : Nat → Bool)
    (f : α → Bool) (h : ∀ k < a.size, g k = f a[k]!) : (List.range a.size).all g = a.toList.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro hg x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk' : k < a.size := by simpa using hk
    have := hg k hk'
    rw [h k hk', getElem!_pos a k hk'] at this
    simpa using this
  · intro hf k hk
    rw [h k hk, getElem!_pos a k hk]
    exact hf _ (Array.getElem_mem_toList hk)

section Checks

variable (n w : Nat)

theorem pmask_cons (b : Nat) (bs : List Nat) (m : Nat) :
    pmask n w ⟨b :: bs⟩ m =
      if m.testBit 0 then pc n w b (pmask n w ⟨bs⟩ (m / 2)) else pmask n w ⟨bs⟩ (m / 2) := by
  unfold pmask pprod
  simp only [List.size_toArray, List.length_cons, List.range_succ_eq_map, List.filter_cons,
    List.filter_map, List.map_map]
  have hg : ∀ k, (⟨b :: bs⟩ : Array Nat)[k + 1]! = (⟨bs⟩ : Array Nat)[k]! := fun k => by
    simp only [getElem!_eq_toList_getDL, List.getD_cons_succ]
  have h0 : (⟨b :: bs⟩ : Array Nat)[0]! = b := by
    simp only [getElem!_eq_toList_getDL, List.getD_cons_zero]
  have hf : ((fun k => m.testBit k) ∘ Nat.succ) = fun k => (m / 2).testBit k := by
    funext k
    simp [Nat.testBit_add_one]
  have hm : ((fun k => (⟨b :: bs⟩ : Array Nat)[k]!) ∘ Nat.succ) = fun k => (⟨bs⟩ : Array Nat)[k]! := by
    funext k
    exact hg k
  rw [hf]
  split <;> simp only [List.map_cons, List.map_map, hm, h0, List.foldr_cons]

theorem range_two_mul (k : Nat) :
    List.range (2 * k) = (List.range k).flatMap fun m => [2 * m, 2 * m + 1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.range_succ, List.range_succ, ih,
      List.range_succ, List.flatMap_append]
    simp

theorem pspanL_eq (l : List Nat) :
    (List.range (2 ^ l.length)).map (pmask n w ⟨l⟩) = pspanL n w l := by
  induction l with
  | nil => simp [pspanL, pmask, pprod]
  | cons b bs ih =>
    rw [pspanL, strictLA_eq, ← ih, List.length_cons, Nat.pow_succ', range_two_mul,
      List.map_flatMap, List.flatMap_map]
    congr 1
    funext m
    have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    simp [pmask_cons, h1, h2, Nat.testBit_zero]

theorem pmaskCert_pts (b : Array Nat) : (pmaskCert n w b).pts = Array.mk (pspanL n w b.toList) := by
  cases b with
  | mk l =>
    simp only [pmaskCert, ← pspanL_eq, List.size_toArray]

theorem pmaskCert_mk (b : Array Nat) :
    (⟨Array.mk (pspanL n w b.toList), (pmaskCert n w b).edges, (pmaskCert n w b).par,
      (pmaskCert n w b).lab⟩ : ArrCertP) = pmaskCert n w b := by
  rw [← pmaskCert_pts]

theorem pmem_pmaskCert (b : Array Nat) (u : Nat) :
    pmem (pmaskCert n w b) u = (pspanL n w b.toList).any (Nat.beq u) := by
  unfold pmem
  rw [pmaskCert_pts]

variable {n w}

theorem pchildOK_eqL {nodes : Array NodeP} {cN : Array ArrCertP}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {i : Nat}
    (hi : i < nodes.size) (u j : Nat) :
    pchildOK n w nodes cN i u j = pchildL n w nodes.toList nodes.size nodes[i]!.basis.toList
      (pspanL n w nodes[i]!.basis.toList) u j := by
  unfold pchildOK pchildL
  by_cases hj : j < nodes.size
  · have hb : Nat.blt j nodes.size = true := by rw [Nat.blt_eq]; exact hj
    simp only [hb, Bool.true_and]
    rw [← getElem!_eq_toList_getDL, hc j hj, hc i hi]
    generalize nodes[j]! = nd
    cases nd with
    | mk bj wt ch =>
      simp only [pchildAt, strictLA_eq, pmem_pmaskCert]
      rw [range_all_getElem! bj _ (fun b => (pspanL n w nodes[i]!.basis.toList).any (Nat.beq b) ||
          (pspanL n w nodes[i]!.basis.toList).any (Nat.beq (pc n w u b))) (fun _ _ => rfl),
        range_all_getElem! nodes[i]!.basis _ (fun b => (pspanL n w bj.toList).any (Nat.beq b))
          (fun _ _ => rfl)]
      simp only [Bool.and_assoc]
  · have hb : Nat.blt j nodes.size = false := by
      rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
      exact hj
    simp only [hb, Bool.false_and]

theorem walk_eqL {nodes : Array NodeP} {cN : Array ArrCertP}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {i : Nat}
    (hi : i < nodes.size) (pts ch : List Nat) :
    walkAll (fun u c =>
      !(Nat.beq (pc n w u u) (pid n w)) ||
        !((List.range nodes[i]!.basis.size).all fun k => pcommA n w u nodes[i]!.basis[k]!) ||
        pmem cN[i]! u || pchildOK n w nodes cN i u c) pts ch =
      pwalkF n w nodes.toList nodes.size nodes[i]!.basis.toList
        (pspanL n w nodes[i]!.basis.toList) pts (pts.map fun u => Nat.beq (pc n w u u) (pid n w))
        ch := by
  unfold pwalkF
  rw [walkF_map]
  refine congrArg (fun f => walkAll f pts ch) ?_
  funext u c
  rw [pchildOK_eqL hc hi, hc i hi, pmem_pmaskCert,
    range_all_getElem! nodes[i]!.basis _ (fun b => pcommA n w u b) (fun _ _ => rfl)]
  simp only [Bool.or_assoc]

theorem pinvFl_eq (cS : ArrCertP) :
    pinvFl n w cS = cS.pts.toList.map fun u => Nat.beq (pc n w u u) (pid n w) := by
  unfold pinvFl
  rw [strictNA_eq]

theorem withFl_eq (cS : ArrCertP) (k : List Bool → Bool) : withFl n w cS k = k (pinvFl n w cS) :=
  strictLBo_eq _ _

theorem pnodeL_eq {ps : List Nat} {inX outX : Nat → Bool} {allowPW allowInX allowU : Bool}
    {cS : ArrCertP} {nodes : Array NodeP} {cN : Array ArrCertP} {wcs : Array (Array ArrCertP)}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {i : Nat}
    (hi : i < nodes.size) :
    pnodeL n w ps inX outX allowPW allowInX allowU cS nodes wcs (pinvFl n w cS) i =
      pnodeOK n w ps inX outX allowPW allowInX allowU cS nodes cN wcs i := by
  unfold pnodeL pnodeOK
  rw [strictB_eqL, ← getElem!_eq_toList_getDL, ← getElem!_eq_toList_getDL wcs, walk_eqL hc hi,
    hc i hi, pinvFl_eq]
  generalize nodes[i]! = nd
  cases nd with
  | mk b wt ch => simp only [pnodeAtL, strictLA_eq, pmaskCert_mk]

theorem pnodeL2_eq {ps : List Nat} {inX outX : Nat → Bool} {allowPW allowInX allowU : Bool}
    {cS : ArrCertP} {nodes : Array NodeP} {cN : Array ArrCertP} {wcs : Array (Array ArrCertP)}
    {pfs : Array PerfWP} (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {i : Nat}
    (hi : i < nodes.size) :
    pnodeL2 n w ps inX outX allowPW allowInX allowU cS nodes wcs pfs (pinvFl n w cS) i =
      pnodeOK2 n w ps inX outX allowPW allowInX allowU cS nodes cN wcs pfs i := by
  unfold pnodeL2 pnodeOK2
  rw [strictB_eqL, ← getElem!_eq_toList_getDL, ← getElem!_eq_toList_getDL wcs,
    ← getElem!_eq_toList_getDL pfs, walk_eqL hc hi, hc i hi, pinvFl_eq]
  generalize nodes[i]! = nd
  cases nd with
  | mk b wt ch => simp only [pnodeAtL, strictLA_eq, pmaskCert_mk]

theorem pnodeExcL_eq {ps : List Nat} {inX outX inW : Nat → Bool}
    {allowPW allowInX allowU : Bool} {cS : ArrCertP} {nodes : Array NodeP}
    {cN : Array ArrCertP} {wcs : Array (Array ArrCertP)} {e0 : Array Nat} {excs : List ExcRefP}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {i : Nat}
    (hi : i < nodes.size) :
    pnodeExcL n w ps inX outX inW allowPW allowInX allowU cS nodes cN wcs e0 excs
        (pinvFl n w cS) i =
      pnodeExcOK n w ps inX outX inW allowPW allowInX allowU cS nodes cN wcs e0 excs i := by
  unfold pnodeExcL pnodeExcOK
  rw [pnodeL_eq hc hi]
  congr 1
  unfold pexcAtL pchildrenOK
  rw [strictB_eqL, ← getElem!_eq_toList_getDL, walk_eqL hc hi, hc i hi, pinvFl_eq]
  generalize nodes[i]! = nd
  cases nd with
  | mk b wt ch => simp only [strictLA_eq, pmaskCert_mk]

theorem pcN_getElem! (nodes : Array NodeP) {j : Nat} (hj : j < nodes.size) :
    (pcN n w nodes)[j]! = pmaskCert n w nodes[j]!.basis := by
  unfold pcN
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos nodes j hj, Array.getElem_map]

theorem mapCert_getElem! (nodes : Array NodeP) {j : Nat} (hj : j < nodes.size) :
    (Array.mk (nodes.toList.map fun nd => pmaskCert n w nd.basis))[j]! =
      pmaskCert n w nodes[j]!.basis := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos nodes j hj]
  simp

end Checks

end CFSG.KC.Census
