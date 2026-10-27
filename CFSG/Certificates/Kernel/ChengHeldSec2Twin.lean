module

public import Certificates.Data.Kernel.ChengHeldSec2K

public section

namespace CFSG.KC.ChengHeldS2

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

variable {M : RegModel} {N : ℕ} {m : ℕ → ℕ → ℕ} {inv : ℕ → ℕ}

theorem all_congr' {l : List ℕ} {p q : ℕ → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem all_congr'' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem elems_eq {B : Array Bool} {f : ℕ → Bool} (hs : B.size = N) (hf : ∀ i, B[i]! = f i) :
    elems B = elemsK N f := by
  unfold elems elemsK
  rw [hs]
  exact List.filter_congr fun i _ => hf i

theorem pw_eq (hm : ∀ a b, M.m a b = m a b) (a : ℕ) : ∀ n, M.pw a n = pwK m a n
  | 0 => rfl
  | n + 1 => by
    change M.m (M.pw a n) a = m (pwK m a n) a
    rw [hm, pw_eq hm a n]

theorem cj_eq (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a) (a b : ℕ) :
    M.cj a b = cjK m inv a b := by
  unfold RegModel.cj cjK
  rw [hm, hm, hinv]

theorem cent_size' (B : Array Bool) : (M.cent B).size = M.N := by
  simp [RegModel.cent]

theorem cent_get (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) {B : Array Bool} {f : ℕ → Bool}
    (hs : B.size = N) (hf : ∀ i, B[i]! = f i) (a : ℕ) :
    (M.cent B)[a]! = (decide (a < N) && centK N m f a) := by
  unfold RegModel.cent
  by_cases ha : a < N
  · rw [getElem!_pos _ _ (by simp [hN, ha]), Array.getElem_map, Array.getElem_range]
    simp only [ha, decide_true, Bool.true_and, centK, elems_eq hs hf, hm]
  · rw [getElem!_neg _ _ (by simp [hN, ha])]
    simp [ha]

theorem elems_cent (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) {B : Array Bool} {f : ℕ → Bool}
    (hs : B.size = N) (hf : ∀ i, B[i]! = f i) : elems (M.cent B) = elemsK N (centK N m f) := by
  unfold elems elemsK
  rw [cent_size', hN]
  refine List.filter_congr fun i hi => ?_
  rw [cent_get hN hm hs hf, decide_eq_true (List.mem_range.1 hi), Bool.true_and]

theorem twM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a)
    {α k : ℕ} {A : ℕ → ℕ} {Z : ℕ → Bool} (hA : ∀ x, (autArr M α k)[x]! = A x)
    (hZ : ∀ x, (secZ M)[x]! = Z x) : twM M α k = twK N m inv A Z := by
  unfold twM twK
  simp only [hN, hm, hinv, hA, hZ]

theorem sqVM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) {V : ℕ → Bool}
    (hVs : (secV M).size = N) (hV : ∀ x, (secV M)[x]! = V x) : sqVM M = sqVK N m V := by
  unfold sqVM sqVK
  simp only [elems_eq hVs hV, elems_cent hN hm hVs hV, hm]

theorem notCentVM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b)
    (hinv : ∀ a, M.inv[a]! = inv a) {α k : ℕ} {A : ℕ → ℕ} {V : ℕ → Bool}
    (hA : ∀ x, (autArr M α k)[x]! = A x) (hVs : (secV M).size = N)
    (hV : ∀ x, (secV M)[x]! = V x) : notCentVM M α k = notCentK N m inv A V := by
  unfold notCentVM notCentK
  simp only [hN, elems_eq hVs hV, cj_eq hm hinv, hA]

theorem pairFixM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b)
    (hinv : ∀ a, M.inv[a]! = inv a) {α : ℕ} {A1 A2 : ℕ → ℕ}
    (hA1 : ∀ x, (autArr M α 0)[x]! = A1 x) (hA2 : ∀ x, (autArr M α 1)[x]! = A2 x) :
    pairFixM M α = pairFixK N m inv A1 A2 := by
  unfold pairFixM pairFixK pairCase pairCaseK pairSet fixSet1 fixSet1K
  simp only [hN, cj_eq hm hinv, hA1, hA2, hm]

theorem graphM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b)
    (hinv : ∀ a, M.inv[a]! = inv a) {A : ℕ → ℕ} {V : ℕ → Bool} {t : ℕ}
    (hA : ∀ x, (autArr M 1 1)[x]! = A x) (hVs : (secV M).size = N)
    (hV : ∀ x, (secV M)[x]! = V x) (ht : M.g 0 = t) : graphM M 1 = graphK N m inv A V t := by
  unfold graphM graphK graphCase graphCaseK graphSet inV1 inV1K
  simp only [hN, elems_eq hVs hV, elems_cent hN hm hVs hV, cj_eq hm hinv, hA, hV, hm,
    pw_eq hm, ht]
  rfl

theorem beq_bitmap {A B : Array Bool} {f g : ℕ → Bool} (hA : A.size = N) (hB : B.size = N)
    (hf : ∀ i, A[i]! = f i) (hg : ∀ i, B[i]! = g i) :
    (A == B) = (List.range N).all fun x => f x == g x := by
  rw [Bool.eq_iff_iff, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro rfl x -
    rw [← hf, ← hg, beq_self_eq_true]
  · intro h
    refine Array.ext (by rw [hA, hB]) fun i hi _ => ?_
    have := h i (List.mem_range.2 (hA ▸ hi))
    rw [← hf, ← hg, beq_iff_eq, getElem!_pos A i hi, getElem!_pos B i (hB ▸ hA ▸ hi)] at this
    exact this

theorem fixedPts_get (hN : M.N = N) (a : Array ℕ) (x : ℕ) :
    (M.fixedPts a)[x]! = (decide (x < N) && a[x]! == x) := by
  unfold RegModel.fixedPts
  by_cases hx : x < N
  · rw [getElem!_pos _ _ (by simp [hN, hx]), Array.getElem_map, Array.getElem_range]
    simp [hx]
  · rw [getElem!_neg _ _ (by simp [hN, hx])]
    simp [hx]

theorem unitFixM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) {α : ℕ} {A : ℕ → ℕ}
    {C1 C2 : ℕ → Bool} (hA : ∀ x, (autArr M α 2)[x]! = A x)
    (h1s : (M.closure [M.pw (M.g 0) 2, M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)]).size = N)
    (h1 : ∀ x, (M.closure [M.pw (M.g 0) 2,
      M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)])[x]! = C1 x)
    (h2s : (M.closure [M.pw (M.g 0) 2,
      M.m (M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)) (M.g 0)]).size = N)
    (h2 : ∀ x, (M.closure [M.pw (M.g 0) 2,
      M.m (M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)) (M.g 0)])[x]! = C2 x) :
    unitFixM M α = unitFixK N A C1 C2 := by
  have hfs : ∀ a : Array ℕ, (M.fixedPts a).size = N := fun a => by simp [RegModel.fixedPts, hN]
  unfold unitFixM unitFixK
  simp only []
  rw [beq_bitmap (hfs _) h1s (fixedPts_get hN _) h1, beq_bitmap (hfs _) h2s (fixedPts_get hN _) h2]
  congr 1 <;> refine all_congr' fun x hx => ?_ <;>
    rw [decide_eq_true (List.mem_range.1 hx), Bool.true_and, hA]

@[expose] def eaStepH (M : RegModel) (E : Array ℕ) (s : Std.HashSet ℕ × Array (Array ℕ)) (a : ℕ) :
    Std.HashSet ℕ × Array (Array ℕ) :=
  if (!(eaMask E).testBit a && E.all fun e => M.m a e == M.m e a) = true then
    if (!s.1.contains (eaMask (E ++ Array.map (fun e => M.m a e) E))) = true then
      (s.1.insert (eaMask (E ++ Array.map (fun e => M.m a e) E)),
        s.2.push (E ++ Array.map (fun e => M.m a e) E))
    else s
  else s

theorem eaNext_foldl (M : RegModel) (invs : Array ℕ) (L : Array (Array ℕ)) :
    M.eaNext invs L = (L.foldl (fun s E => invs.foldl (eaStepH M E) s) (∅, #[])).2 := by
  unfold RegModel.eaNext
  simp only [Id.run, bind_pure_comp]
  have h1 : ∀ E : Array ℕ, (fun (a : ℕ) (s : Std.HashSet ℕ × Array (Array ℕ)) =>
      if (!(eaMask E).testBit a && E.all fun e => M.m a e == M.m e a) = true then
        if (!s.1.contains (eaMask (E ++ Array.map (fun e => M.m a e) E))) = true then
          (pure (ForInStep.yield (s.1.insert (eaMask (E ++ Array.map (fun e => M.m a e) E)),
            s.2.push (E ++ Array.map (fun e => M.m a e) E))) : Id _)
        else pure (ForInStep.yield (s.1, s.2))
      else pure (ForInStep.yield (s.1, s.2))) =
      fun a s => pure (ForInStep.yield (eaStepH M E s a)) := by
    intro E
    funext a s
    unfold eaStepH
    split_ifs <;> rfl
  simp only [h1, Array.forIn_pure_yield_eq_foldl, Array.forIn_yield_eq_foldlM]
  rfl

theorem maskL_eq (E : Array ℕ) : eaMask E = maskL E.toList := by
  unfold eaMask maskL
  rw [Array.foldl_toList]

@[expose] def Rel (s : Std.HashSet ℕ × Array (Array ℕ)) (t : List ℕ × List (List ℕ)) : Prop :=
  (∀ x, s.1.contains x = t.1.contains x) ∧ s.2.toList.map Array.toList = t.2

theorem rel_step (hm : ∀ a b, M.m a b = m a b) (E : Array ℕ) {s t} (h : Rel s t) (a : ℕ) :
    Rel (eaStepH M E s a) (eaStepK m E.toList t a) := by
  obtain ⟨h1, h2⟩ := h
  have hc : (E.all fun e => M.m a e == M.m e a) = E.toList.all fun e => m a e == m e a := by
    rw [← Array.all_toList]
    simp only [hm]
  have hE : (E ++ Array.map (fun e => M.m a e) E).toList = E.toList ++ E.toList.map fun e => m a e := by
    rw [Array.toList_append, Array.toList_map]
    simp only [hm]
  unfold eaStepH eaStepK
  rw [hc, maskL_eq, maskL_eq, hE, h1]
  split_ifs
  · refine ⟨fun x => ?_, ?_⟩
    · rw [Std.HashSet.contains_insert, List.contains_cons, h1, Bool.beq_comm]
    · rw [Array.toList_push, List.map_append, h2, List.map_cons, List.map_nil, hE]
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

theorem eaNext_eq (hm : ∀ a b, M.m a b = m a b) (invs : Array ℕ) (L : Array (Array ℕ)) :
    (M.eaNext invs L).toList.map Array.toList =
      eaNextK m invs.toList (L.toList.map Array.toList) := by
  rw [eaNext_foldl, eaNextK, ← Array.foldl_toList, List.foldl_map]
  suffices key : ∀ (l : List (Array ℕ)) s t, Rel s t →
      Rel (l.foldl (fun s E => invs.foldl (eaStepH M E) s) s)
        (l.foldl (fun st E => invs.toList.foldl (eaStepK m E.toList) st) t) from
    (key L.toList (∅, #[]) ([], []) ⟨fun x => by simp, rfl⟩).2
  have inner : ∀ (E : Array ℕ) (l : List ℕ) s t, Rel s t →
      Rel (l.foldl (eaStepH M E) s) (l.foldl (eaStepK m E.toList) t) := by
    intro E l
    induction l with
    | nil => exact fun s t h => h
    | cons a l ih => exact fun s t h => ih _ _ (rel_step hm E h a)
  intro l
  induction l with
  | nil => exact fun s t h => h
  | cons E l ih =>
    intro s t h
    refine ih _ _ ?_
    dsimp only
    rw [← Array.foldl_toList]
    exact inner E _ _ _ h

theorem eaCentM_eq (hN : M.N = N) (hm : ∀ a b, M.m a b = m a b) {V : ℕ → Bool}
    (hVs : (secV M).size = N) (hV : ∀ x, (secV M)[x]! = V x) : eaCentM M = eaCentK N m V := by
  have hinvs : secInvs M = (invsK N m).toArray := by
    unfold secInvs invsK
    rw [hN]
    simp only [hm]
  have h3 : (secEA3 M).toList.map Array.toList = ea3K N m := by
    unfold secEA3 ea3K
    rw [hinvs, eaNext_eq hm, eaNext_eq hm]
    simp only [List.toList_toArray, Array.toList_map, List.map_map]
    rfl
  have hbs : ∀ E : Array ℕ, (secBitmap M E).size = N := fun E => by
    simp [secBitmap, hN]
  have hbg : ∀ (E : Array ℕ) i, (secBitmap M E)[i]! = (decide (i < N) && E.toList.contains i) := by
    intro E i
    unfold secBitmap
    by_cases hi : i < N
    · rw [getElem!_pos _ _ (by simp [hN, hi]), Array.getElem_map, Array.getElem_range]
      simp [hi]
    · rw [getElem!_neg _ _ (by simp [hN, hi])]
      simp [hi]
  unfold eaCentM eaCentK
  rw [← h3, List.all_map, ← Array.all_toList]
  refine all_congr'' fun E _ => ?_
  simp only [Function.comp, card]
  rw [beq_bitmap (hbs E) hVs (hbg E) hV]
  simp only [elems_cent hN hm (hbs E) (hbg E), pw_eq hm]

end CFSG.KC.ChengHeldS2

end
