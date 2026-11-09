module

public import Certificates.Data.Kernel.SporLatDcT
public import CFSG.Certificates.Kernel.SporLatDcPSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem allRc_eq {α : Type} (p : α → Bool) : ∀ xs : List α, allRc p xs = xs.all p
  | [] => rfl
  | a :: l => by
    rw [List.all_cons, ← allRc_eq p l]
    rfl

theorem zipAllRc_eq {α β : Type} (f : α → β → Bool) :
    ∀ (xs : List α) (ys : List β), zipAllRc f xs ys = (List.zip xs ys).all fun e => f e.1 e.2
  | [], ys => by cases ys <;> rfl
  | _ :: _, [] => rfl
  | a :: l, b :: ys => by
    rw [List.zip_cons_cons, List.all_cons, ← zipAllRc_eq f l ys]
    rfl

theorem mapRc_eq {α β : Type} (f : α → β) : ∀ xs : List α, mapRc f xs = xs.map f
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, ← mapRc_eq f l]
    rfl

theorem insORc_eq (a : Nat) : ∀ xs : List Nat, insORc a xs = insO a xs
  | [] => rfl
  | b :: l => by
    change (bif Nat.ble a b then a :: b :: l else b :: insORc a l) = insO a (b :: l)
    rw [insORc_eq a l]
    rfl

theorem insNRc_eq : ∀ xs : List Nat, insNRc xs = insN xs
  | [] => rfl
  | a :: l => by
    change insORc a (insNRc l) = insN (a :: l)
    rw [insNRc_eq l, insORc_eq]
    rfl

theorem encRc_eq (n : Nat) : ∀ xs : List Nat, encRc n xs = encodeSet n xs
  | [] => rfl
  | p :: l => by
    change Nat.add (Nat.add p 1) (Nat.mul (Nat.add n 1) (encRc n l)) = encodeSet n (p :: l)
    rw [encRc_eq n l]
    rfl

theorem encRc_fun (n : Nat) : encRc n = encodeSet n :=
  funext (encRc_eq n)

theorem incFRc_eq : ∀ (xs : List Nat) (a : Nat), incFRc a xs = incDc (a :: xs)
  | [], _ => rfl
  | b :: l, a => by
    change (Nat.blt a b && incFRc b l) = incDc (a :: b :: l)
    rw [incFRc_eq l b]
    rfl

theorem incRc_eq : ∀ xs : List Nat, incRc xs = incDc xs
  | [] => rfl
  | a :: l => incFRc_eq l a

theorem allIdxRc_eq {α : Type} (f : Nat → α → Bool) :
    ∀ (xs : List α) (c : Nat), allIdxRc f c xs = allIdx f c xs
  | [], _ => rfl
  | a :: l, c => by
    change (f c a && allIdxRc f (Nat.succ c) l) = allIdx f c (a :: l)
    rw [allIdxRc_eq f l]
    rfl

theorem eqLRc_iff : ∀ xs ys : List Nat, eqLRc xs ys = true ↔ xs = ys
  | [], [] => iff_of_true rfl rfl
  | [], _ :: _ => ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | _ :: _, [] => ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | a :: xs, b :: ys => by
    change (Nat.beq a b && eqLRc xs ys) = true ↔ _
    rw [Bool.and_eq_true, Nat.beq_eq, eqLRc_iff xs ys, List.cons.injEq]

theorem imgRc_eq (M w K p : Nat) (y : List Nat) : imgRc M w K p y = imgDc M w K p y := by
  rw [imgRc, imgDc, allRc_eq, encRc_eq]

theorem toList_getD_arr (t : Array Nat) (q : Nat) : t.toList.getD q 0 = t.getD q 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem tabTD_eq (n w : Nat) (ts : Array (Array Nat)) (pts : List (List Nat)) (P : Nat)
    (ci : List (List Nat)) : tabTD n w ts pts P ci =
    allIdx (fun l row => Nat.beq row.length pts.length &&
      (List.zip row pts).all fun e => Nat.blt e.1 pts.length &&
        Nat.beq (encodeSet n (insN (e.2.map fun p => (ts.getD l #[]).getD p 0)))
          (slotDc w P e.1)) 0 ci := by
  simp only [tabTD, allIdxRc_eq, zipAllRc_eq, encRc_eq, insNRc_eq, mapRc_eq, toList_getD_arr]

theorem insN_map_mono {f : Nat → Nat} {N : Nat} (hf : ∀ a < N, ∀ b < N, a < b → f a < f b)
    (xs : List Nat) (hx : ∀ a ∈ xs, a < N) : insN (xs.map f) = (insN xs).map f := by
  rw [insN_eq, insN_eq]
  refine (List.map_insertionSort (· ≤ ·) (· ≤ ·) f xs fun a ha b hb => ?_).symm
  have ha' := hx a ha
  have hb' := hx b hb
  constructor
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact Nat.le_of_lt (hf a ha' b hb' h)
    · exact Nat.le_refl _
  · intro h
    by_contra hc
    exact absurd h (Nat.not_le.2 (hf b hb' a ha' (Nat.lt_of_not_le hc)))

theorem map_injOn_lt {F : Nat → Nat} {N : Nat} (hF : ∀ a < N, ∀ b < N, F a = F b → a = b) :
    ∀ x y : List Nat, (∀ a ∈ x, a < N) → (∀ a ∈ y, a < N) → x.map F = y.map F → x = y
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: x, b :: y, hx, hy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hF a (hx a (by simp)) b (hy b (by simp)) h.1,
      map_injOn_lt hF x y (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc])) h.2]

theorem getD_mapT {α β : Type} (g : α → β) (l : List α) (d : α) (e : β) {k : Nat}
    (hk : k < l.length) : (l.map g).getD k e = g (l.getD k d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
    List.getElem_map]

theorem codeAT_encodeSet (n : Nat) (t : Array Nat) (p : List Nat) (hp : ∀ q ∈ p, q < n) :
    codeAT n t (encodeSet n p) = encodeSet n (insN (p.map fun q => t.getD q 0)) := by
  unfold codeAT
  rw [decodeSet_encodeSet n p hp _ (encodeSet_ge n p)]

theorem omPKo_sound {actF : Nat → List Nat → List Nat} {x0 : List Nat} {nl M w n : Nat}
    {lbl rows : List (List Nat)} {par via ord : List Nat}
    (h : omPKo actF x0 nl M w n lbl rows par via (packDc w (lbl.map (encodeSet M)))
      (rows.map (packDc w)) ord = true) :
    lbl.getD 0 [] = x0 ∧ 0 < lbl.length ∧
    (∀ l < nl, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = actF l (lbl.getD i [])) ∧
    (∀ i < lbl.length, i = 0 ∨ (par.getD i 0 < i ∧ via.getD i 0 < nl ∧
      (rows.getD (via.getD i 0) []).getD (par.getD i 0) 0 = i)) ∧
    lbl.Nodup := by
  unfold omPKo at h
  simp only [allRc_eq, zipAllRc_eq, allIdxRc_eq, incRc_eq, mapRc_eq, encRc_eq, imgRc_eq,
    Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hn⟩, hlen⟩, hw⟩, hlb⟩, hrow⟩, hpl⟩, hvl⟩, htree⟩, hol⟩, hor⟩, hinc⟩ := h
  subst hlen
  have hK : ∀ p < lbl.length, slotDc w (packDc w (lbl.map (encodeSet M))) p =
      encodeSet M (lbl.getD p []) := by
    intro p hp
    rw [slotDc_packDc w _ (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact (hlb x hx).2) p]
    rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getD_eq_getElem _ _ hp,
      List.getElem_map]
  have hmemL : ∀ p < lbl.length, ∀ a ∈ lbl.getD p [], a < M := by
    intro p hp a ha
    rw [List.getD_eq_getElem _ _ hp] at ha
    exact (hlb _ (List.getElem_mem hp)).1 a ha
  have hact : ∀ l < nl, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = actF l (lbl.getD i []) := by
    intro l hl i hi
    obtain ⟨hrl, hz⟩ := hrow l hl
    have e := zipAllDc (d := 0) (e := []) hz hrl i hi
    beta_reduce at e
    simp only [Bool.and_eq_true, Nat.blt_eq, imgDc, Nat.beq_eq, List.all_eq_true] at e
    obtain ⟨hp, hy, hs⟩ := e
    refine ⟨hp, encodeSet_inj M _ _ (hmemL _ hp) hy ?_⟩
    rw [← hK _ hp, hs]
  have hrowB : ∀ l < nl, ∀ a ∈ rows.getD l [], a < 2 ^ w := by
    intro l hl a ha
    obtain ⟨hrl, hz⟩ := hrow l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have e := zipAllDc (d := 0) (e := []) hz hrl i (by omega)
    beta_reduce at e
    rw [List.getD_eq_getElem _ _ hi] at e
    exact Nat.lt_trans e.1 hw
  refine ⟨?_, hn, hact, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hn, ← h0]
    cases lbl with
    | nil => simp at hn
    | cons a l => rfl
  · intro i hi
    have hzl : (List.zip par via).length = lbl.length := by simp [hpl, hvl]
    have e := (allIdx_iff _ 0 _).1 htree i (by omega)
    rw [List.getElem_zip, Nat.zero_add] at e
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    rcases e with e | ⟨⟨e1, e2⟩, e3⟩
    · exact Or.inl e
    · refine Or.inr ⟨e1, e2, ?_⟩
      have eR : (rows.map (packDc w)).getD via[i] 0 = packDc w (rows.getD via[i] []) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases rows[via[i]]? <;> rfl
      rw [eR, slotDc_packDc w _ (hrowB _ e2)] at e3
      exact e3
  · set key := slotDc w (packDc w (lbl.map (encodeSet M))) with hkey
    have hon : ord.Nodup := List.Nodup.of_map key
      ((incDc_pairwise _ hinc).imp fun h => Nat.ne_of_lt h)
    have hsub : ord ⊆ List.range lbl.length := fun i hi => List.mem_range.2 (hor i hi)
    have hperm : ord.Perm (List.range lbl.length) :=
      (hon.subperm hsub).perm_of_length_le (by simp [hol])
    have hnk : ((List.range lbl.length).map key).Nodup :=
      (hperm.map key).nodup_iff.1 ((incDc_pairwise _ hinc).imp fun h => Nat.ne_of_lt h)
    have heq : (List.range lbl.length).map key = lbl.map (encodeSet M) := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      have hi : i < lbl.length := by simpa using h1
      rw [hK i hi, List.getD_eq_getElem _ _ hi]
    rw [heq] at hnk
    exact List.Nodup.of_map _ hnk

theorem omTK_sound {n w wi : Nat} {ts : Array (Array Nat)} {x0 : List Nat}
    {pts ci li lbl rows : List (List Nat)} {par via ord : List Nat}
    (h : omTK n w wi ts x0 pts ci li ord lbl rows par via (packDc w (pts.map (encodeSet n)))
      (ci.map (packDc wi)) = true) :
    lbl.getD 0 [] = x0 ∧ 0 < lbl.length ∧
    (∀ l < ts.size, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = codeSetT n (ts.getD l #[]) (lbl.getD i [])) ∧
    (∀ i < lbl.length, i = 0 ∨ (par.getD i 0 < i ∧ via.getD i 0 < ts.size ∧
      (rows.getD (via.getD i 0) []).getD (par.getD i 0) 0 = i)) ∧
    lbl.Nodup := by
  unfold omTK at h
  simp only [allRc_eq, zipAllRc_eq, incRc_eq, mapRc_eq, encRc_fun, insNRc_eq, eqLRc_iff,
    Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpts, hinc⟩, hcw⟩, hwi⟩, hcil⟩, htab⟩, h0⟩, hll⟩, htie⟩, hpk⟩ := h
  rw [tabTD_eq] at htab
  obtain ⟨-, hn, hact, htree, hnd⟩ := omPKo_sound hpk
  set N := pts.length with hN
  set cs := pts.map (encodeSet n) with hcs
  set F : Nat → Nat := fun k => cs.getD k 0 with hF
  have hPf : slotDc w (packDc w cs) = F := funext (slotDc_packDc w cs hcw)
  have hmono : ∀ a < N, ∀ b < N, a < b → F a < F b := by
    intro a ha b hb hab
    have hp := List.pairwise_iff_getElem.1 (incDc_pairwise _ hinc) a b
      (by simpa [hcs] using ha) (by simpa [hcs] using hb) hab
    simp only [hF]
    rw [List.getD_eq_getElem _ _ (by simpa [hcs] using ha),
      List.getD_eq_getElem _ _ (by simpa [hcs] using hb)]
    exact hp
  have hinj : ∀ a < N, ∀ b < N, F a = F b → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e (Nat.ne_of_lt (hmono a ha b hb h))
    · exact h
    · exact absurd e (Nat.ne_of_gt (hmono b hb a ha h))
  have htab' : ∀ l < ts.size, ∀ k < N, (ci.getD l []).getD k 0 < N ∧
      codeAT n (ts.getD l #[]) (F k) = F ((ci.getD l []).getD k 0) := by
    intro l hl k hk
    have hl' : l < ci.length := by omega
    have e := (allIdx_iff _ 0 ci).1 htab l hl'
    simp only [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at e
    obtain ⟨erl, ez⟩ := e
    have e2 := zipAllDc (d := 0) (e := []) ez erl k hk
    beta_reduce at e2
    rw [← List.getD_eq_getElem ci [] hl'] at e2
    obtain ⟨e3, e4⟩ := e2
    refine ⟨e3, ?_⟩
    have hpk : ∀ q ∈ pts.getD k [], q < n := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hpts _ (List.getElem_mem hk)
    have hFk : F k = encodeSet n (pts.getD k []) := getD_mapT _ pts [] 0 hk
    rw [hFk, codeAT_encodeSet n _ _ hpk, e4, hPf]
  have hCI : ∀ l < ts.size, slotDc wi ((ci.map (packDc wi)).getD l 0) =
      fun k => (ci.getD l []).getD k 0 := by
    intro l hl
    have hl' : l < ci.length := by omega
    have hrl : (ci.getD l []).length = N := by
      have e := (allIdx_iff _ 0 ci).1 htab l hl'
      simp only [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq] at e
      rw [List.getD_eq_getElem _ _ hl']
      exact e.1
    rw [getD_mapT _ ci [] 0 hl']
    refine funext (slotDc_packDc wi _ fun a ha => ?_)
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
    have hk2 := (htab' l hl k (by omega)).1
    rw [List.getD_eq_getElem _ _ hk] at hk2
    exact Nat.lt_of_lt_of_le hk2 hwi
  have hlt : ∀ i < li.length, ∀ q ∈ li.getD i [], q < N := fun i hi =>
    (zipAllDc (d := []) (e := []) htie hll i (by omega)).1
  have hlbl : ∀ i < lbl.length, lbl.getD i [] = (li.getD i []).map F := by
    intro i hi
    have e := (zipAllDc (d := []) (e := []) htie hll i hi).2
    rw [hPf] at e
    exact e.symm
  have hmemli : ∀ x ∈ li, ∀ q ∈ x, q < N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [← List.getD_eq_getElem li [] hi]
    exact hlt i hi
  have hlblEq : lbl = li.map (List.map F) := by
    refine List.ext_getElem (by simp [hll]) fun i h1 h2 => ?_
    rw [← List.getD_eq_getElem lbl [] h1, hlbl i h1, List.getElem_map,
      List.getD_eq_getElem li [] (by simpa using h2)]
  refine ⟨?_, by omega, fun l hl i hi => ?_, fun i hi => htree i (by omega), ?_⟩
  · rw [← h0]
    cases lbl with
    | nil =>
      simp only [List.length_nil, List.length_eq_zero_iff] at hll
      simp [hll] at hn
    | cons a l => rfl
  · have hi' : i < li.length := by omega
    obtain ⟨hr, he⟩ := hact l hl i hi'
    refine ⟨by omega, ?_⟩
    rw [hlbl ((rows.getD l []).getD i 0) (by omega), hlbl i hi, he, hCI l hl]
    have hx := hlt i hi'
    have hcx : ∀ a ∈ (li.getD i []).map (fun k => (ci.getD l []).getD k 0), a < N := by
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
      exact (htab' l hl k (hx k hk)).1
    rw [← insN_map_mono hmono _ hcx, List.map_map]
    change _ = insN (((li.getD i []).map F).map (codeAT n (ts.getD l #[])))
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact ((htab' l hl k (hx k hk)).2).symm
  · rw [hlblEq]
    exact List.Nodup.map_on (fun x hx y hy e => map_injOn_lt hinj x y (hmemli x hx)
      (hmemli y hy) e) hnd

theorem omOKT_omOKG {n w wi : Nat} {ts : Array (Array Nat)} {x0 : List Nat}
    {pts ci li : List (List Nat)} {ord : List Nat} {O : OmegaData (List Nat)}
    (h : omOKT n w wi ts x0 pts ci li ord O = true) :
    omOKG (fun l x => codeSetT n (ts.getD l #[]) x) x0 ts.size O = true := by
  obtain ⟨h0, hn, hact, htree, hnd⟩ := omTK_sound h
  have eR : ∀ l, ((O.pn.toList.map Array.toList).getD l []) =
      (O.pn.toList.getD l default).toList := by
    intro l
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases O.pn.toList[l]? <;> rfl
  simp only [eR] at hact htree
  rw [← omOKL_eq]
  unfold omOKL
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨h0, hn⟩, fun l hl i hi => ⟨(hact l hl i hi).1, (hact l hl i hi).2⟩⟩,
    fun i hi => ?_⟩, hnd⟩
  rcases htree i hi with e | ⟨e1, e2, e3⟩
  · exact Or.inl e
  · exact Or.inr ⟨⟨e1, e2⟩, e3⟩

theorem omCodeT_sound {n w wi : ℕ} {ts : Array (Array ℕ)} {x0 : List ℕ}
    {pts ci li : List (List ℕ)} {ord : List ℕ} {O : OmegaData (List ℕ)}
    (h : omOKT n w wi ts x0 pts ci li ord O = true) : OmegaSpec (codeSetAct n) ts x0 O :=
  omCode_sound (omOKT_omOKG h)

end CFSG.KC.SLDc

end
