module

public import Certificates.Data.Kernel.SporLatDcTup
import CFSG.Certificates.Kernel.LocalQTBaseWProved
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat

section Tup

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

omit [Inhabited Lab] in
theorem nodup_of_distinctB {a : Array Lab} (h : distinctB a = true) : a.toList.Nodup := by
  have key : ∀ (l : List Lab) (f : Bool) (S : Std.HashSet Lab),
      (l.foldl (fun (acc : Bool × Std.HashSet Lab) x =>
        if acc.2.contains x then (false, acc.2) else (acc.1, acc.2.insert x)) (f, S)).1 = true →
      f = true ∧ l.Nodup ∧ ∀ x ∈ l, S.contains x = false := by
    intro l
    induction l with
    | nil => intro f S h; simpa using h
    | cons x l ih =>
      intro f S h
      rw [List.foldl_cons] at h
      by_cases hx : S.contains x = true
      · simp only [hx, if_true] at h
        exact absurd (ih false S h).1 (by decide)
      · simp only [hx, Bool.false_eq_true, if_false] at h
        obtain ⟨hf, hnd, hS⟩ := ih f _ h
        have hS' : ∀ y ∈ l, x ≠ y ∧ S.contains y = false := by
          intro y hy
          have e := hS y hy
          rw [Std.HashSet.contains_insert] at e
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at e
          exact e
        refine ⟨hf, List.nodup_cons.2 ⟨fun hm => (hS' x hm).1 rfl, hnd⟩, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · simpa using hx
        · exact (hS' y hy).2
  unfold distinctB at h
  rw [← Array.foldl_toList] at h
  exact (key _ _ _ h).2.1

theorem otIdxOK_sound {act : Array Nat → Lab → Lab} {letters sl : Array (Array Nat)} {Δ : Lab}
    {Om : OmegaData Lab} (hOm : OmegaSpec act letters Δ Om)
    (hsl : ∀ l < sl.size, l < letters.size ∧ letters[l]! = sl[l]!)
    {w : Nat} {Ps : List Nat} (hPs : Ps.length = sl.size)
    (hP : ∀ l < sl.size, ∀ k < Om.lbl.size,
      CFSG.KC.LQT.PW.imgW w (Ps.getD l 0) k = (Om.pn[l]!)[k]!)
    {O : OmegaData (List Nat)} (h : otIdxOK w Om.lbl.size Ps O = true) :
    OmegaSpec (tupAct act) sl Om.lbl.toList (tupLbl Om O) := by
  obtain ⟨_, _, hOpn, _, hOd⟩ := hOm
  unfold otIdxOK omOKG at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, hpos⟩, hpn⟩, htree⟩, hnd⟩ := h
  set m := Om.lbl.size
  set f : Nat → Lab := fun k => Om.lbl[k]!
  set g : List Nat → List Lab := fun t => t.map f
  have hpn' : ∀ l < sl.size, ∀ i < O.lbl.size,
      (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = tupW w (Ps.getD l 0) O.lbl[i]! := by
    intro l hl i hi
    have e := List.all_eq_true.1 (List.all_eq_true.1 hpn l (List.mem_range.2 (hPs ▸ hl))) i
      (List.mem_range.2 hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using e
  have htree' : ∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < sl.size ∧
      (O.pn[O.via[i]!]!)[O.par[i]!]! = i := by
    intro i hi hi0
    have e := List.all_eq_true.1 htree i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at e
    rcases e with e | ⟨⟨e1, e2⟩, e3⟩
    · omega
    · exact ⟨e1, hPs ▸ e2, e3⟩
  have hrow : ∀ l < sl.size, ∀ t : List Nat, (∀ k ∈ t, k < m) →
      tupW w (Ps.getD l 0) t = t.map (fun k => (Om.pn[l]!)[k]!) := by
    intro l hl t ht
    exact List.map_congr_left fun k hk => hP l hl k (ht k hk)
  have hlt : ∀ l < sl.size, ∀ k < m, (Om.pn[l]!)[k]! < m := fun l hl k hk =>
    (hOpn l (hsl l hl).1 k hk).1
  have hI : ∀ i < O.lbl.size, ∀ k ∈ O.lbl[i]!, k < m := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi k hk
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0] at hk
        exact List.mem_range.1 hk
      · obtain ⟨hp, hv, he⟩ := htree' i hi hi0
        have h1 := hpn' _ hv O.par[i]! (by omega)
        rw [he] at h1
        rw [h1.2, hrow _ hv _ (ih _ hp (by omega))] at hk
        obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
        exact hlt _ hv _ (ih _ hp (by omega) k' hk')
  have hget : ∀ i < O.lbl.size, (tupLbl Om O).lbl[i]! = g O.lbl[i]! := by
    intro i hi
    change (O.lbl.map g)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos _ i hi]
  have hsz : (tupLbl Om O).lbl.size = O.lbl.size := Array.size_map ..
  have hinj : ∀ a < m, ∀ b < m, f a = f b → a = b := by
    intro a ha b hb e
    have hn := nodup_of_distinctB hOd
    change Om.lbl[a]! = Om.lbl[b]! at e
    rw [getElem!_pos _ a ha, getElem!_pos _ b hb] at e
    have e' : Om.lbl.toList[a]'(by simpa using ha) = Om.lbl.toList[b]'(by simpa using hb) := by
      simpa using e
    exact (List.Nodup.getElem_inj_iff hn).1 e'
  refine ⟨?_, by rw [hsz]; exact hpos, fun l hl i hi => ?_, fun i hi hi0 => ?_, ?_⟩
  · rw [hget 0 hpos, h0]
    apply List.ext_getElem (by simp [g, m])
    intro n h1 h2
    simp only [g, f, List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [getElem!_pos _ n (by simpa [g, m] using h1)]
  · rw [hsz] at hi ⊢
    have hl' := hpn' l hl i hi
    refine ⟨hl'.1, ?_⟩
    change (tupLbl Om O).lbl[(O.pn[l]!)[i]!]! = tupAct act sl[l]! ((tupLbl Om O).lbl[i]!)
    rw [hget _ hl'.1, hget i hi, hl'.2, hrow l hl _ (hI i hi)]
    unfold tupAct
    simp only [g, List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk' := hI i hi k hk
    simp only [Function.comp, f]
    rw [(hOpn l (hsl l hl).1 k hk').2, (hsl l hl).2]
  · rw [hsz] at hi
    exact htree' i hi hi0
  · apply CFSG.Quasithin.GoldD3.distinctB_of_nodup
    change (O.lbl.map g).toList.Nodup
    rw [Array.toList_map]
    have hmem : ∀ x ∈ O.lbl.toList, ∀ k ∈ x, k < m := by
      intro x hx k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      have hi' : i < O.lbl.size := by simpa using hi
      have e := hI i hi'
      rw [getElem!_pos _ i hi'] at e
      exact e k (by simpa using hk)
    have hginj : ∀ x : List Nat, (∀ k ∈ x, k < m) → ∀ y : List Nat, (∀ k ∈ y, k < m) →
        x.map f = y.map f → x = y := by
      intro x
      induction x with
      | nil =>
        intro _ y _ e
        rw [List.map_nil, eq_comm, List.map_eq_nil_iff] at e
        exact e.symm
      | cons a x ih =>
        intro hx y hy e
        cases y with
        | nil => simp at e
        | cons b y =>
          simp only [List.map_cons, List.cons.injEq] at e
          rw [hinj a (hx a (by simp)) b (hy b (by simp)) e.1,
            ih (fun k hk => hx k (by simp [hk])) y (fun k hk => hy k (by simp [hk])) e.2]
    exact List.Nodup.map_on (fun x hx y hy e => hginj x (hmem x hx) y (hmem y hy) e) hnd

theorem codeK_rows {w : Nat} {rows : List (List Nat)} {m : Nat}
    (h : ∀ r ∈ rows, ∀ x ∈ r, x < 2 ^ w) (hm : ∀ r ∈ rows, m ≤ r.length) :
    ∀ l < rows.length, ∀ k < m, CFSG.KC.LQT.PW.imgW w ((rows.map (CFSG.KC.LQT.PP.codeK w)).getD l 0) k =
      (rows.getD l []).getD k 0 := by
  intro l hl k hk
  have hr := List.getElem_mem hl
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl]
  exact CFSG.KC.LQT.BW.Pf.imgW_codeK _ (h _ hr) k (by have := hm _ hr; omega)

end Tup

end CFSG.KC.SLDc

end
