module

public import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KS.BfsMap

open CFSG.PSL3Four.Native CFSG.KS.BfsReplay

theorem forIn_sim {β γ : Type} (l : List Nat) (f₁ : Nat → β → Id (ForInStep β))
    (f₂ : Nat → γ → Id (ForInStep γ)) (R : β → γ → Prop)
    (h : ∀ a ∈ l, ∀ b c, R b c →
      (∃ b' c', f₁ a b = pure (ForInStep.yield b') ∧ f₂ a c = pure (ForInStep.yield c') ∧
        R b' c') ∨
      (∃ b' c', f₁ a b = pure (ForInStep.done b') ∧ f₂ a c = pure (ForInStep.done c') ∧ R b' c'))
    (b : β) (c : γ) (hR : R b c) : R (Id.run (forIn l b f₁)) (Id.run (forIn l c f₂)) := by
  induction l generalizing b c with
  | nil => simpa using hR
  | cons a l ih =>
    rw [List.forIn_cons, List.forIn_cons]
    rcases h a List.mem_cons_self b c hR with ⟨b', c', h1, h2, hR'⟩ | ⟨b', c', h1, h2, hR'⟩
    · rw [h1, h2]
      simpa using ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) b' c' hR'
    · rw [h1, h2]
      simpa using hR'

structure MapHyp (step step' : Nat → Tab → Tab) (k : Nat) (r r' : Tab) (f : Tab → Tab)
    (X : Tab → Prop) : Prop where
  root : f r = r'
  mem_root : X r
  mem_step : ∀ j < k, ∀ t, X t → X (step j t)
  map_step : ∀ j < k, ∀ t, X t → f (step j t) = step' j (f t)
  inj : ∀ a b, X a → X b → f a = f b → a = b

@[expose] def Rel (f : Tab → Tab) (X : Tab → Prop) (s s' : St) : Prop :=
  s'.1 = s.1.map f ∧ s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 ∧ (∀ x ∈ s.1, X x) ∧
    (∀ x, s.2.2.2.contains x = true ↔ x ∈ s.1) ∧ (∀ x, s'.2.2.2.contains x = true ↔ x ∈ s'.1)

theorem get_map {f : Tab → Tab} {a : Array Tab} {i : Nat} (hi : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem get_mem {X : Tab → Prop} {a : Array Tab} (hX : ∀ x ∈ a, X x) {i : Nat} (hi : i < a.size) :
    X a[i]! := by
  rw [getElem!_pos a i hi]
  exact hX _ (Array.getElem_mem hi)

section

variable {step step' : Nat → Tab → Tab} {k : Nat} {r r' : Tab} {f : Tab → Tab} {X : Tab → Prop}

theorem contains_push {m : Std.HashMap Tab Nat} {a : Array Tab} (hK : ∀ x, m.contains x = true ↔ x ∈ a)
    (y : Tab) (v : Nat) : ∀ x, (m.insert y v).contains x = true ↔ x ∈ a.push y := by
  intro x
  rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hK, Array.mem_push]
  exact ⟨fun h => h.elim (fun e => Or.inr e.symm) Or.inl,
    fun h => h.elim Or.inr (fun e => Or.inl e.symm)⟩

theorem inner_sim (H : MapHyp step step' k r r' f X) {t : Tab} (ht : X t) (h : Nat) {j : Nat}
    (hj : j < k) {s s' : St} (hR : Rel f X s s') :
    ∃ b c, innerBody step t h j s = pure (ForInStep.yield b) ∧
      innerBody step' (f t) h j s' = pure (ForInStep.yield c) ∧ Rel f X b c := by
  obtain ⟨e1, e2, e3, hX, hK, hK'⟩ := hR
  have hx := H.mem_step j hj t ht
  have hmap := H.map_step j hj t ht
  have hc : s'.2.2.2.contains (step' j (f t)) = s.2.2.2.contains (step j t) := by
    rw [← hmap]
    apply Bool.eq_iff_iff.2
    rw [hK', hK, e1, Array.mem_map]
    constructor
    · rintro ⟨y, hy, e⟩
      rwa [H.inj y _ (hX y hy) hx e] at hy
    · intro hm
      exact ⟨_, hm, rfl⟩
  by_cases hn : s.2.2.2.contains (step j t) = true
  · have hn' : s'.2.2.2.contains (step' j (f t)) = true := hc.trans hn
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2),
      by simp [innerBody, hn], by simp [innerBody, hn'], e1, e2, e3, hX, hK, hK'⟩
  · have hn1 : s.2.2.2.contains (step j t) = false := by simpa using hn
    have hn' : s'.2.2.2.contains (step' j (f t)) = false := hc.trans hn1
    refine ⟨(s.1.push (step j t), s.2.1.push h, s.2.2.1.push j, s.2.2.2.insert (step j t) s.1.size),
      (s'.1.push (step' j (f t)), s'.2.1.push h, s'.2.2.1.push j,
        s'.2.2.2.insert (step' j (f t)) s'.1.size),
      by simp [innerBody, hn1], by simp [innerBody, hn'], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change s'.1.push (step' j (f t)) = (s.1.push (step j t)).map f
      rw [e1, Array.map_push, hmap]
    · change s'.2.1.push h = s.2.1.push h
      rw [e2]
    · change s'.2.2.1.push j = s.2.2.1.push j
      rw [e3]
    · intro x hm
      rcases Array.mem_push.1 hm with hm | e
      · exact hX x hm
      · exact e ▸ hx
    · exact contains_push hK _ _
    · exact contains_push hK' _ _

theorem inner_loop_sim (H : MapHyp step step' k r r' f X) {s s' : St} (hR : Rel f X s s') {h : Nat}
    (hh : h < s.1.size) :
    Rel f X (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerBody step s.1[h]! h)))
      (Id.run (forIn (List.range' 0 k) (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2)
        (innerBody step' s'.1[h]! h))) := by
  have ht : X s.1[h]! := get_mem hR.2.2.2.1 hh
  have e : s'.1[h]! = f s.1[h]! := by rw [hR.1]; exact get_map hh
  rw [e]
  refine forIn_sim _ _ _ (Rel f X) (fun j hj b c hbc => Or.inl ?_) _ _ hR
  exact inner_sim H ht h (by rw [List.mem_range'_1] at hj; omega) hbc

theorem outer_sim (H : MapHyp step step' k r r' f X) (h : Nat) {s s' : St} (hR : Rel f X s s') :
    (∃ b c, outerBody step k h s = pure (ForInStep.yield b) ∧
      outerBody step' k h s' = pure (ForInStep.yield c) ∧ Rel f X b c) ∨
    (∃ b c, outerBody step k h s = pure (ForInStep.done b) ∧
      outerBody step' k h s' = pure (ForInStep.done c) ∧ Rel f X b c) := by
  have hsz : s'.1.size = s.1.size := by rw [hR.1, Array.size_map]
  by_cases hh : h < s.1.size
  · exact Or.inl ⟨_, _, by simp [outerBody, hh], by simp [outerBody, hsz, hh],
      inner_loop_sim H hR hh⟩
  · exact Or.inr ⟨_, _, by simp [outerBody, hh], by simp [outerBody, hsz, hh], hR⟩

theorem init_rel (H : MapHyp step step' k r r' f X) (cap : Nat) :
    Rel f X (initSt r cap) (initSt r' cap) := by
  refine ⟨by simp [initSt, H.root], rfl, rfl, fun x hx => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [initSt, Array.mem_singleton] at hx
    exact hx ▸ H.mem_root
  · simp only [initSt]
    rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
      beq_iff_eq, Array.mem_singleton]
    exact eq_comm
  · simp only [initSt]
    rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
      beq_iff_eq, Array.mem_singleton]
    exact eq_comm

theorem bfs_map (H : MapHyp step step' k r r' f X) (cap : Nat) :
    (bfs step' k r' cap).tabs = (bfs step k r cap).tabs.map f ∧
      (bfs step' k r' cap).par = (bfs step k r cap).par ∧
      (bfs step' k r' cap).lab = (bfs step k r cap).lab ∧ ∀ x ∈ (bfs step k r cap).tabs, X x := by
  have hR := forIn_sim (List.range' 0 cap) (outerBody step k) (outerBody step' k) (Rel f X)
    (fun h _ b c hbc => outer_sim H h hbc) (initSt r cap) (initSt r' cap) (init_rel H cap)
  rw [bfs_eq, bfs_eq]
  exact ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1⟩

end

theorem treeOK_iff {step : Nat → Tab → Tab} {k : Nat} {root : Tab} {E : Enum} :
    treeOK step k root E = true ↔ 0 < E.tabs.size ∧ E.tabs[0]! = root ∧
      (∀ a < E.tabs.size, ∀ b < E.tabs.size, E.tabs[a]! = E.tabs[b]! → a = b) ∧
      ∀ i < E.tabs.size, (∀ j < k, step j E.tabs[i]! ∈ E.tabs) ∧
        (i = 0 ∨ (E.par[i]! < i ∧ E.lab[i]! < k ∧ E.tabs[i]! = step E.lab[i]! E.tabs[E.par[i]!]!)) := by
  unfold treeOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_iff, Bool.or_eq_true]
  generalize E.tabs = A
  have hfound : ∀ x, found (indexOf A) A x = true → x ∈ A := fun x hx => by
    unfold found at hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    rw [← hx.2, getElem!_pos A _ hx.1]
    exact Array.getElem_mem hx.1
  constructor
  · rintro ⟨⟨h0, hr⟩, hall⟩
    have hinj : ∀ a < A.size, ∀ b < A.size, A[a]! = A[b]! → a = b := fun a ha b hb e => by
      have h1 := (hall a ha).1.1
      have h2 := (hall b hb).1.1
      rw [e] at h1
      exact h1.symm.trans h2
    refine ⟨h0, hr, hinj, fun i hi => ⟨fun j hj => hfound _ ((hall i hi).1.2 j hj),
      (hall i hi).2.imp_right and_assoc.1⟩⟩
  · rintro ⟨h0, hr, hinj, hall⟩
    obtain ⟨hi1, -⟩ := indexOf_spec hinj
    refine ⟨⟨h0, hr⟩, fun i hi => ⟨⟨hi1 i hi, fun j hj => ?_⟩, (hall i hi).2.imp_right and_assoc.2⟩⟩
    obtain ⟨m, hm, e⟩ := Array.mem_iff_getElem.1 ((hall i hi).1 j hj)
    have em : A[m]! = step j A[i]! := by rw [getElem!_pos A m hm]; exact e
    unfold found posOf
    rw [← em, hi1 m hm]
    simp [hm]

theorem treeOK_map {step step' : Nat → Tab → Tab} {k : Nat} {r r' : Tab} {f : Tab → Tab}
    {X : Tab → Prop} (H : MapHyp step step' k r r' f X) {E E' : Enum}
    (ht : E'.tabs = E.tabs.map f) (hp : E'.par = E.par) (hl : E'.lab = E.lab)
    (hX : ∀ x ∈ E.tabs, X x) (h : treeOK step' k r' E' = true) : treeOK step k r E = true := by
  rw [treeOK_iff] at h ⊢
  rw [ht, hp, hl, Array.size_map] at h
  obtain ⟨h0, hr, hinj, hall⟩ := h
  have g : ∀ i < E.tabs.size, (E.tabs.map f)[i]! = f E.tabs[i]! := fun i hi => get_map hi
  have m : ∀ i < E.tabs.size, X E.tabs[i]! := fun i hi => get_mem hX hi
  refine ⟨h0, ?_, fun a ha b hb e => hinj a ha b hb (by rw [g a ha, g b hb, e]),
    fun i hi => ⟨fun j hj => ?_, ?_⟩⟩
  · refine H.inj _ _ (m 0 h0) H.mem_root ?_
    rw [← g 0 h0, hr, H.root]
  · have hs := (hall i hi).1 j hj
    rw [g i hi, ← H.map_step j hj _ (m i hi), Array.mem_map] at hs
    obtain ⟨y, hy, e⟩ := hs
    rwa [H.inj y _ (hX y hy) (H.mem_step j hj _ (m i hi)) e] at hy
  · rcases (hall i hi).2 with h0' | ⟨a1, a2, a3⟩
    · exact Or.inl h0'
    · refine Or.inr ⟨a1, a2, H.inj _ _ (m i hi) (H.mem_step _ a2 _ (m _ (by omega))) ?_⟩
      rw [← g i hi, a3, g _ (by omega), H.map_step _ a2 _ (m _ (by omega))]

theorem enumBFS_map {n m : Nat} {gens gens' : Array Tab} {f : Tab → Tab} {X : Tab → Prop}
    (hsz : gens'.size = gens.size)
    (H : MapHyp (leftStep n gens) (leftStep m gens') gens.size (idTab n) (idTab m) f X) (cap : Nat)
    (h : enumOK m gens' (enumBFS m gens' cap) = true) :
    enumOK n gens (enumBFS n gens cap) = true ∧
      (enumBFS n gens cap).tabs.size = (enumBFS m gens' cap).tabs.size := by
  unfold enumOK enumBFS at h ⊢
  rw [hsz] at h ⊢
  obtain ⟨ht, hp, hl, hX⟩ := bfs_map H cap
  exact ⟨treeOK_map H ht hp hl hX h, by rw [ht, Array.size_map]⟩

end CFSG.KS.BfsMap

end
