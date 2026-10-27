module

public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.E68Spor.Chk
public import CFSG.Certificates.Kernel.E64FSound
import Init.Internal.Order.While
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer

public section

namespace CFSG.KC.SLOm

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F CFSG.Quasithin.E6.Spor

section Twin

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

abbrev St5 (Lab : Type) [BEq Lab] [Hashable Lab] :=
  Array Lab × Std.HashMap Lab Nat × Array Nat × Array Nat × Array (Array Nat)

abbrev St6 (Lab : Type) [BEq Lab] [Hashable Lab] :=
  Array Lab × Std.HashMap Lab Nat × Array Nat × Array Nat × Array (Array Nat) × Nat

@[expose] def stepF (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (L : Lab)
    (i l : Nat) (t : St5 Lab) : Id (ForInStep (St5 Lab)) :=
  match t.2.1.get? (act letters[l]! L) with
  | some j => pure (.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.modify l fun a => a.push j))
  | none => pure (.yield (t.1.push (act letters[l]! L), t.2.1.insert (act letters[l]! L) t.1.size,
      t.2.2.1.push i, t.2.2.2.1.push l, t.2.2.2.2.modify l fun a => a.push t.1.size))

@[expose] def bodyF (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (cap : Nat)
    (s : St6 Lab) : Id (ForInStep (St6 Lab)) :=
  if (decide (s.2.2.2.2.2 < s.1.size) && decide (s.1.size ≤ cap)) = true then
    let t := Id.run (forIn (List.range' 0 letters.size) (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1)
      (stepF act letters s.1[s.2.2.2.2.2]! s.2.2.2.2.2))
    pure (.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

@[expose] def outF (s : St6 Lab) : OmegaData Lab × Bool :=
  (⟨s.1, s.2.2.2.2.1, s.2.2.1, s.2.2.2.1⟩, s.2.2.2.2.2 == s.1.size)

theorem buildOmega_eq (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (Δ : Lab)
    (cap : Nat) : buildOmega act letters Δ cap =
      outF (forIn (m := Id) Lean.Loop.mk (#[Δ], (∅ : Std.HashMap Lab Nat).insert Δ 0, #[0], #[0],
        Array.replicate letters.size #[], 0) (fun _ s => bodyF act letters cap s)) := by
  unfold buildOmega
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem forIn_loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

theorem idxL_append (x M : Lab) : ∀ l : List Lab, idxL x (l ++ [M]) =
    match idxL x l with
    | some j => some j
    | none => if x = M then some l.length else none
  | [] => by
    by_cases h : x = M
    · simp [idxL, h]
    · simp [idxL, h]
  | y :: l => by
    by_cases h : x = y
    · simp [idxL, h]
    · simp only [List.cons_append, idxL, h, ↓reduceIte, idxL_append x M l, List.length_cons]
      cases idxL x l with
      | some j => rfl
      | none =>
        by_cases hM : x = M
        · simp [hM]
        · simp [hM]

def Rel5 (t : St5 Lab) (s : St4 Lab) : Prop :=
  t.1 = s.1 ∧ t.2.2.1 = s.2.1 ∧ t.2.2.2.1 = s.2.2.1 ∧ t.2.2.2.2 = s.2.2.2 ∧
    ∀ x, t.2.1[x]? = idxL x s.1.toList

theorem rel5_step {act : Array Nat → Lab → Lab} {letters : Array (Array Nat)}
    {actF : Nat → Lab → Lab} {P : Lab → Prop} {L : Lab} {i l : Nat} {t : St5 Lab} {s : St4 Lab}
    (hL : P L) (hl : l < letters.size)
    (hcl : ∀ l < letters.size, ∀ x, P x → P (actF l x) ∧ act letters[l]! x = actF l x)
    (R : Rel5 t s) (hP : ∀ x ∈ s.1.toList, P x) :
    ∃ t', stepF act letters L i l t = pure (.yield t') ∧ Rel5 t' (omStep actF L i s l) ∧
      ∀ x ∈ (omStep actF L i s l).1.toList, P x := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := R
  obtain ⟨hPM, hM⟩ := hcl l hl L hL
  have hg : t.2.1.get? (act letters[l]! L) = idxL (actF l L) s.1.toList := by
    rw [Std.HashMap.get?_eq_getElem?, r5, hM]
  unfold stepF omStep
  rw [hg, hM]
  cases hj : idxL (actF l L) s.1.toList with
  | some j =>
    refine ⟨_, rfl, ⟨r1, r2, r3, by rw [r4], r5⟩, hP⟩
  | none =>
    refine ⟨_, rfl, ⟨by rw [r1], by rw [r2], by rw [r3], by rw [r4, r1], fun x => ?_⟩, ?_⟩
    · rw [Std.HashMap.getElem?_insert, Array.toList_push, idxL_append, ← r5 x, r1]
      by_cases hx : actF l L = x
      · subst hx
        have e : t.2.1[actF l L]? = none := by rw [r5, hj]
        simp [e]
      · have hx' : x ≠ actF l L := fun e => hx e.symm
        simp only [beq_iff_eq, hx, ↓reduceIte, hx']
        cases t.2.1[x]? <;> rfl
    · intro x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hP x hx
      · exact hPM

theorem rel5_loop {act : Array Nat → Lab → Lab} {letters : Array (Array Nat)}
    {actF : Nat → Lab → Lab} {P : Lab → Prop} {L : Lab} {i : Nat} (hL : P L)
    (hcl : ∀ l < letters.size, ∀ x, P x → P (actF l x) ∧ act letters[l]! x = actF l x) :
    ∀ (ls : List Nat) (t : St5 Lab) (s : St4 Lab), (∀ l ∈ ls, l < letters.size) → Rel5 t s →
      (∀ x ∈ s.1.toList, P x) →
      Rel5 (Id.run (forIn ls t (stepF act letters L i))) (ls.foldl (omStep actF L i) s) ∧
        ∀ x ∈ (ls.foldl (omStep actF L i) s).1.toList, P x
  | [], t, s, _, R, hP => ⟨R, hP⟩
  | l :: ls, t, s, hls, R, hP => by
    obtain ⟨t', e, R', hP'⟩ := rel5_step (i := i) hL (hls l List.mem_cons_self) hcl R hP
    rw [List.forIn_cons, e, List.foldl_cons]
    exact rel5_loop hL hcl ls t' _ (fun l' h => hls l' (List.mem_cons_of_mem _ h)) R' hP'

theorem getElem!_mem {a : Array Lab} {i : Nat} (h : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i h]
  exact Array.getElem_mem_toList h

theorem run_eq {act : Array Nat → Lab → Lab} {letters : Array (Array Nat)} {cap : Nat}
    {actF : Nat → Lab → Lab} {P : Lab → Prop}
    (hcl : ∀ l < letters.size, ∀ x, P x → P (actF l x) ∧ act letters[l]! x = actF l x) :
    ∀ (f : Nat) (u : St6 Lab) (s : St4 Lab) (R : OmegaData Lab × Bool),
      Rel5 (u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1) s → (∀ x ∈ s.1.toList, P x) →
      omRun actF letters.size cap f s u.2.2.2.2.2 = some R →
      outF (forIn (m := Id) Lean.Loop.mk u (fun _ s => bodyF act letters cap s)) = R ∧
        ∀ x ∈ R.1.lbl.toList, P x
  | 0, _, _, _, _, _, h => by simp [omRun] at h
  | f + 1, u, s, R, Rl, hP, h => by
    obtain ⟨r1, r2, r3, r4, r5⟩ := Rl
    simp only at r1 r2 r3 r4 r5
    rw [forIn_loop_unfold]
    unfold omRun at h
    unfold bodyF
    rw [r1]
    by_cases hc : (decide (u.2.2.2.2.2 < s.1.size) && decide (s.1.size ≤ cap)) = true
    · rw [if_pos hc] at h ⊢
      have hi : u.2.2.2.2.2 < s.1.size := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1
      have hL := hP _ (getElem!_mem hi)
      obtain ⟨R', hP'⟩ := rel5_loop (i := u.2.2.2.2.2) hL hcl (List.range' 0 letters.size)
        (s.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1) s
        (fun l hl => by simpa using (List.mem_range'.1 hl)) ⟨rfl, r2, r3, r4, r5⟩ hP
      exact run_eq hcl f _ _ R R' hP' h
    · rw [if_neg hc] at h ⊢
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, hP⟩
      change outF (s.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1, u.2.2.2.2.2) = _
      unfold outF
      dsimp only
      rw [r2, r3, r4]

theorem buildOmega_of_twin {act : Array Nat → Lab → Lab} {letters : Array (Array Nat)} {Δ : Lab}
    {cap fuel : Nat} {actF : Nat → Lab → Lab} {R : OmegaData Lab × Bool} (P : Lab → Prop)
    (hΔ : P Δ) (hcl : ∀ l < letters.size, ∀ x, P x → P (actF l x) ∧ act letters[l]! x = actF l x)
    (h : omTwin actF letters.size Δ cap fuel = some R) :
    buildOmega act letters Δ cap = R ∧ ∀ x ∈ R.1.lbl.toList, P x := by
  rw [buildOmega_eq]
  refine run_eq hcl fuel _ (#[Δ], #[0], #[0], Array.replicate letters.size #[]) R
    ⟨rfl, rfl, rfl, rfl, fun x => ?_⟩ (by simpa using hΔ) h
  rw [Std.HashMap.getElem?_insert]
  by_cases hx : x = Δ
  · subst hx
    simp [idxL]
  · have hx' : (Δ == x) = false := by simpa using fun e => hx e.symm
    simp [hx', idxL, hx]

end Twin

theorem good_ext {n : Nat} {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g)
    (h : ∀ p < n, f p = g p) : s = t := by
  apply Array.ext (by rw [hs.1, ht.1])
  intro i h1 h2
  have hi : i < n := by rw [← hs.1]; exact h1
  have e1 := (hs.2 i hi).1
  have e2 := (ht.2 i hi).1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1] at e1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2] at e2
  simp only [Option.getD_some] at e1 e2
  rw [e1, e2, h i hi]

theorem good_ne {n : Nat} {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g)
    {p : Nat} (hp : p < n) (h : f p ≠ g p) : s ≠ t := by
  rintro rfl
  exact h (by rw [← (hs.2 p hp).1, ← (ht.2 p hp).1])

@[expose] def two (f g : Nat → Nat) : Nat → Nat → Nat
  | 0 => f
  | _ => g

theorem good_two {n : Nat} {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g) :
    ∀ l < (#[s, t] : Array (Array Nat)).size, Good n ((#[s, t] : Array (Array Nat)).getD l #[])
      (two f g l)
  | 0, _ => hs
  | 1, _ => ht
  | _ + 2, h => absurd h (by simp)

theorem good_comm {n : Nat} {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f)
    (ht : Good n t g) :
    Good n (wordTabA #[s, t] n [0, 1]) (fun p => f (g p)) ∧
      Good n (wordTabA #[s, t] n [1, 0]) (fun p => g (f p)) :=
  ⟨good_word (good_two hs ht) (by simp), good_word (good_two hs ht) (by simp)⟩

theorem good_idTab (n : Nat) : Good n (idTab' n) (fun p => p) := by
  refine ⟨by simp [idTab'], fun p hp => ⟨?_, hp⟩⟩
  simp [idTab', Array.getD_eq_getD_getElem?, hp]

theorem all_range {n : Nat} {f : Nat → Bool} (h : (List.range n).all f = true) :
    ∀ p < n, f p = true := fun p hp => by
  rw [List.all_eq_true] at h
  exact h p (List.mem_range.2 hp)

theorem not_all_range {n : Nat} {f : Nat → Bool} (h : (!(List.range n).all f) = true) :
    ∃ p < n, f p = false := by
  rw [Bool.not_eq_true', List.all_eq_false] at h
  obtain ⟨p, hp, e⟩ := h
  exact ⟨p, List.mem_range.1 hp, by simpa using e⟩

theorem insN_mem {l : List Nat} {p : Nat} (h : p ∈ insN l) : p ∈ l := by
  rw [insN_eq] at h
  exact (List.perm_insertionSort _ l).mem_iff.1 h

theorem ptAct_good {n : Nat} {t : Array Nat} {f : Nat → Nat} (ht : Good n t f) {x : List Nat}
    (hx : ∀ p ∈ x, p < n) : ptAct t x = insN (x.map f) := by
  unfold ptAct
  rw [sortN_eq]
  congr 1
  exact List.map_congr_left fun p hp => (ht.2 p (hx p hp)).1

theorem getElem!_eq_getD' (a : Array (Array Nat)) (l : Nat) : a[l]! = a.getD l #[] := by
  rw [Array.getElem!_eq_getD]
  rfl

theorem rChkF_sound {n : Nat} {Δ : List Nat} {sTabs : List (Array Nat)} {ta tb zT : Array Nat}
    {uWords : List (List Nat)} {yw nw : List Nat} {r m fuel : Nat} {L AB : Nat → Nat → Nat}
    {Z : Nat → Nat}
    (hS : ∀ l < sTabs.length, Good n (sTabs.toArray.getD l #[]) (L l))
    (ha : Good n ta (AB 0)) (hb : Good n tb (AB 1)) (hz : Good n zT Z)
    (h : rChkF n Δ L sTabs.length AB Z uWords yw nw r m fuel = true) :
    rChk n ptAct Δ sTabs ta tb zT uWords yw nw r m = true := by
  unfold rChkF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hΔ⟩, hu⟩, horb⟩, hcz⟩, hyo⟩, hy1⟩, hyz⟩, hxy⟩ := h
  have hAB : ∀ l < (#[ta, tb] : Array (Array Nat)).size,
      Good n ((#[ta, tb] : Array (Array Nat)).getD l #[]) (AB l)
    | 0, _ => ha
    | 1, _ => hb
    | _ + 2, h => absurd h (by simp)
  have hw : ∀ w ∈ uWords, ∀ l ∈ w, l < (#[ta, tb] : Array (Array Nat)).size := by
    intro w hw l hl
    have := List.all_eq_true.1 h1 w hw
    simpa using List.all_eq_true.1 this l hl
  have hlen : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size =
      sTabs.length + uWords.length := by simp
  have hLet : ∀ l < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size,
      Good n (((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD l #[]) (L l) := by
    intro l hl
    rw [hlen] at hl
    by_cases hls : l < sTabs.length
    · have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD l #[] =
          sTabs.toArray.getD l #[] := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left hls, hls]
      rw [e]
      exact hS l hls
    · obtain ⟨k, rfl⟩ : ∃ k, l = sTabs.length + k := ⟨l - sTabs.length, by omega⟩
      have hk : k < uWords.length := by omega
      have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD (sTabs.length + k) #[] =
          wordTabA #[ta, tb] n (uWords.getD k []) := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, hk]
      rw [e]
      have hmem : uWords.getD k [] ∈ uWords := by
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      have g := good_word hAB (hw _ hmem)
      have hk' := all_range (all_range hu k hk)
      refine ⟨g.1, fun p hp => ?_⟩
      rw [(beq_iff_eq.1 (hk' p hp))]
      exact g.2 p hp
  have hcl : ∀ l < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size, ∀ x : List Nat,
      (∀ p ∈ x, p < n) → (∀ p ∈ insN (x.map (L l)), p < n) ∧
        ptAct ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray)[l]! x = insN (x.map (L l)) := by
    intro l hl x hx
    refine ⟨fun p hp => ?_, by rw [getElem!_eq_getD']; exact ptAct_good (hLet l hl) hx⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (insN_mem hp)
    exact ((hLet l hl).2 q (hx q hq)).2
  unfold orbOK at horb
  split at horb
  · next R hR =>
    rw [← hlen] at hR
    obtain ⟨hbo, hPR⟩ := buildOmega_of_twin (act := ptAct) (cap := m + 1)
      (fun x : List Nat => ∀ p ∈ x, p < n)
      (fun p hp => by simpa using List.all_eq_true.1 hΔ p hp) hcl hR
    simp only [Bool.and_eq_true] at horb
    obtain ⟨⟨hom, hm⟩, hfix⟩ := horb
    unfold omOK at hom
    simp only [Bool.and_eq_true] at hom
    obtain ⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, o4⟩ := hom
    have hpts : ∀ i < R.1.lbl.size, ∀ p ∈ R.1.lbl[i]!, p < n := fun i hi =>
      hPR _ (getElem!_mem hi)
    have hy := good_word hLet (w := yw) (fun l hl => by
      rw [hlen]
      simpa using List.all_eq_true.1 h2 l hl)
    have hS' : ∀ l < sTabs.toArray.size, Good n (sTabs.toArray.getD l #[]) (L l) :=
      fun l hl => hS l (by simpa using hl)
    have hx := good_word hS' (w := nw) (fun l hl => by simpa using List.all_eq_true.1 h3 l hl)
    unfold rChk
    simp only [hbo, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [lettersLt] using h2
    · simpa [lettersLt] using h3
    · refine decide_eq_true ⟨beq_iff_eq.1 o0, of_decide_eq_true o1, fun l hl i hi => ?_,
        fun i hi hi0 => ?_, CFSG.Quasithin.GoldD3.distinctB_of_nodup (of_decide_eq_true o4)⟩
      · have e := List.all_eq_true.1 (List.all_eq_true.1 o2 l (List.mem_range.2 (by
          rw [← hlen]; exact hl))) i (List.mem_range.2 hi)
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at e
        refine ⟨e.1, ?_⟩
        rw [e.2, (hcl l hl _ (hpts i hi)).2]
      · have e := List.all_eq_true.1 o3 i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at e
        rcases e with e | ⟨⟨e1, e2⟩, e3⟩
        · omega
        · exact ⟨e1, (by omega), e3⟩
    · simpa using hm
    · rw [List.all_eq_true]
      intro uT huT
      obtain ⟨w, hw', rfl⟩ := List.mem_map.1 huT
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw'
      have hk' : sTabs.length + k < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size := by
        rw [hlen]
        omega
      have g := hLet _ hk'
      have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD (sTabs.length + k) #[] =
          wordTabA #[ta, tb] n uWords[k] := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, hk]
      rw [e] at g
      have hc := good_comm g hz
      rw [beq_iff_eq]
      refine good_ext hc.1 hc.2 fun p hp => ?_
      have := all_range (all_range hcz k hk) p hp
      exact beq_iff_eq.1 this
    · rw [beq_iff_eq]
      refine good_ext (good_word (L := fun _ => wordF L yw) (fun l hl => by
        have : l = 0 := by simpa using hl
        subst this
        exact hy) (by simp)) (good_idTab n) fun p hp => beq_iff_eq.1 (all_range hyo p hp)
    · obtain ⟨p, hp, e⟩ := not_all_range hy1
      rw [bne_iff_ne]
      exact good_ne hy (good_idTab n) hp (by simpa using e)
    · have hc := good_comm hy hz
      rw [beq_iff_eq]
      exact good_ext hc.1 hc.2 fun p hp => beq_iff_eq.1 (all_range hyz p hp)
    · rw [List.all_eq_true]
      intro i hi
      have hi' := List.mem_range.1 hi
      rw [decide_eq_true_eq, ptAct_good hx (hpts i hi')]
      have := List.all_eq_true.1 hfix _ (getElem!_mem hi')
      exact beq_iff_eq.1 this
    · obtain ⟨p, hp, e⟩ := not_all_range hxy
      have hc := good_comm hy hx
      rw [bne_iff_ne]
      exact good_ne hc.1 hc.2 hp (by simpa using e)
  · simp at horb

theorem ncChkF_sound {n : Nat} {ta zT : Array Nat} {a z : Nat → Nat} (ha : Good n ta a)
    (hz : Good n zT z) (h : ncChkF n a z = true) : ncChk n ta zT = true := by
  obtain ⟨p, hp, e⟩ := not_all_range h
  have hc := good_comm ha hz
  unfold ncChk
  rw [bne_iff_ne]
  exact good_ne hc.1 hc.2 hp (by simpa using e)

end CFSG.KC.SLOm

end
