module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.ChengHeld.Model

@[expose] def bfsRun {α : Type} (N : ℕ) (fs : List α) (step : α → ℕ → ℕ) (x0 : ℕ) :
    Array Bool × Array ℕ := Id.run do
  let mut mem : Array Bool := Array.replicate N false
  mem := mem.set! x0 true
  let mut queue : Array ℕ := #[x0]
  let mut qi := 0
  while qi < queue.size do
    let y := queue[qi]!
    qi := qi + 1
    for f in fs do
      let z := step f y
      if !mem[z]! then
        mem := mem.set! z true
        queue := queue.push z
  return (mem, queue)

theorem forIn_loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

theorem forIn_loop_induction {β : Type} (f : Unit → β → Id (ForInStep β)) (μ : β → ℕ)
    (I Q : β → Prop)
    (hdone : ∀ s, I s → ∀ s', f () s = ForInStep.done s' → Q s')
    (hyield : ∀ s, I s → ∀ s', f () s = ForInStep.yield s' → I s' ∧ μ s' < μ s) :
    ∀ s, I s → Q (forIn (m := Id) Lean.Loop.mk s f) := by
  suffices h : ∀ n, ∀ s, μ s = n → I s → Q (forIn (m := Id) Lean.Loop.mk s f) from
    fun s hI => h _ s rfl hI
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hμ hI
    rw [forIn_loop_unfold]
    rcases hfs : f () s with s' | s'
    · exact hdone s hI s' hfs
    · obtain ⟨hI', hlt⟩ := hyield s hI s' hfs
      exact ih (μ s') (hμ ▸ hlt) s' rfl hI'

theorem forIn_list_ite {α β : Type} (l : List α) (c : α → β → Bool) (a b : α → β → β) (init : β) :
    forIn (m := Id) l init (fun f s => if c f s = true then pure (ForInStep.yield (a f s))
      else pure (ForInStep.yield (b f s))) =
    l.foldl (fun s f => if c f s = true then a f s else b f s) init := by
  induction l generalizing init with
  | nil => rfl
  | cons f l ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    by_cases hc : c f init = true
    · simp [hc, ih]
    · simp [hc, ih]


@[expose] def bfsInner {α : Type} (step : α → ℕ → ℕ) (y : ℕ) (t : Array Bool × Array ℕ) (f : α) :
    Array Bool × Array ℕ :=
  if (!t.1[step f y]!) = true then (t.1.set! (step f y) true, t.2.push (step f y)) else t

@[expose] def bfsBody {α : Type} (fs : List α) (step : α → ℕ → ℕ) (s : Array Bool × Array ℕ × ℕ) :
    ForInStep (Array Bool × Array ℕ × ℕ) :=
  if s.2.2 < s.2.1.size then
    ForInStep.yield ((fs.foldl (bfsInner step s.2.1[s.2.2]!) (s.1, s.2.1)).1,
      (fs.foldl (bfsInner step s.2.1[s.2.2]!) (s.1, s.2.1)).2, s.2.2 + 1)
  else ForInStep.done s


theorem bfsRun_eq {α : Type} (N : ℕ) (fs : List α) (step : α → ℕ → ℕ) (x0 : ℕ) :
    bfsRun N fs step x0 =
      ((forIn (m := Id) Lean.Loop.mk ((Array.replicate N false).set! x0 true, #[x0], 0)
        (fun _ s => pure (bfsBody fs step s))).1,
       (forIn (m := Id) Lean.Loop.mk ((Array.replicate N false).set! x0 true, #[x0], 0)
        (fun _ s => pure (bfsBody fs step s))).2.1) := by
  unfold bfsRun
  simp only [Id.run, bind_pure_comp]
  simp only [forIn_list_ite]
  rfl

theorem bfsInner_spec {α : Type} {N : ℕ} {step : α → ℕ → ℕ} {y : ℕ} {f : α} (hf : step f y < N)
    {t : Array Bool × Array ℕ} (hs : t.1.size = N) (hm : ∀ z, t.1[z]! = true ↔ z ∈ t.2.toList)
    (hnd : t.2.toList.Nodup) :
    (bfsInner step y t f).1.size = N ∧
      (∀ z, (bfsInner step y t f).1[z]! = true ↔ z ∈ (bfsInner step y t f).2.toList) ∧
      (bfsInner step y t f).2.toList.Nodup ∧
      ((bfsInner step y t f).2.toList = t.2.toList ∨
        (bfsInner step y t f).2.toList = t.2.toList ++ [step f y]) ∧
      step f y ∈ (bfsInner step y t f).2.toList := by
  unfold bfsInner
  by_cases hc : (!t.1[step f y]!) = true
  · simp only [hc, ↓reduceIte]
    have hz0 : t.1[step f y]! = false := by simpa using hc
    have hnot : step f y ∉ t.2.toList := fun hmem => by
      have := (hm _).2 hmem
      rw [hz0] at this
      exact Bool.false_ne_true this
    refine ⟨by simp [hs], fun z => ?_, ?_, Or.inr ?_, ?_⟩
    · by_cases hz : z = step f y
      · subst hz
        rw [Array.getElem!_set!_self _ _ _ (by omega)]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hz), hm]
        simp [hz]
    · simp only [Array.toList_push, List.nodup_append, hnd, List.nodup_singleton, true_and,
        List.mem_singleton]
      intro a ha b hb
      subst hb
      rintro rfl
      exact hnot ha
    · simp
    · simp
  · simp only [hc]
    have hz1 : t.1[step f y]! = true := by simpa using hc
    exact ⟨hs, hm, hnd, Or.inl rfl, (hm _).1 hz1⟩

theorem bfsFold_spec {α : Type} {N : ℕ} {step : α → ℕ → ℕ} {y : ℕ} (l : List α)
    (hl : ∀ f ∈ l, step f y < N) :
    ∀ t : Array Bool × Array ℕ, t.1.size = N → (∀ z, t.1[z]! = true ↔ z ∈ t.2.toList) →
      t.2.toList.Nodup →
      (l.foldl (bfsInner step y) t).1.size = N ∧
      (∀ z, (l.foldl (bfsInner step y) t).1[z]! = true ↔
        z ∈ (l.foldl (bfsInner step y) t).2.toList) ∧
      (l.foldl (bfsInner step y) t).2.toList.Nodup ∧
      (∃ ext : List ℕ, (l.foldl (bfsInner step y) t).2.toList = t.2.toList ++ ext ∧
        ∀ e ∈ ext, ∃ f ∈ l, e = step f y) ∧
      ∀ f ∈ l, step f y ∈ (l.foldl (bfsInner step y) t).2.toList := by
  induction l with
  | nil =>
    intro t hs hm hnd
    exact ⟨hs, hm, hnd, ⟨[], by simp, by simp⟩, by simp⟩
  | cons f l ih =>
    intro t hs hm hnd
    obtain ⟨h1, h2, h3, h4, h5⟩ := bfsInner_spec (hl f (by simp)) hs hm hnd
    obtain ⟨k1, k2, k3, ⟨ext, hext, hext2⟩, k5⟩ :=
      ih (fun g hg => hl g (by simp [hg])) _ h1 h2 h3
    simp only [List.foldl_cons]
    refine ⟨k1, k2, k3, ?_, ?_⟩
    · rcases h4 with h4 | h4
      · exact ⟨ext, by rw [hext, h4], fun e he => by
          obtain ⟨g, hg, rfl⟩ := hext2 e he
          exact ⟨g, by simp [hg], rfl⟩⟩
      · exact ⟨[step f y] ++ ext, by rw [hext, h4]; simp, fun e he => by
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with rfl | he
          · exact ⟨f, by simp, rfl⟩
          · obtain ⟨g, hg, rfl⟩ := hext2 e he
            exact ⟨g, by simp [hg], rfl⟩⟩
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · rw [hext]
        exact List.mem_append_left _ h5
      · exact k5 g hg

structure BfsInv {α : Type} (N : ℕ) (fs : List α) (step : α → ℕ → ℕ) (x0 : ℕ)
    (s : Array Bool × Array ℕ × ℕ) : Prop where
  size : s.1.size = N
  mem : ∀ z, s.1[z]! = true ↔ z ∈ s.2.1.toList
  nodup : s.2.1.toList.Nodup
  lt : ∀ z ∈ s.2.1.toList, z < N
  start : x0 ∈ s.2.1.toList
  qi_le : s.2.2 ≤ s.2.1.size
  done : ∀ i, i < s.2.2 → ∀ f ∈ fs, step f (s.2.1[i]!) ∈ s.2.1.toList
  reach : ∀ P : ℕ → Prop, P x0 → (∀ f ∈ fs, ∀ y, P y → P (step f y)) → ∀ z ∈ s.2.1.toList, P z

theorem getElem!_replicate_false (N z : ℕ) : (Array.replicate N false)[z]! = false := by
  by_cases hz : z < N
  · rw [getElem!_pos _ _ (by simpa using hz)]
    simp
  · rw [getElem!_neg _ _ (by simpa using hz)]
    rfl

theorem bfsInv_init {α : Type} {N : ℕ} {fs : List α} {step : α → ℕ → ℕ} {x0 : ℕ} (hx0 : x0 < N) :
    BfsInv N fs step x0 ((Array.replicate N false).set! x0 true, #[x0], 0) := by
  refine ⟨by simp, fun z => ?_, by simp, by simpa using hx0, by simp, by simp,
    fun i hi => by simp at hi, fun P hP0 _ z hz => ?_⟩
  · by_cases hz : z = x0
    · subst hz
      rw [Array.getElem!_set!_self _ _ _ (by simpa using hx0)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hz), getElem!_replicate_false]
      simp [hz]
  · simp only [List.mem_singleton] at hz
    rw [hz]
    exact hP0

theorem length_le_of_nodup_lt {l : List ℕ} {N : ℕ} (hnd : l.Nodup) (hlt : ∀ z ∈ l, z < N) :
    l.length ≤ N := by
  have h1 : l.toFinset ⊆ Finset.range N := fun z hz => by
    simpa using hlt z (List.mem_toFinset.1 hz)
  have := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this

theorem getElem!_eq_of_toList_append {a b : Array ℕ} {ext : List ℕ}
    (h : b.toList = a.toList ++ ext) {i : ℕ} (hi : i < a.size) : b[i]! = a[i]! := by
  have hb : i < b.size := by
    have := congrArg List.length h
    simp only [Array.length_toList, List.length_append] at this
    omega
  rw [getElem!_pos a i hi, getElem!_pos b i hb]
  have h1 : b[i] = b.toList[i]'(by simpa using hb) := by simp
  have h2 : b.toList[i]'(by simpa using hb) = (a.toList ++ ext)[i]'(by
      rw [← h]; simpa using hb) := List.getElem_of_eq h _
  rw [h1, h2, List.getElem_append_left (by simpa using hi)]
  simp

theorem bfsBody_yield {α : Type} {N : ℕ} {fs : List α} {step : α → ℕ → ℕ} {x0 : ℕ}
    (hstep : ∀ f ∈ fs, ∀ y < N, step f y < N) {s s' : Array Bool × Array ℕ × ℕ}
    (hI : BfsInv N fs step x0 s) (h : bfsBody fs step s = ForInStep.yield s') :
    BfsInv N fs step x0 s' ∧
      2 * N + 1 - (s'.2.1.size + s'.2.2) < 2 * N + 1 - (s.2.1.size + s.2.2) := by
  unfold bfsBody at h
  split at h
  · rename_i hq
    injection h with h
    subst h
    have hyq : s.2.1[s.2.2]! ∈ s.2.1.toList := by
      rw [getElem!_pos s.2.1 s.2.2 hq]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hq)
    have hyN : s.2.1[s.2.2]! < N := hI.lt _ hyq
    obtain ⟨k1, k2, k3, ⟨ext, hext, hext2⟩, k5⟩ :=
      bfsFold_spec (step := step) fs (fun f hf => hstep f hf _ hyN) (s.1, s.2.1) hI.size hI.mem
        hI.nodup
    set r := fs.foldl (bfsInner step s.2.1[s.2.2]!) (s.1, s.2.1) with hr
    have hext : r.2.toList = s.2.1.toList ++ ext := hext
    have hlt : ∀ z ∈ r.2.toList, z < N := by
      intro z hz
      rw [hext] at hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hI.lt z hz
      · obtain ⟨f, hf, rfl⟩ := hext2 z hz
        exact hstep f hf _ hyN
    have hlen : s.2.1.size ≤ r.2.size := by
      have := congrArg List.length hext
      simp only [Array.length_toList, List.length_append] at this
      omega
    have hbound : r.2.size ≤ N := by
      have := length_le_of_nodup_lt k3 hlt
      simpa using this
    have hI' : BfsInv N fs step x0 (r.1, r.2, s.2.2 + 1) := by
      refine ⟨k1, k2, k3, hlt, ?_, ?_, ?_, ?_⟩
      · rw [hext]; exact List.mem_append_left _ hI.start
      · show s.2.2 + 1 ≤ r.2.size
        omega
      · intro i hi f hf
        show step f (r.2[i]!) ∈ r.2.toList
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [getElem!_eq_of_toList_append hext (by show i < s.2.1.size; omega)]
          rw [hext]
          exact List.mem_append_left _ (hI.done i hi f hf)
        · subst hi
          rw [getElem!_eq_of_toList_append hext hq]
          exact k5 f hf
      · intro P hP0 hPc z hz
        rw [hext] at hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hI.reach P hP0 hPc z hz
        · obtain ⟨f, hf, rfl⟩ := hext2 z hz
          exact hPc f hf _ (hI.reach P hP0 hPc _ hyq)
    refine ⟨hI', ?_⟩
    show 2 * N + 1 - (r.2.size + (s.2.2 + 1)) < 2 * N + 1 - (s.2.1.size + s.2.2)
    omega
  · cases h

theorem bfsRun_spec {α : Type} {N : ℕ} (fs : List α) (step : α → ℕ → ℕ) {x0 : ℕ} (hx0 : x0 < N)
    (hstep : ∀ f ∈ fs, ∀ y < N, step f y < N) :
    (bfsRun N fs step x0).1.size = N ∧
      (∀ z, (bfsRun N fs step x0).1[z]! = true ↔ z ∈ (bfsRun N fs step x0).2.toList) ∧
      (bfsRun N fs step x0).2.toList.Nodup ∧
      (∀ z ∈ (bfsRun N fs step x0).2.toList, z < N) ∧
      x0 ∈ (bfsRun N fs step x0).2.toList ∧
      (∀ y ∈ (bfsRun N fs step x0).2.toList, ∀ f ∈ fs, step f y ∈ (bfsRun N fs step x0).2.toList) ∧
      (∀ P : ℕ → Prop, P x0 → (∀ f ∈ fs, ∀ y, P y → P (step f y)) →
        ∀ z ∈ (bfsRun N fs step x0).2.toList, P z) := by
  rw [bfsRun_eq]
  have key := forIn_loop_induction (fun _ s => pure (bfsBody fs step s))
    (fun s => 2 * N + 1 - (s.2.1.size + s.2.2)) (BfsInv N fs step x0)
    (fun s => s.1.size = N ∧ (∀ z, s.1[z]! = true ↔ z ∈ s.2.1.toList) ∧ s.2.1.toList.Nodup ∧
      (∀ z ∈ s.2.1.toList, z < N) ∧ x0 ∈ s.2.1.toList ∧
      (∀ y ∈ s.2.1.toList, ∀ f ∈ fs, step f y ∈ s.2.1.toList) ∧
      (∀ P : ℕ → Prop, P x0 → (∀ f ∈ fs, ∀ y, P y → P (step f y)) → ∀ z ∈ s.2.1.toList, P z))
    (fun s hI s' hs' => by
      have h' : bfsBody fs step s = ForInStep.done s' := hs'
      unfold bfsBody at h'
      split at h'
      · cases h'
      · rename_i hq
        injection h' with h'
        subst h'
        refine ⟨hI.size, hI.mem, hI.nodup, hI.lt, hI.start, ?_, hI.reach⟩
        intro y hy f hf
        obtain ⟨i, hi, rfl⟩ : ∃ i < s.2.1.size, s.2.1[i]! = y := by
          rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hy
          obtain ⟨i, hi, rfl⟩ := hy
          exact ⟨i, hi, getElem!_pos s.2.1 i hi⟩
        exact hI.done i (by have := hI.qi_le; omega) f hf)
    (fun s hI s' hs' => bfsBody_yield hstep hI hs')
    _ (bfsInv_init hx0)
  exact key

end CFSG.OddStandard.ChengHeld.Model
