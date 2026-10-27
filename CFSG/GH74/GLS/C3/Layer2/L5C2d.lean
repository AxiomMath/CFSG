module

public import CFSG.GH74.GLS.C3.Layer2.L5C2c
public import CFSG.GH74.GLS.C3.Layer2.L5C2a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

variable {n : Nat} [Group (Idx n)]

theorem isInv_iff {u : Idx n} : isInv u = true ↔ u * u = 1 ∧ u ≠ 1 := by
  simp [isInv]

theorem cszI_eq (u : Idx n) : cszI u = cardC u := by
  unfold cszI cardC
  symm
  apply natCard_eq_length _ _ ((nodup_elemsI n).filter _)
  intro p
  simp [Subgroup.mem_centralizer_singleton_iff, mem_elemsI]

omit [Group (Idx n)] in
theorem foldl_addNew_mem (P : Idx n → Prop) (ys : List (Idx n)) :
    ∀ (st : Array Bool × List (Idx n)), (∀ z ∈ st.2, P z) → (∀ y ∈ ys, P y) →
      ∀ z ∈ (ys.foldl (fun (st : Array Bool × List (Idx n)) y =>
        if st.1.getD y.v false then st else (st.1.set! y.v true, y :: st.2)) st).2, P z := by
  induction ys with
  | nil => intro st hst _ z hz; exact hst z hz
  | cons y ys ih =>
    intro st hst hys z hz
    rw [List.foldl_cons] at hz
    refine ih _ ?_ (fun y' hy' => hys y' (List.mem_cons_of_mem _ hy')) z hz
    by_cases hv : st.1.getD y.v false = true
    · simpa [hv] using hst
    · have : st.1.getD y.v false = false := by simpa using hv
      simp only [this, Bool.false_eq_true, ite_false]
      intro z' hz'
      rcases List.mem_cons.1 hz' with rfl | hz'
      · exact hys _ List.mem_cons_self
      · exact hst z' hz'

omit [Group (Idx n)] in
theorem frontier_fold_mem (steps : Idx n → List (Idx n)) (P : Idx n → Prop)
    (hP : ∀ x, P x → ∀ y ∈ steps x, P y) (frontier : List (Idx n)) :
    ∀ (st : Array Bool × List (Idx n)), (∀ z ∈ st.2, P z) → (∀ x ∈ frontier, P x) →
      ∀ z ∈ (frontier.foldl (fun (st : Array Bool × List (Idx n)) x =>
        addNew st.1 st.2 (steps x)) st).2, P z := by
  induction frontier with
  | nil => intro st hst _ z hz; exact hst z hz
  | cons x xs ih =>
    intro st hst hxs z hz
    rw [List.foldl_cons] at hz
    refine ih _ ?_ (fun x' hx' => hxs x' (List.mem_cons_of_mem _ hx')) z hz
    exact foldl_addNew_mem P (steps x) (st.1, st.2) hst (hP x (hxs x List.mem_cons_self))

omit [Group (Idx n)] in
theorem bfsGo_mem (steps : Idx n → List (Idx n)) (P : Idx n → Prop)
    (hP : ∀ x, P x → ∀ y ∈ steps x, P y) :
    ∀ (fuel : Nat) (vis : Array Bool) (frontier acc : List (Idx n)),
      (∀ x ∈ frontier, P x) → (∀ x ∈ acc, P x) → ∀ y ∈ bfsGo steps fuel vis frontier acc, P y := by
  intro fuel
  induction fuel with
  | zero => intro vis frontier acc _ hacc y hy; exact hacc y (by simpa [bfsGo] using hy)
  | succ fuel ih =>
    intro vis frontier acc hf hacc y hy
    cases frontier with
    | nil => exact hacc y (by simpa [bfsGo] using hy)
    | cons x xs =>
      simp only [bfsGo] at hy
      have hnew := frontier_fold_mem steps P hP (x :: xs) (vis, []) (by simp) hf
      refine ih _ _ _ hnew ?_ y hy
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hacc z hz
      · exact hnew z hz

omit [Group (Idx n)] in
theorem bfs_mem (steps : Idx n → List (Idx n)) (P : Idx n → Prop)
    (hP : ∀ x, P x → ∀ y ∈ steps x, P y) (r : Idx n) (hr : P r) : ∀ y ∈ bfs steps r, P y := by
  unfold bfs
  refine bfsGo_mem steps P hP _ _ _ _ ?_ ?_
  · intro x hx; rw [List.mem_singleton.1 hx]; exact hr
  · intro x hx; rw [List.mem_singleton.1 hx]; exact hr

omit [Group (Idx n)] in
theorem foldl_dedup_sub (ps₀ : List (Idx n × Idx n)) (qs : List (Idx n × Idx n)) :
    ∀ (st : Array Bool × List (Idx n × Idx n)), (∀ p ∈ st.2, p ∈ ps₀) → (∀ q ∈ qs, q ∈ ps₀) →
      ∀ p ∈ (qs.foldl (fun (st : Array Bool × List (Idx n × Idx n)) p =>
        if st.1.getD (p.1.v * n + p.2.v) false then st
        else (st.1.set! (p.1.v * n + p.2.v) true, p :: st.2)) st).2, p ∈ ps₀ := by
  induction qs with
  | nil => intro st hst _ p hp; exact hst p hp
  | cons q qs ih =>
    intro st hst hqs p hp
    rw [List.foldl_cons] at hp
    refine ih _ ?_ (fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq')) p hp
    by_cases hv : st.1.getD (q.1.v * n + q.2.v) false = true
    · simpa [hv] using hst
    · have : st.1.getD (q.1.v * n + q.2.v) false = false := by simpa using hv
      simp only [this, Bool.false_eq_true, ite_false]
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hqs _ List.mem_cons_self
      · exact hst z hz

omit [Group (Idx n)] in
theorem dedupPairs_sub (ps : List (Idx n × Idx n)) : ∀ p ∈ dedupPairs ps, p ∈ ps := by
  intro p hp
  exact foldl_dedup_sub ps ps _ (by simp) (fun q hq => hq) p hp

variable {emb : ↥T5 →* Idx n} {E : Idx n → Idx n → Prop}

theorem f5Pairs_E
    (h : FusionHyp (Idx n) emb E) : ∀ p ∈ f5Pairs emb, E p.1 p.2 := by
  intro p hp
  simp only [f5Pairs, List.mem_flatMap, List.mem_filterMap] at hp
  obtain ⟨t, -, g, hg, hdite⟩ := hp
  by_cases hT : T5b (g * (t : Amb 5) * g⁻¹) = true
  · simp only [hT, ↓reduceDIte] at hdite
    obtain rfl := Option.some.inj hdite
    exact h.f5 g (mem_F5list.1 hg) t ⟨_, mem_T5_of_b hT⟩ rfl
  · simp [hT] at hdite

theorem nbarPairs_E
    (h : FusionHyp (Idx n) emb E) : ∀ p ∈ nbarPairs emb, E p.1 p.2 := by
  intro p hp
  simp only [nbarPairs, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨A, hA, i, -, rfl⟩ := hp
  exact h.nbar A hA i

theorem fuseOf_E
    (h : FusionHyp (Idx n) emb E) : ∀ p ∈ fuseOf emb, E p.1 p.2 := by
  intro p hp
  have hp' := dedupPairs_sub _ p hp
  rw [List.mem_filter] at hp'
  rcases List.mem_append.1 hp'.1 with h1 | h1
  · exact f5Pairs_E h p h1
  · exact nbarPairs_E h p h1

theorem stepsOf_E
    (h : FusionHyp (Idx n) emb E) (fuse : List (Idx n × Idx n))
    (hf : ∀ p ∈ fuse, E p.1 p.2) (x : Idx n) : ∀ y ∈ stepsOf fuse x, E x y := by
  intro y hy
  simp only [stepsOf, List.mem_append, List.mem_map, List.mem_filterMap] at hy
  rcases hy with ⟨s, -, rfl⟩ | ⟨p, hp, hpy⟩
  · exact h.conj x s
  · by_cases h1 : p.1 = x
    · simp only [h1, ite_true, Option.some.injEq] at hpy
      subst hpy
      have := hf p hp
      rwa [h1] at this
    · by_cases h2 : p.2 = x
      · simp only [h1, h2, ite_false, ite_true, Option.some.injEq] at hpy
        subst hpy
        have := hf p hp
        rw [h2] at this
        exact h.equiv.symm this
      · simp [h1, h2] at hpy

theorem engOK_spec {e : Eng n} (hok : engOK e = true) :
    (∀ r ∈ e.reps, isInv r = true) ∧
    (∀ k < e.reps.length, e.ciA.getD (e.reps.getD k 1).v 0 = k) ∧
    (∀ u ∈ e.invs, e.ciA.getD u.v 0 < e.reps.length ∧ u ∈ e.members.getD (e.ciA.getD u.v 0) []) ∧
    (∀ a : Idx n, e.cszA.getD a.v 0 = cszI a) ∧
    (∀ m : Idx n, evW e.mgens (e.wordA.getD m.v []) = m) ∧
    (∀ k < e.reps.length, ctxOK (e.reps.getD k 1) (e.ctxs.getD k default) = true) ∧
    isInv e.x = true := by
  simp only [engOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.contains_iff_mem] at hok
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩ := hok
  refine ⟨hA, hB, fun u hu => hC u hu, fun a => hD a (mem_elemsI a),
    fun m => hE m (mem_elemsI m), hF, hG⟩

theorem members_getD
    (emb : ↥T5 →* Idx n) (k : Nat) (hk : k < (mkEng emb).reps.length) :
    (mkEng emb).members.getD k [] =
      bfs (stepsOf (fuseOf emb)) ((mkEng emb).reps.getD k 1) := by
  have h1 : (mkEng emb).members = (mkEng emb).reps.map (bfs (stepsOf (fuseOf emb))) := rfl
  rw [h1]
  simp [List.getD_eq_getElem?_getD, hk]

omit [Group (Idx n)] in
theorem getD_toArray_map {α : Type} (f : Idx n → α) (m : Idx n) (d : α) :
    (((elemsI n).map f).toArray).getD m.v d = f m := by
  simp [elemsI, Idx.v, Array.getD_eq_getD_getElem?]

theorem allVecs_length : ∀ (r : Nat) (v : List Bool), v ∈ allVecs r → v.length = r
  | 0, v, hv => by simp [allVecs] at hv; simp [hv]
  | r + 1, v, hv => by
    simp only [allVecs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨v', hv', rfl | rfl⟩ := hv <;> simp [allVecs_length r v' hv']

theorem foldl_xor_acc (v : List Bool) (w : List Nat) (b : Bool) :
    w.foldl (fun acc i => xor acc (v.getD i false)) b =
      xor b (w.foldl (fun acc i => xor acc (v.getD i false)) false) := by
  induction w generalizing b with
  | nil => simp
  | cons i w ih =>
    simp only [List.foldl_cons]
    rw [ih (xor b _), ih (xor false _)]
    cases b <;> cases v.getD i false <;> cases w.foldl (fun acc i => xor acc (v.getD i false)) false <;>
      rfl

theorem foldl_mul_assoc (gs : List (Idx n)) (w : List Nat) (a b : Idx n) :
    w.foldl (fun c i => c * gs.getD i 1) (a * b) = a * w.foldl (fun c i => c * gs.getD i 1) b := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    simp only [List.foldl_cons]
    rw [mul_assoc, ih]

theorem foldl_xor_false (v : List Bool) (hv : ∀ i, v.getD i false = false) (w : List Nat)
    (b : Bool) : w.foldl (fun acc i => xor acc (v.getD i false)) b = b := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    simp only [List.foldl_cons]
    rw [hv i, Bool.xor_false]
    exact ih b

theorem maxSubsOf_sound (mgens : List (Idx n)) (wordA : Array (List Nat))
    (hcov : ∀ m : Idx n, evW mgens (wordA.getD m.v []) = m) :
    ∀ Hm ∈ maxSubsOf mgens wordA, (∀ m : Idx n, Hm.getD m.v false = true) ∨
      ∃ H : Subgroup (Idx n), H.index = 2 ∧ ∀ m, m ∈ H ↔ Hm.getD m.v false = true := by
  intro Hm hHm
  simp only [maxSubsOf, List.mem_map, List.mem_filter] at hHm
  obtain ⟨v, ⟨hvlen, hvalid⟩, rfl⟩ := hHm
  have hlen := allVecs_length _ _ hvlen
  have hmem : ∀ m : Idx n, ((elemsI n).map fun m => !(chiV wordA v m)).toArray.getD m.v false =
      !(chiV wordA v m) := fun m => getD_toArray_map _ m false
  simp only [charValid, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at hvalid
  obtain ⟨h1, hedge⟩ := hvalid
  have hedge' : ∀ (m : Idx n) (i : Nat),
      chiV wordA v (m * mgens.getD i 1) = xor (chiV wordA v m) (v.getD i false) := by
    intro m i
    by_cases hi : i < mgens.length
    · exact hedge m (mem_elemsI m) i (List.mem_range.2 hi)
    · have h2 : mgens.getD i 1 = 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : mgens.length ≤ i)]
        rfl
      have h3 : v.getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : v.length ≤ i)]
        rfl
      rw [h2, h3, mul_one, Bool.xor_false]
  have hword : ∀ (w : List Nat) (a : Idx n),
      chiV wordA v (w.foldl (fun c i => c * mgens.getD i 1) a) =
        xor (chiV wordA v a) (w.foldl (fun acc i => xor acc (v.getD i false)) false) := by
    intro w
    induction w with
    | nil => intro a; simp
    | cons i w ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih, hedge', foldl_xor_acc v w (xor false (v.getD i false))]
      cases chiV wordA v a <;> cases v.getD i false <;>
        cases w.foldl (fun acc i => xor acc (v.getD i false)) false <;> rfl
  have hhom : ∀ a b : Idx n, chiV wordA v (a * b) = xor (chiV wordA v a) (chiV wordA v b) := by
    intro a b
    have hb : evW mgens (wordA.getD b.v []) = b := hcov b
    have : a * b = (wordA.getD b.v []).foldl (fun c i => c * mgens.getD i 1) a := by
      conv_lhs => rw [← hb]
      unfold evW
      rw [← foldl_mul_assoc, mul_one]
    rw [this, hword]
    rfl
  by_cases hall : ∀ i, v.getD i false = false
  · left
    intro m
    rw [hmem m]
    have : chiV wordA v m = false := foldl_xor_false v hall _ false
    rw [this]; rfl
  · right
    obtain ⟨i0, hi0⟩ := not_forall.1 hall
    have hi0' : v.getD i0 false = true := by simpa using hi0
    have hi0lt : i0 < mgens.length := by
      by_contra hcon
      have : v.getD i0 false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : v.length ≤ i0)]
        rfl
      rw [this] at hi0'; exact Bool.false_ne_true hi0'
    let H : Subgroup (Idx n) :=
      { carrier := {m | chiV wordA v m = false}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          have ha' : chiV wordA v a = false := ha
          have hb' : chiV wordA v b = false := hb
          show chiV wordA v (a * b) = false
          rw [hhom, ha', hb']; rfl
        inv_mem' := fun {a} ha => by
          have ha' : chiV wordA v a = false := ha
          show chiV wordA v a⁻¹ = false
          have := hhom a⁻¹ a
          rw [inv_mul_cancel, h1, ha'] at this
          cases hc : chiV wordA v a⁻¹
          · rfl
          · rw [hc] at this; exact absurd this (by decide) }
    refine ⟨H, ?_, fun m => ?_⟩
    · rw [Subgroup.index_eq_two_iff]
      refine ⟨mgens.getD i0 1, fun b => ?_⟩
      show Xor (chiV wordA v (b * mgens.getD i0 1) = false) (chiV wordA v b = false)
      rw [hedge', hi0']
      cases chiV wordA v b <;> simp [Xor]
    · rw [hmem m]
      show chiV wordA v m = false ↔ (!chiV wordA v m) = true
      cases chiV wordA v m <;> simp

omit [Group (Idx n)] in
theorem getD_mem {α : Type} (l : List α) (d : α) {k : Nat} (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

structure EngSound (e : Eng n) (E : Idx n → Idx n → Prop) : Prop where
  invs_iff : ∀ u : Idx n, u ∈ e.invs ↔ isInv u = true
  csz_eq : ∀ a : Idx n, e.cszA.getD a.v 0 = cardC a
  reps_inv : ∀ k < e.reps.length, isInv (e.reps.getD k 1) = true
  ci_rep : ∀ k < e.reps.length, e.ciA.getD (e.reps.getD k 1).v 0 = k
  ci_lt : ∀ u : Idx n, isInv u = true → e.ciA.getD u.v 0 < e.reps.length
  ci_E : ∀ u : Idx n, isInv u = true → E u (e.reps.getD (e.ciA.getD u.v 0) 1)
  x_inv : isInv e.x = true
  x_max : ∀ i : Idx n, E e.x i → cardC i ≤ 32
  ctx_ok : ∀ k < e.reps.length, ctxOK (e.reps.getD k 1) (e.ctxs.getD k default) = true
  maxSubs_sound : ∀ Hm ∈ e.maxSubs, (∀ m : Idx n, Hm.getD m.v false = true) ∨
    ∃ H : Subgroup (Idx n), H.index = 2 ∧ ∀ m, m ∈ H ↔ Hm.getD m.v false = true

theorem engSound_mk
    (h : FusionHyp (Idx n) emb E) (hok : engOK (mkEng emb) = true) :
    EngSound (mkEng emb) E := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := engOK_spec hok
  have hinvs : ∀ u : Idx n, u ∈ (mkEng emb).invs ↔ isInv u = true := by
    intro u
    show u ∈ (elemsI n).filter isInv ↔ _
    simp [mem_elemsI]
  have hci : ∀ u : Idx n, isInv u = true →
      (mkEng emb).ciA.getD u.v 0 < (mkEng emb).reps.length ∧
        E u ((mkEng emb).reps.getD ((mkEng emb).ciA.getD u.v 0) 1) := by
    intro u hu
    obtain ⟨hlt, hmem⟩ := hC u ((hinvs u).2 hu)
    refine ⟨hlt, ?_⟩
    rw [members_getD emb _ hlt] at hmem
    have := bfs_mem (stepsOf (fuseOf emb))
      (fun x => E ((mkEng emb).reps.getD ((mkEng emb).ciA.getD u.v 0) 1) x)
      (fun x hx y hy => h.equiv.trans hx (stepsOf_E h _ (fuseOf_E h) x y hy)) _
      (h.equiv.refl _) u hmem
    exact h.equiv.symm this
  refine ⟨hinvs, fun a => by rw [hD a, cszI_eq], fun k hk => hA _ (getD_mem _ _ hk), hB,
    fun u hu => (hci u hu).1, fun u hu => (hci u hu).2, hG, fun i hi => ?_, hF,
    maxSubsOf_sound _ _ hE⟩
  exact h.xmax i hi

section Partition

open Classical

noncomputable def ldE (e : Eng n) (E : Idx n → Idx n → Prop) (k : Nat) : Nat :=
  if h : ∃ j, j < e.reps.length ∧ E (e.reps.getD j 1) (e.reps.getD k 1) then Nat.find h else k

variable {e : Eng n}

theorem ldE_spec (hE : Equivalence E) {k : Nat} (hk : k < e.reps.length) :
    ldE e E k < e.reps.length ∧ E (e.reps.getD (ldE e E k) 1) (e.reps.getD k 1) := by
  have hex : ∃ j, j < e.reps.length ∧ E (e.reps.getD j 1) (e.reps.getD k 1) :=
    ⟨k, hk, hE.refl _⟩
  unfold ldE
  simp only [hex, ↓reduceDIte]
  exact Nat.find_spec hex

theorem ldE_min (hE : Equivalence E) {k j : Nat} (hk : k < e.reps.length)
    (hj : j < e.reps.length) (hjk : E (e.reps.getD j 1) (e.reps.getD k 1)) : ldE e E k ≤ j := by
  have hex : ∃ j, j < e.reps.length ∧ E (e.reps.getD j 1) (e.reps.getD k 1) :=
    ⟨k, hk, hE.refl _⟩
  unfold ldE
  simp only [hex, ↓reduceDIte]
  exact Nat.find_min' hex ⟨hj, hjk⟩

theorem ldE_le (hE : Equivalence E) {k : Nat} (hk : k < e.reps.length) : ldE e E k ≤ k :=
  ldE_min hE hk hk (hE.refl _)

theorem ldE_eq_iff (hE : Equivalence E) {k k' : Nat} (hk : k < e.reps.length)
    (hk' : k' < e.reps.length) :
    ldE e E k = ldE e E k' ↔ E (e.reps.getD k 1) (e.reps.getD k' 1) := by
  obtain ⟨hl, hs⟩ := ldE_spec (e := e) hE hk
  obtain ⟨hl', hs'⟩ := ldE_spec (e := e) hE hk'
  constructor
  · intro heq
    rw [heq] at hs
    exact hE.trans (hE.symm hs) hs'
  · intro hkk
    apply le_antisymm
    · exact ldE_min hE hk hl' (hE.trans hs' (hE.symm hkk))
    · exact ldE_min hE hk' hl (hE.trans hs hkk)

theorem ldE_idem (hE : Equivalence E) {k : Nat} (hk : k < e.reps.length) :
    ldE e E (ldE e E k) = ldE e E k :=
  (ldE_eq_iff hE (ldE_spec (e := e) hE hk).1 hk).2 (ldE_spec (e := e) hE hk).2

end Partition

omit [Group (Idx n)] in
theorem getD_range_map (f : Nat → Nat) {K k : Nat} (hk : k < K) :
    ((List.range K).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

omit [Group (Idx n)] in
theorem mem_leaders (f : Nat → Nat) :
    ∀ m, (∀ k < m, f k ≤ k ∧ f (f k) = f k) → (List.range m).map f ∈ leaders m := by
  intro m
  induction m with
  | zero => intro _; simp [leaders]
  | succ m ih =>
    intro hf
    have ih' := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
    simp only [leaders, List.mem_flatMap]
    refine ⟨(List.range m).map f, ih', ?_⟩
    simp only [List.mem_map, List.mem_filter, List.mem_range]
    refine ⟨f m, ⟨?_, ?_⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hf m (Nat.lt_succ_self m)).1
    · by_cases hfm : f m = m
      · simp [hfm]
      · have hlt : f m < m := lt_of_le_of_ne (hf m (Nat.lt_succ_self m)).1 hfm
        rw [getD_range_map f hlt]
        simp [(hf m (Nat.lt_succ_self m)).2]
    · rw [List.range_succ, List.map_append]
      rfl

section Constraints

variable {e : Eng n} {E : Idx n → Idx n → Prop}

noncomputable def ldList (e : Eng n) (E : Idx n → Idx n → Prop) : List Nat :=
  (List.range e.reps.length).map (ldE e E)

theorem ldList_mem (hE : Equivalence E) : ldList e E ∈ leaders e.reps.length :=
  mem_leaders _ _ (fun _ hk => ⟨ldE_le hE hk, ldE_idem hE hk⟩)

theorem blkOf_ldList (hS : EngSound e E) {u : Idx n} (hu : isInv u = true) :
    blkOf e.ciA (ldList e E) u = ldE e E (e.ciA.getD u.v 0) := by
  unfold blkOf ldList
  exact getD_range_map _ (hS.ci_lt u hu)

theorem E_iff_blk (hS : EngSound e E) (hE : Equivalence E) {u v : Idx n} (hu : isInv u = true)
    (hv : isInv v = true) :
    E u v ↔ blkOf e.ciA (ldList e E) u = blkOf e.ciA (ldList e E) v := by
  rw [blkOf_ldList hS hu, blkOf_ldList hS hv, ldE_eq_iff hE (hS.ci_lt u hu) (hS.ci_lt v hv)]
  constructor
  · intro huv
    exact hE.trans (hE.symm (hS.ci_E u hu)) (hE.trans huv (hS.ci_E v hv))
  · intro hr
    exact hE.trans (hS.ci_E u hu) (hE.trans hr (hE.symm (hS.ci_E v hv)))

omit [Group (Idx n)] in
theorem foldl_cond_max_ge (c : Idx n → Nat) (p : Idx n → Prop) [DecidablePred p]
    (l : List (Idx n)) : ∀ m0, m0 ≤ l.foldl (fun m i => if p i then max m (c i) else m) m0 := by
  induction l with
  | nil => intro m0; exact le_refl _
  | cons x l ih =>
    intro m0
    simp only [List.foldl_cons]
    refine le_trans ?_ (ih _)
    split_ifs
    · exact le_max_left _ _
    · exact le_refl _

omit [Group (Idx n)] in
theorem le_foldl_cond_max (c : Idx n → Nat) (p : Idx n → Prop) [DecidablePred p]
    (l : List (Idx n)) :
    ∀ m0 i, i ∈ l → p i → c i ≤ l.foldl (fun m i => if p i then max m (c i) else m) m0 := by
  induction l with
  | nil => intro m0 i hi; cases hi
  | cons x l ih =>
    intro m0 i hi hpi
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · refine le_trans ?_ (foldl_cond_max_ge c p l _)
      simp [hpi]
    · exact ih _ i hi hpi

omit [Group (Idx n)] in
theorem foldl_cond_max_attained (c : Idx n → Nat) (p : Idx n → Prop) [DecidablePred p]
    (l : List (Idx n)) : ∀ m0, l.foldl (fun m i => if p i then max m (c i) else m) m0 = m0 ∨
      ∃ i ∈ l, p i ∧ c i = l.foldl (fun m i => if p i then max m (c i) else m) m0 := by
  induction l with
  | nil => intro m0; left; rfl
  | cons x l ih =>
    intro m0
    simp only [List.foldl_cons]
    by_cases hx : p x
    · simp only [hx, ite_true]
      rcases ih (max m0 (c x)) with h | ⟨i, hi, hpi, hci⟩
      · rcases max_choice m0 (c x) with hm | hm
        · left; rw [h, hm]
        · right; exact ⟨x, List.mem_cons_self, hx, by rw [h, hm]⟩
      · right; exact ⟨i, List.mem_cons_of_mem _ hi, hpi, hci⟩
    · simp only [hx, ite_false]
      rcases ih m0 with h | ⟨i, hi, hpi, hci⟩
      · left; exact h
      · right; exact ⟨i, List.mem_cons_of_mem _ hi, hpi, hci⟩

omit [Group (Idx n)] in
theorem le_cvalOf {ld : List Nat} {b : Nat} {i : Idx n} (hi : i ∈ e.invs)
    (hb : blkOf e.ciA ld i = b) : e.cszA.getD i.v 0 ≤ cvalOf e ld b :=
  le_foldl_cond_max (fun i => e.cszA.getD i.v 0) (fun i => blkOf e.ciA ld i = b) e.invs 0 i hi hb

theorem cvalOf_attained (hS : EngSound e E) {ld : List Nat} {b : Nat}
    (h0 : ∃ i ∈ e.invs, blkOf e.ciA ld i = b) :
    ∃ i ∈ e.invs, blkOf e.ciA ld i = b ∧ e.cszA.getD i.v 0 = cvalOf e ld b := by
  rcases foldl_cond_max_attained (fun i => e.cszA.getD i.v 0) (fun i => blkOf e.ciA ld i = b)
    e.invs 0 with h | h
  · obtain ⟨i0, hi0, hb0⟩ := h0
    have h1 := le_cvalOf (e := e) (ld := ld) hi0 hb0
    have hpos : 0 < e.cszA.getD i0.v 0 := by rw [hS.csz_eq]; exact Nat.card_pos
    have h2 : cvalOf e ld b = 0 := h
    omega
  · exact h

theorem xOK_of (hS : EngSound e E) {ld : List Nat}
    (hblk : ∀ u v : Idx n, isInv u = true → isInv v = true →
      (E u v ↔ blkOf e.ciA ld u = blkOf e.ciA ld v)) : xOK e ld = true := by
  simp only [xOK, List.all_eq_true]
  intro i hi
  by_cases hb : blkOf e.ciA ld i = blkOf e.ciA ld e.x
  · have hEi : E e.x i := (hblk e.x i hS.x_inv ((hS.invs_iff i).1 hi)).2 hb.symm
    have h32 : e.cszA.getD i.v 0 ≤ 32 := by
      have := hS.x_max i hEi
      rwa [← hS.csz_eq] at this
    simp only [decide_eq_true h32, Bool.or_true]
  · simp only [decide_eq_false hb, Bool.not_false, Bool.true_or]

theorem thompsonOK_of
    (h : FusionHyp (Idx n) emb E) (hS : EngSound e E) {ld : List Nat}
    (hblk : ∀ u v : Idx n, isInv u = true → isInv v = true →
      (E u v ↔ blkOf e.ciA ld u = blkOf e.ciA ld v)) : thompsonOK e ld = true := by
  simp only [thompsonOK, List.all_eq_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  intro Hm hHm u hu
  rcases hS.maxSubs_sound Hm hHm with hall | ⟨H, hH, hmemH⟩
  · exact Or.inl (hall u)
  · by_cases hu' : Hm.getD u.v false = true
    · exact Or.inl hu'
    · right
      have huI : isInv u = true := (hS.invs_iff u).1 hu
      obtain ⟨hu2, hu1⟩ := isInv_iff.1 huI
      have huH : u ∉ H := fun hm => hu' ((hmemH u).1 hm)
      obtain ⟨u', hu'H, hu'2, hu'1, hEu', hext⟩ := h.thompson_inv H hH huH hu2
      have hu'I : isInv u' = true := isInv_iff.2 ⟨hu'2, hu'1⟩
      have hb : blkOf e.ciA ld u' = blkOf e.ciA ld u := (hblk u' u hu'I huI).1 hEu'
      refine ⟨u', (hS.invs_iff u').2 hu'I, ⟨(hmemH u').1 hu'H, hb⟩, ?_⟩
      have h1 : e.cszA.getD u'.v 0 ≤ cvalOf e ld (blkOf e.ciA ld u) :=
        le_cvalOf ((hS.invs_iff u').2 hu'I) hb
      obtain ⟨i1, hi1, hbi1, hci1⟩ := cvalOf_attained hS
        (ld := ld) (b := blkOf e.ciA ld u) ⟨u', (hS.invs_iff u').2 hu'I, hb⟩
      have hi1I : isInv i1 = true := (hS.invs_iff i1).1 hi1
      have hEi1 : E u' i1 := (hblk u' i1 hu'I hi1I).2 (hb.trans hbi1.symm)
      obtain ⟨hi12, hi11⟩ := isInv_iff.1 hi1I
      have h2 : cardC i1 ≤ cardC u' := hext i1 hi12 hi11 hEi1
      rw [hS.csz_eq] at hci1
      have h3 := hS.csz_eq u'
      omega

end Constraints

section Hom

variable {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat} {t tp : Idx n}

theorem ctxOK_spec (h : ctxOK t ctx = true) :
    ctx.gens.getD 0 1 = t ∧ (∀ g ∈ ctx.gens, g * t = t * g) ∧
      ∀ j < ctx.gens.length, ∀ r ∈ ctx.R.getD j [],
        evW (ctx.gens.take (j + 1)) r.1 = evW (ctx.gens.take (j + 1)) r.2 := by
  simp only [ctxOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem getD_map_apply (ψ : Idx n → Idx n) (hψ1 : ψ 1 = 1) (gs : List (Idx n)) (i : Nat) :
    (gs.map ψ).getD i 1 = ψ (gs.getD i 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gs[i]? <;> simp [hψ1]

theorem evW_map (ψ : Idx n → Idx n) (t : Idx n) (hψ1 : ψ 1 = 1)
    (hψ : ∀ a b, a * t = t * a → b * t = t * b → ψ (a * b) = ψ a * ψ b)
    (gs : List (Idx n)) (hgs : ∀ g ∈ gs, g * t = t * g) (w : List Nat) :
    evW gs w * t = t * evW gs w ∧ evW (gs.map ψ) w = ψ (evW gs w) := by
  have key : ∀ (w : List Nat) (a : Idx n), a * t = t * a →
      (w.foldl (fun c i => c * gs.getD i 1) a) * t = t * (w.foldl (fun c i => c * gs.getD i 1) a) ∧
      w.foldl (fun c i => c * (gs.map ψ).getD i 1) (ψ a) =
        ψ (w.foldl (fun c i => c * gs.getD i 1) a) := by
    intro w
    induction w with
    | nil => intro a ha; exact ⟨ha, rfl⟩
    | cons i w ih =>
      intro a ha
      simp only [List.foldl_cons]
      have hgi : gs.getD i 1 * t = t * gs.getD i 1 := by
        by_cases hi : i < gs.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          exact hgs _ (List.getElem_mem hi)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : gs.length ≤ i)]
          simp
      have hac : (a * gs.getD i 1) * t = t * (a * gs.getD i 1) := by
        rw [mul_assoc, hgi, ← mul_assoc, ha, mul_assoc]
      rw [getD_map_apply ψ hψ1, ← hψ a _ ha hgi]
      exact ih _ hac
  obtain ⟨k1, k2⟩ := key w 1 (by rw [one_mul, mul_one])
  rw [hψ1] at k2
  exact ⟨k1, k2⟩

theorem candOK_of_map (hctx : ctxOK t ctx = true)
    (ψ : Idx n → Idx n) (hψ1 : ψ 1 = 1)
    (hψ : ∀ a b, a * t = t * a → b * t = t * b → ψ (a * b) = ψ a * ψ b)
    (hker : ∀ a, a * t = t * a → a ≠ 1 → ψ a ≠ 1)
    (hinv : ∀ a, a * t = t * a → isInv a = true →
      isInv (ψ a) = true ∧ blkOf ci ld (ψ a) = blkOf ci ld a)
    {j : Nat} (hj1 : 1 ≤ j) (hjr : j ≤ ctx.gens.length) :
    candOK ctx ci ld j ((ctx.gens.take j).map ψ) = true := by
  obtain ⟨-, hgc, hrel⟩ := ctxOK_spec hctx
  have hgs : ∀ g ∈ ctx.gens.take j, g * t = t * g := fun g hg => hgc g (List.mem_of_mem_take hg)
  have hev := fun w => evW_map ψ t hψ1 hψ (ctx.gens.take j) hgs w
  unfold candOK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro rr hrr
    rw [decide_eq_true_eq, (hev rr.1).2, (hev rr.2).2]
    have := hrel (j - 1) (by omega) rr hrr
    rw [show j - 1 + 1 = j by omega] at this
    rw [this]
  · rw [List.all_eq_true]
    intro w _
    obtain ⟨hc, hm⟩ := hev w
    rw [hm]
    set e0 := evW (ctx.gens.take j) w with he0
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h1 : e0 = 1
      · exact Or.inl h1
      · exact Or.inr (hker e0 hc h1)
    · by_cases h1 : isInv e0 = true
      · right
        obtain ⟨h2, h3⟩ := hinv e0 hc h1
        simp [h2, h3]
      · left; simpa using h1
    · by_cases h1 : isInv (e0 * e0) = true
      · right
        have hcc : e0 * e0 * t = t * (e0 * e0) := by
          rw [mul_assoc, hc, ← mul_assoc, hc, mul_assoc]
        obtain ⟨h2, h3⟩ := hinv (e0 * e0) hcc h1
        rw [hψ e0 e0 hc hc] at h2 h3
        simp [h2, h3]
      · left; simpa using h1

theorem homExists_complete (hr : 0 < ctx.gens.length) (hctx : ctxOK t ctx = true)
    (ψ : Idx n → Idx n) (hψ1 : ψ 1 = 1)
    (hψ : ∀ a b, a * t = t * a → b * t = t * b → ψ (a * b) = ψ a * ψ b)
    (hψt : ψ t = tp) (hψc : ∀ a, a * t = t * a → ψ a * tp = tp * ψ a)
    (hker : ∀ a, a * t = t * a → a ≠ 1 → ψ a ≠ 1)
    (hinv : ∀ a, a * t = t * a → isInv a = true →
      isInv (ψ a) = true ∧ blkOf ci ld (ψ a) = blkOf ci ld a) :
    homExists ctx ci ld tp = true := by
  obtain ⟨hg0, hgc, -⟩ := ctxOK_spec hctx
  obtain ⟨g0, gs0, hgens⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hr)
  have hg0t : g0 = t := by rw [hgens] at hg0; exact hg0
  set cands : List (Idx n) := (elemsI n).filter fun c => decide (c * tp = tp * c) with hcands
  have main : ∀ d j, 1 ≤ j → j + d = ctx.gens.length →
      homGo ctx ci ld cands d j ((ctx.gens.take j).map ψ) = true := by
    intro d
    induction d with
    | zero =>
      intro j hj1 hjd
      unfold homGo
      exact candOK_of_map hctx ψ hψ1 hψ hker hinv hj1 (by omega)
    | succ d ih =>
      intro j hj1 hjd
      unfold homGo
      rw [Bool.and_eq_true]
      refine ⟨candOK_of_map hctx ψ hψ1 hψ hker hinv hj1 (by omega), ?_⟩
      rw [List.any_eq_true]
      have hjlt : j < ctx.gens.length := by omega
      refine ⟨ψ (ctx.gens.getD j 1), ?_, ?_⟩
      · rw [hcands, List.mem_filter]
        refine ⟨mem_elemsI _, ?_⟩
        rw [decide_eq_true_eq]
        have hgj : ctx.gens.getD j 1 * t = t * ctx.gens.getD j 1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
          exact hgc _ (List.getElem_mem hjlt)
        exact hψc _ hgj
      · have : (ctx.gens.take j).map ψ ++ [ψ (ctx.gens.getD j 1)] =
            (ctx.gens.take (j + 1)).map ψ := by
          rw [List.take_add_one, List.map_append, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hjlt]
          rfl
        rw [this]
        exact ih (j + 1) (by omega) (by omega)
  have h1 := main (ctx.gens.length - 1) 1 (le_refl _) (by omega)
  have htake : (ctx.gens.take 1).map ψ = [tp] := by
    rw [hgens, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, hg0t, hψt]
  rw [htake] at h1
  unfold homExists
  exact h1

theorem ctxOK_pos (h : ctxOK t ctx = true) (ht1 : t ≠ 1) : 0 < ctx.gens.length := by
  obtain ⟨hg0, -, -⟩ := ctxOK_spec h
  by_contra hcon
  have : ctx.gens = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [this] at hg0
  exact ht1 hg0.symm

theorem homExists_of_hom (hr : 0 < ctx.gens.length) (hctx : ctxOK t ctx = true)
    (φ : ↥(Subgroup.centralizer ({t} : Set (Idx n))) →*
      ↥(Subgroup.centralizer ({tp} : Set (Idx n))))
    (hinj : Function.Injective φ)
    (hφt : (φ ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : Idx n) = tp)
    (hinv : ∀ s : ↥(Subgroup.centralizer ({t} : Set (Idx n))), isInv (s : Idx n) = true →
      isInv (φ s : Idx n) = true ∧ blkOf ci ld (φ s : Idx n) = blkOf ci ld (s : Idx n)) :
    homExists ctx ci ld tp = true := by
  classical
  let ψ : Idx n → Idx n := fun a =>
    if h : a * t = t * a then
      (φ ⟨a, Subgroup.mem_centralizer_singleton_iff.2 h⟩ : Idx n) else 1
  have hψa : ∀ a (h : a * t = t * a),
      ψ a = (φ ⟨a, Subgroup.mem_centralizer_singleton_iff.2 h⟩ : Idx n) := by
    intro a h
    simp only [ψ, h, ↓reduceDIte]
  have h1t : (1 : Idx n) * t = t * 1 := by rw [one_mul, mul_one]
  have hψ1 : ψ 1 = 1 := by
    rw [hψa 1 h1t]
    show ((φ (1 : ↥(Subgroup.centralizer ({t} : Set (Idx n)))) :
      ↥(Subgroup.centralizer ({tp} : Set (Idx n)))) : Idx n) = 1
    rw [map_one]
    rfl
  have hψ : ∀ a b, a * t = t * a → b * t = t * b → ψ (a * b) = ψ a * ψ b := by
    intro a b ha hb
    have hab : a * b * t = t * (a * b) := by rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    rw [hψa (a * b) hab, hψa a ha, hψa b hb]
    show ((φ (⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha⟩ *
      ⟨b, Subgroup.mem_centralizer_singleton_iff.2 hb⟩) :
      ↥(Subgroup.centralizer ({tp} : Set (Idx n)))) : Idx n) = _
    rw [map_mul]
    rfl
  have hψt : ψ t = tp := by
    rw [hψa t rfl]
    exact hφt
  have hψc : ∀ a, a * t = t * a → ψ a * tp = tp * ψ a := by
    intro a ha
    rw [hψa a ha]
    exact Subgroup.mem_centralizer_singleton_iff.1 (φ _).2
  have hker : ∀ a, a * t = t * a → a ≠ 1 → ψ a ≠ 1 := by
    intro a ha ha1 hψ1'
    rw [hψa a ha] at hψ1'
    have h3 : φ ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha⟩ = 1 := Subtype.ext hψ1'
    have h4 := hinj (h3.trans (map_one φ).symm)
    exact ha1 (congrArg Subtype.val h4)
  have hinv' : ∀ a, a * t = t * a → isInv a = true →
      isInv (ψ a) = true ∧ blkOf ci ld (ψ a) = blkOf ci ld a := by
    intro a ha hI
    rw [hψa a ha]
    exact hinv ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha⟩ hI
  exact homExists_complete hr hctx ψ hψ1 hψ hψt hψc hker hinv'

end Hom

section Scp

variable {e : Eng n} {E : Idx n → Idx n → Prop}

theorem scpOK_of
    (h : FusionHyp (Idx n) emb E) (hS : EngSound e E) {ld : List Nat}
    (hblk : ∀ u v : Idx n, isInv u = true → isInv v = true →
      (E u v ↔ blkOf e.ciA ld u = blkOf e.ciA ld v)) : scpOK e ld = true := by
  simp only [scpOK, List.all_eq_true, List.mem_range]
  intro k hk
  have htI : isInv (e.reps.getD k 1) = true := hS.reps_inv k hk
  obtain ⟨ht2, ht1⟩ := isInv_iff.1 htI
  have hbt : blkOf e.ciA ld (e.reps.getD k 1) = ld.getD k 0 := by
    unfold blkOf
    rw [hS.ci_rep k hk]
  have htin : e.reps.getD k 1 ∈ e.invs := (hS.invs_iff _).2 htI
  obtain ⟨tp0, htp0, hbtp0, hctp0⟩ := cvalOf_attained hS (ld := ld) (b := ld.getD k 0)
    ⟨_, htin, hbt⟩
  have hfind : ∃ x ∈ e.invs, (decide (blkOf e.ciA ld x = ld.getD k 0) &&
      decide (e.cszA.getD x.v 0 = cvalOf e ld (ld.getD k 0))) = true :=
    ⟨tp0, htp0, by simp [hbtp0, hctp0]⟩
  obtain ⟨tp, htp⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 hfind)
  have htp' := List.find?_some htp
  have htpin : tp ∈ e.invs := List.mem_of_find?_eq_some htp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htp'
  obtain ⟨hbtp, hctp⟩ := htp'
  have htpeq : tpOf e ld (ld.getD k 0) = tp := by
    unfold tpOf
    rw [htp]
    rfl
  rw [htpeq]
  have htpI : isInv tp = true := (hS.invs_iff tp).1 htpin
  obtain ⟨htp2, htp1⟩ := isInv_iff.1 htpI
  have hEt : E (e.reps.getD k 1) tp := (hblk _ tp htI htpI).2 (hbt.trans hbtp.symm)
  have hmax : ∀ i : Idx n, i * i = 1 → i ≠ 1 → E tp i → cardC i ≤ cardC tp := by
    intro i hi2 hi1 hEi
    have hiI : isInv i = true := isInv_iff.2 ⟨hi2, hi1⟩
    have hbi : blkOf e.ciA ld i = blkOf e.ciA ld tp := ((hblk tp i htpI hiI).1 hEi).symm
    have h1 := le_cvalOf (e := e) ((hS.invs_iff i).2 hiI) (hbi.trans hbtp)
    rw [hS.csz_eq] at h1
    rw [hS.csz_eq] at hctp
    omega
  obtain ⟨φ, hinj, hφt, hφE⟩ := h.scp_inv ht2 hEt htp2 htp1 hmax
  have hinv : ∀ s : ↥(Subgroup.centralizer ({e.reps.getD k 1} : Set (Idx n))),
      isInv (s : Idx n) = true → isInv (φ s : Idx n) = true ∧
        blkOf e.ciA ld (φ s : Idx n) = blkOf e.ciA ld (s : Idx n) := by
    intro s hs
    obtain ⟨hs2, hs1⟩ := isInv_iff.1 hs
    have hss : s * s = 1 := Subtype.ext hs2
    have h2 : (φ s : Idx n) * (φ s : Idx n) = 1 := by
      have := congrArg (fun x => ((φ x : ↥(Subgroup.centralizer ({tp} : Set (Idx n)))) : Idx n))
        hss
      simpa [map_mul] using this
    have h1 : (φ s : Idx n) ≠ 1 := by
      intro hc
      have h3 : φ s = 1 := Subtype.ext hc
      have h4 := hinj (h3.trans (map_one φ).symm)
      exact hs1 (by simpa using congrArg Subtype.val h4)
    have hφI : isInv (φ s : Idx n) = true := isInv_iff.2 ⟨h2, h1⟩
    exact ⟨hφI, (hblk _ _ hφI hs).1 (hφE s)⟩
  exact homExists_of_hom (ctxOK_pos (hS.ctx_ok k hk) ht1) (hS.ctx_ok k hk) φ hinj hφt hinv

end Scp

theorem fusion_core
    {emb : ↥T5 →* Idx n} {E : Idx n → Idx n → Prop}
    (h : FusionHyp (Idx n) emb E) (hok : engOK (mkEng emb) = true) :
    ∃ ld ∈ leaders (mkEng emb).reps.length, feasible (mkEng emb) ld = true ∧
      ∀ u v : Idx n, isInv u = true → isInv v = true →
        (E u v ↔ blkOf (mkEng emb).ciA ld u = blkOf (mkEng emb).ciA ld v) := by
  have hS := engSound_mk h hok
  have hblk : ∀ u v : Idx n, isInv u = true → isInv v = true →
      (E u v ↔ blkOf (mkEng emb).ciA (ldList (mkEng emb) E) u =
        blkOf (mkEng emb).ciA (ldList (mkEng emb) E) v) :=
    fun u v hu hv => E_iff_blk hS h.equiv hu hv
  refine ⟨ldList (mkEng emb) E, ldList_mem h.equiv, ?_, hblk⟩
  unfold feasible
  simp only [Bool.and_eq_true]
  exact ⟨⟨xOK_of hS hblk, thompsonOK_of h hS hblk⟩, scpOK_of h hS hblk⟩

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
