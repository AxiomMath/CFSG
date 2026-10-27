module

public section

namespace CFSG.KTabPack

abbrev Tab : Type := List Nat

@[expose] def tm (s t : Tab) : Tab := t.map fun j => s.getD j 0

@[expose] def extT (sp : List Tab) (g : Tab) : List Tab := sp ++ sp.map (tm g)

@[expose] def isInvT (n : Nat) (t : Tab) : Bool :=
  decide (t ≠ List.range n ∧ tm t t = List.range n)

@[expose] def commT (s t : Tab) : Bool := decide (tm s t = tm t s)

@[expose] def spanT (n : Nat) : List Tab → List Tab
  | [] => [List.range n]
  | g :: gs => extT (spanT n gs) g

@[expose] def sylowT (n : Nat) (gs : List Tab) : Bool :=
  decide ((spanT n gs).length = 128 ∧ (spanT n gs).Nodup ∧
    ∀ l ∈ spanT n gs, ∀ g ∈ gs, tm l g ∈ spanT n gs)

@[expose] def elemAbT (n : Nat) (L : List Tab) (As : List (List Tab)) : Bool :=
  let I := L.filter (isInvT n)
  I.all fun a =>
    let Ia := I.filter (commT a)
    let P1 := extT [List.range n] a
    Ia.all fun b =>
      if decide (b ∉ P1) then
        let Ib := Ia.filter (commT b)
        let P2 := extT P1 b
        Ib.all fun c =>
          if decide (c ∉ P2) then
            let Ic := Ib.filter (commT c)
            let P3 := extT P2 c
            Ic.all fun d =>
              if decide (d ∉ P3) then
                let P4 := extT P3 d
                As.any fun A => A.all fun y => decide (y ∈ P4)
              else true
          else true
      else true

@[expose] noncomputable def enc : List Nat → Nat := List.rec 0 fun x _ ih => x + (ih <<< 5)

@[expose] def rd (c j : Nat) : Nat := (c >>> (5 * j)) &&& 31

@[expose] noncomputable def pmK (s : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih t => rd s (t &&& 31) + (ih (t >>> 5) <<< 5)) k

@[expose] noncomputable def allR {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun x _ ih => p x && ih

@[expose] noncomputable def anyR {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec false fun x _ ih => p x || ih

@[expose] noncomputable def filterR (p : Nat → Bool) : List Nat → List Nat :=
  List.rec [] fun x _ ih => Bool.rec ih (x :: ih) (p x)

@[expose] noncomputable def mapR (f : Nat → Nat) : List Nat → List Nat :=
  List.rec [] fun x _ ih => f x :: ih

@[expose] noncomputable def memN (y : Nat) : List Nat → Bool := List.rec false fun x _ ih => Nat.beq y x || ih

@[expose] noncomputable def nodupN : List Nat → Bool := List.rec true fun x l ih => !memN x l && ih

@[expose] noncomputable def extN (n : Nat) (sp : List Nat) (g : Nat) : List Nat := sp ++ mapR (pmK g n) sp

@[expose] noncomputable def isInvN (n : Nat) (t : Nat) : Bool :=
  !Nat.beq t (enc (List.range n)) && Nat.beq (pmK t n t) (enc (List.range n))

@[expose] noncomputable def commN (n : Nat) (s t : Nat) : Bool := Nat.beq (pmK s n t) (pmK t n s)

@[expose] noncomputable def elemAbN (n : Nat) (L : List Nat) (As : List (List Nat)) : Bool :=
  let I := filterR (isInvN n) L
  allR (fun a =>
    let Ia := filterR (commN n a) I
    let P1 := extN n [enc (List.range n)] a
    allR (fun b =>
      if !memN b P1 then
        let Ib := filterR (commN n b) Ia
        let P2 := extN n P1 b
        allR (fun c =>
          if !memN c P2 then
            let Ic := filterR (commN n c) Ib
            let P3 := extN n P2 c
            allR (fun d =>
              if !memN d P3 then
                let P4 := extN n P3 d
                anyR (fun A => allR (fun y => memN y P4) A) As
              else true) Ic
          else true) Ib
      else true) Ia) I

@[expose] noncomputable def spanN (n : Nat) : List Nat → List Nat :=
  List.rec [enc (List.range n)] fun g _ ih => extN n ih g

@[expose] noncomputable def sylowN (n : Nat) (gs : List Nat) : Bool :=
  let S := spanN n gs
  Nat.beq (List.length S) 128 && nodupN S && allR (fun l => allR (fun g => memN (pmK l n g) S) gs) S

theorem allR_eq {α : Type} (p : α → Bool) (l : List α) : allR p l = l.all p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [allR, List.all_cons] at *; rw [← ih]

theorem anyR_eq {α : Type} (p : α → Bool) (l : List α) : anyR p l = l.any p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [anyR, List.any_cons] at *; rw [← ih]

theorem filterR_eq (p : Nat → Bool) (l : List Nat) : filterR p l = l.filter p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [filterR, List.filter_cons] at *
    cases p x <;> simp [ih]

theorem mapR_eq (f : Nat → Nat) (l : List Nat) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [mapR, List.map_cons] at *; rw [← ih]

theorem memN_eq (y : Nat) (l : List Nat) : memN y l = decide (y ∈ l) := by
  induction l with
  | nil => simp [memN]
  | cons x l ih =>
    change (Nat.beq y x || memN y l) = _
    rw [ih]
    apply Bool.eq_iff_iff.2
    simp [Nat.beq_eq]

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.any_cons, List.any_cons, h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem nodupN_eq (l : List Nat) : nodupN l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupN]
  | cons x l ih =>
    simp only [nodupN, List.nodup_cons] at *
    rw [← ih, memN_eq]
    simp

@[expose] def W (n : Nat) (t : Tab) : Prop := t.length = n ∧ ∀ j ∈ t, j < 32

theorem enc_cons (x : Nat) (l : List Nat) : enc (x :: l) = x + (enc l <<< 5) := rfl

theorem lane_and {x m : Nat} (hx : x < 32) : (x + (m <<< 5)) &&& 31 = x := by
  have h := Nat.and_two_pow_sub_one_eq_mod (x + (m <<< 5)) 5
  simp only [Nat.reducePow, Nat.reduceSub] at h
  rw [h, Nat.shiftLeft_eq]
  omega

theorem lane_shr {x m : Nat} (hx : x < 32) : (x + (m <<< 5)) >>> 5 = m := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  omega

theorem rd_enc (s : List Nat) (hs : ∀ j ∈ s, j < 32) (j : Nat) : rd (enc s) j = s.getD j 0 := by
  induction s generalizing j with
  | nil => simp [rd, enc]
  | cons x l ih =>
    have hx : x < 32 := hs x (List.mem_cons_self ..)
    have hl : ∀ j ∈ l, j < 32 := fun j hj => hs j (List.mem_cons_of_mem _ hj)
    cases j with
    | zero => simp only [rd, Nat.mul_zero, Nat.shiftRight_zero, enc_cons, lane_and hx]; rfl
    | succ j =>
      have h5 : 5 * (j + 1) = 5 + 5 * j := by omega
      simp only [rd, h5, Nat.shiftRight_add, enc_cons, lane_shr hx, List.getD_cons_succ]
      exact ih hl j

theorem pmK_enc (s : Nat) (t : List Nat) (ht : ∀ j ∈ t, j < 32) :
    pmK s t.length (enc t) = enc (t.map fun j => rd s j) := by
  induction t with
  | nil => rfl
  | cons x l ih =>
    have hx : x < 32 := ht x (List.mem_cons_self ..)
    have hl : ∀ j ∈ l, j < 32 := fun j hj => ht j (List.mem_cons_of_mem _ hj)
    change rd s ((x + (enc l <<< 5)) &&& 31) + (pmK s l.length ((x + (enc l <<< 5)) >>> 5) <<< 5) = _
    rw [lane_and hx, lane_shr hx, ih hl]
    rfl

theorem W_tm {n : Nat} {s t : Tab} (hs : W n s) (ht : W n t) : W n (tm s t) := by
  refine ⟨by simp [tm, ht.1], ?_⟩
  intro j hj
  simp only [tm, List.mem_map] at hj
  obtain ⟨i, -, rfl⟩ := hj
  rw [List.getD_eq_getElem?_getD]
  cases h : s[i]? with
  | none => simp
  | some v => exact hs.2 v (List.mem_of_getElem? h)

theorem enc_tm {n : Nat} {s t : Tab} (hs : W n s) (ht : W n t) :
    enc (tm s t) = pmK (enc s) n (enc t) := by
  rw [← ht.1, pmK_enc _ _ ht.2, tm]
  congr 1
  exact List.map_congr_left fun j _ => (rd_enc s hs.2 j).symm

theorem enc_inj : ∀ {x y : List Nat}, x.length = y.length → (∀ j ∈ x, j < 32) →
    (∀ j ∈ y, j < 32) → enc x = enc y → x = y
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: x, b :: y, hl, hx, hy, h => by
    have ha : a < 32 := hx a (List.mem_cons_self ..)
    have hb : b < 32 := hy b (List.mem_cons_self ..)
    rw [enc_cons, enc_cons] at h
    have h1 := congrArg (· &&& 31) h
    have h2 := congrArg (· >>> 5) h
    simp only [lane_and ha, lane_and hb] at h1
    simp only [lane_shr ha, lane_shr hb] at h2
    rw [h1, enc_inj (by simpa using hl) (fun j hj => hx j (List.mem_cons_of_mem _ hj))
      (fun j hj => hy j (List.mem_cons_of_mem _ hj)) h2]

theorem decide_eq_enc {n : Nat} {x y : Tab} (hx : W n x) (hy : W n y) :
    decide (x = y) = Nat.beq (enc x) (enc y) := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, Nat.beq_eq]
  exact ⟨congrArg enc, enc_inj (hx.1.trans hy.1.symm) hx.2 hy.2⟩

theorem decide_mem_enc {n : Nat} {y : Tab} {P : List Tab} (hy : W n y) (hP : ∀ x ∈ P, W n x) :
    decide (y ∈ P) = memN (enc y) (P.map enc) := by
  rw [memN_eq]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, decide_eq_true_iff, List.mem_map]
  refine ⟨fun h => ⟨y, h, rfl⟩, fun ⟨x, hx, e⟩ => ?_⟩
  rwa [← enc_inj ((hP x hx).1.trans hy.1.symm) (hP x hx).2 hy.2 e]

theorem W_range {n : Nat} (hn : n ≤ 32) : W n (List.range n) :=
  ⟨List.length_range, fun j hj => by have := List.mem_range.1 hj; omega⟩

theorem extT_W {n : Nat} {P : List Tab} {g : Tab} (hP : ∀ x ∈ P, W n x) (hg : W n g) :
    ∀ x ∈ extT P g, W n x := by
  intro x hx
  simp only [extT, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨t, ht, rfl⟩
  · exact hP x hx
  · exact W_tm hg (hP t ht)

theorem extT_enc {n : Nat} {P : List Tab} {g : Tab} (hP : ∀ x ∈ P, W n x) (hg : W n g) :
    (extT P g).map enc = extN n (P.map enc) (enc g) := by
  simp only [extT, extN, List.map_append, mapR_eq, List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => enc_tm hg (hP t ht)

theorem all_enc {n : Nat} {I : List Tab} {f : Tab → Bool} {g : Nat → Bool}
    (hI : ∀ x ∈ I, W n x) (h : ∀ x ∈ I, f x = g (enc x)) : I.all f = allR g (I.map enc) := by
  rw [allR_eq, List.all_map]
  induction I with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, Function.comp]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => hI y (List.mem_cons_of_mem _ hy))
      (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem filter_enc {I : List Tab} {f : Tab → Bool} {g : Nat → Bool}
    (h : ∀ x ∈ I, f x = g (enc x)) : (I.filter f).map enc = filterR g (I.map enc) := by
  rw [filterR_eq, List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => h x hx

theorem filter_W {n : Nat} {I : List Tab} {f : Tab → Bool} (hI : ∀ x ∈ I, W n x) :
    ∀ x ∈ I.filter f, W n x := fun x hx => hI x (List.mem_filter.1 hx).1

theorem comm_enc {n : Nat} {s t : Tab} (hs : W n s) (ht : W n t) :
    commT s t = commN n (enc s) (enc t) := by
  rw [commT, commN, decide_eq_enc (W_tm hs ht) (W_tm ht hs), enc_tm hs ht, enc_tm ht hs]

theorem isInv_enc {n : Nat} (hn : n ≤ 32) {t : Tab} (ht : W n t) :
    isInvT n t = isInvN n (enc t) := by
  simp only [isInvT, isInvN, ne_eq, Bool.decide_and, decide_not]
  rw [decide_eq_enc ht (W_range hn),
    decide_eq_enc (W_tm ht ht) (W_range hn), enc_tm ht ht]

theorem not_mem_enc {n : Nat} {y : Tab} {P : List Tab} (hy : W n y) (hP : ∀ x ∈ P, W n x) :
    decide (y ∉ P) = !memN (enc y) (P.map enc) := by
  rw [decide_not, decide_mem_enc hy hP]

theorem elemAbT_eq {n : Nat} (hn : n ≤ 32) {L : List Tab} {As : List (List Tab)}
    (hL : ∀ x ∈ L, W n x) (hA : ∀ A ∈ As, ∀ y ∈ A, W n y) :
    elemAbT n L As = elemAbN n (L.map enc) (As.map (List.map enc)) := by
  have hr := W_range hn
  have hI := filter_W (f := isInvT n) hL
  simp only [elemAbT, elemAbN]
  rw [← filter_enc (fun x hx => isInv_enc hn (hL x hx))]
  refine all_enc hI fun a ha => ?_
  have hIa := filter_W (f := commT a) hI
  have hP1 := extT_W (P := [List.range n]) (by simpa using hr) (hI a ha)
  have h1 : [enc (List.range n)] = [List.range n].map enc := rfl
  rw [← filter_enc (fun x hx => comm_enc (hI a ha) (hI x hx)), h1,
    ← extT_enc (by simpa using hr) (hI a ha)]
  refine all_enc hIa fun b hb => ?_
  rw [not_mem_enc (hIa b hb) hP1]
  congr 1
  have hIb := filter_W (f := commT b) hIa
  have hP2 := extT_W hP1 (hIa b hb)
  rw [← filter_enc (fun x hx => comm_enc (hIa b hb) (hIa x hx)),
    ← extT_enc hP1 (hIa b hb)]
  refine all_enc hIb fun c hc => ?_
  rw [not_mem_enc (hIb c hc) hP2]
  congr 1
  have hIc := filter_W (f := commT c) hIb
  have hP3 := extT_W hP2 (hIb c hc)
  rw [← filter_enc (fun x hx => comm_enc (hIb c hc) (hIb x hx)),
    ← extT_enc hP2 (hIb c hc)]
  refine all_enc hIc fun d hd => ?_
  rw [not_mem_enc (hIc d hd) hP3]
  congr 1
  have hP4 := extT_W hP3 (hIc d hd)
  rw [← extT_enc hP3 (hIc d hd), anyR_eq, List.any_map]
  refine any_congr_mem fun A hA' => ?_
  exact all_enc (g := fun z => memN z (List.map enc _)) (hA A hA')
    (fun y hy => decide_mem_enc (hA A hA' y hy) hP4)

theorem spanT_W {n : Nat} (hn : n ≤ 32) {gs : List Tab} (hg : ∀ g ∈ gs, W n g) :
    ∀ x ∈ spanT n gs, W n x := by
  induction gs with
  | nil => simpa [spanT] using W_range hn
  | cons g gs ih =>
    exact extT_W (ih fun x hx => hg x (List.mem_cons_of_mem _ hx)) (hg g (List.mem_cons_self ..))

theorem spanT_enc {n : Nat} (hn : n ≤ 32) {gs : List Tab} (hg : ∀ g ∈ gs, W n g) :
    (spanT n gs).map enc = spanN n (gs.map enc) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg' : ∀ x ∈ gs, W n x := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rw [spanT, extT_enc (spanT_W hn hg') (hg g (List.mem_cons_self ..)), ih hg']
    rfl

theorem sylowT_of_N {n : Nat} (hn : n ≤ 32) {gs : List Tab} (hg : ∀ g ∈ gs, W n g)
    (h : sylowN n (gs.map enc) = true) : sylowT n gs = true := by
  have hS := spanT_W hn hg
  simp only [sylowN] at h
  rw [← spanT_enc hn hg] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.length_map, nodupN_eq, allR_eq, List.all_map,
    List.all_eq_true, Function.comp_apply, memN_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine decide_eq_true ⟨h1, List.Pairwise.of_map enc (fun a b e => fun hab => e (hab ▸ rfl)) h2,
    fun l hl g hg' => ?_⟩
  have h4 := h3 l hl g hg'
  rw [← enc_tm (hS l hl) (hg g hg'), List.mem_map] at h4
  obtain ⟨x, hx, e⟩ := h4
  rwa [← enc_inj ((hS x hx).1.trans (W_tm (hS l hl) (hg g hg')).1.symm) (hS x hx).2
    (W_tm (hS l hl) (hg g hg')).2 e]

end CFSG.KTabPack
