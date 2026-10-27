module

public import CFSG.Certificates.Kernel.Census.ExcProof
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Census.ToMainConj

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat}

theorem pid_good24 (hw : n ≤ 2 ^ w) (h24 : n ≤ 2 ^ 24) :
    unpackP n w (pid n w) = idA n ∧ canon1 n w (pid n w) = true ∧
      ∀ i < n, at' w (pid n w) i = i := by
  have hf := fld_pid (n := n) hw
  have hval : ∀ i, (if i < 2 ^ clog n then (if i < n then i else 0) else 0) < 2 ^ w := by
    intro i
    split
    · split
      · omega
      · exact Nat.two_pow_pos w
    · exact Nat.two_pow_pos w
  have hat : ∀ i, at' w (pid n w) i =
      if i < 2 ^ clog n then (if i < n then i else 0) else 0 :=
    fun i => CFSG.KS.PackFld.pg_of_fld hf (hval i)
  have hc : n ≤ 2 ^ clog n := by
    rcases clog_spec' n with h | h
    · rw [h]
      exact h24
    · exact h
  have hid : ∀ i < n, at' w (pid n w) i = i := fun i hi => by
    rw [hat i]
    simp only [show i < 2 ^ clog n by omega, hi, ↓reduceIte]
  refine ⟨?_, ?_, hid⟩
  · apply Array.ext
    · simp [unpackP_size, idA]
    · intro i h1 _
      have hi : i < n := by simpa [unpackP_size] using h1
      have := unpackP_get (n := n) (w := w) (pid n w) i
      rw [getElem!_pos _ _ (by rw [unpackP_size]; exact hi)] at this
      simp only [hi, ↓reduceIte, hid i hi] at this
      rw [this]
      simp [idA]
  · rcases Nat.eq_zero_or_pos w with rfl | hw0
    · have hn1 : n ≤ 1 := by simpa using hw
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · decide +kernel
      · decide +kernel
    · unfold canon1
      rw [Nat.beq_eq]
      exact CFSG.KS.PackFld.shr_zero_of_fld hw0 hf fun i hi => by
        have : ¬ i < n := by omega
        simp [this]

theorem all_of {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = true → g a = true)
    (hf : l.all f = true) : l.all g = true :=
  List.all_eq_true.2 fun a ha => h a ha (List.all_eq_true.1 hf a ha)

theorem idA_get {i : Nat} (hi : i < n) : (idA n)[i]! = i := by
  rw [getElem!_pos _ i (by simpa [idA] using hi)]
  simp [idA]

theorem compA_get {t u : Array Nat} {i : Nat} (hi : i < n) : (compA n t u)[i]! = t[u[i]!]! := by
  rw [getElem!_pos _ i (by simpa [compA] using hi)]
  simp [compA]

variable (G : Good n w)
include G

theorem ppcA_eq : ∀ (l : List Nat) (m : Nat), (∀ x ∈ l, canon1 n w x = true) →
    unpackP n w (ppcA n w l m) = pcA n (l.map (unpackP n w)) m ∧
      canon1 n w (ppcA n w l m) = true
  | [], _, _ => ⟨G.pid_eq, G.pid_canon⟩
  | x :: l, m, h => by
    have hx := h x List.mem_cons_self
    have ih := ppcA_eq l (m / 2) fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e1 : ppcA n w (x :: l) m = Bool.rec (motive := fun _ => Nat) (ppcA n w l (m / 2))
        (pc n w x (ppcA n w l (m / 2))) (Nat.beq (m % 2) 1) := rfl
    rw [e1, List.map_cons, pcA]
    by_cases hm : m % 2 = 1
    · have hb : Nat.beq (m % 2) 1 = true := by rw [hm]; rfl
      rw [hb, ite_eq_left hm]
      exact ⟨by rw [pc_eq G hx, ih.1], pc_canon G _ _⟩
    · have hb : Nat.beq (m % 2) 1 = false := by
        cases h' : Nat.beq (m % 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hm
      rw [hb, ite_eq_right hm]
      exact ih

theorem ppcA_valid (hpv : pvalid n w (pid n w) = true) :
    ∀ (l : List Nat) (m : Nat), (∀ x ∈ l, canon1 n w x = true ∧ pvalid n w x = true) →
      pvalid n w (ppcA n w l m) = true
  | [], _, _ => hpv
  | x :: l, m, h => by
    have hx := h x List.mem_cons_self
    have hl : ∀ y ∈ l, canon1 n w y = true ∧ pvalid n w y = true :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ih := ppcA_valid hpv l (m / 2) hl
    have hcl := (ppcA_eq G l (m / 2) fun y hy => (hl y hy).1).2
    have e1 : ppcA n w (x :: l) m = Bool.rec (motive := fun _ => Nat) (ppcA n w l (m / 2))
        (pc n w x (ppcA n w l (m / 2))) (Nat.beq (m % 2) 1) := rfl
    rw [e1]
    cases Nat.beq (m % 2) 1
    · exact ih
    · exact pvalid_pc G.hn G.hw hx.1 hx.2 hcl ih

omit G in
theorem ppcAt_eq : ∀ (l : List Nat) (m p : Nat), (∀ x ∈ l, canon1 n w x = true ∧ pvalid n w x = true) →
    p < n → ppcAt w l m p = (pcA n (l.map (unpackP n w)) m)[p]! ∧ ppcAt w l m p < n
  | [], _, p, _, hp => by
    refine ⟨?_, hp⟩
    rw [List.map_nil, pcA, idA_get hp]
    rfl
  | x :: l, m, p, h, hp => by
    have hx := h x List.mem_cons_self
    have ih := ppcAt_eq l (m / 2) p (fun y hy => h y (List.mem_cons_of_mem _ hy)) hp
    have e1 : ppcAt w (x :: l) m p = Bool.rec (motive := fun _ => Nat) (ppcAt w l (m / 2) p)
        (at' w x (ppcAt w l (m / 2) p)) (Nat.beq (m % 2) 1) := rfl
    rw [e1, List.map_cons, pcA]
    by_cases hm : m % 2 = 1
    · have hb : Nat.beq (m % 2) 1 = true := by rw [hm]; rfl
      rw [hb, ite_eq_left hm, compA_get hp, ← ih.1, unpackP_get_canon hx.1]
      exact ⟨rfl, (inj_of_pvalid hx.2).1 _ ih.2⟩
    · have hb : Nat.beq (m % 2) 1 = false := by
        cases h' : Nat.beq (m % 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hm
      rw [hb, ite_eq_right hm]
      exact ih

theorem pcOK_of : ∀ (l rs : List Nat) (cs : List (List Nat)) (bs : List (Nat × Nat)),
    (∀ x ∈ l, canon1 n w x = true) → ppcOK n w l rs cs bs = true →
      pcOK n (l.map (unpackP n w)) rs cs bs = true ∧ ∀ x ∈ l, pvalid n w x = true
  | [], _, _, _, _, _ => ⟨by simp [pcOK], fun x hx => absurd hx (by simp)⟩
  | _ :: _, [], _, _, _, h => by simp [ppcOK] at h
  | _ :: _, _ :: _, [], _, _, h => by simp [ppcOK] at h
  | _ :: _, _ :: _, _ :: _, [], _, h => by simp [ppcOK] at h
  | x :: l, r :: rs, c :: cs, b :: bs, hc, h => by
    have hx := hc x List.mem_cons_self
    have hl : ∀ y ∈ l, canon1 n w y = true := fun y hy => hc y (List.mem_cons_of_mem _ hy)
    have hppc : ∀ m, unpackP n w (ppcA n w l m) = pcA n (l.map (unpackP n w)) m ∧
        canon1 n w (ppcA n w l m) = true := fun m => ppcA_eq G l m hl
    unfold ppcOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv, hsq⟩, hcl⟩, hcj⟩, hb2⟩, hb1⟩, hbx⟩, hbl⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := pcOK_of l rs cs bs hl hrest
    refine ⟨?_, fun y hy => ?_⟩
    · rw [List.map_cons, pcOK]
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hb1⟩, ?_⟩, ?_⟩, ih1⟩
      · rw [validA_unpack G.hw hx]
        exact hv
      · rw [← pc_eq G hx, ← (hppc r).1, eqA_unpack (pc_canon G _ _) (hppc r).2]
        exact hsq
      · rw [List.length_map]
        exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hcl)
      · rw [List.zip_map_left, List.all_map]
        refine all_of (fun yc hyc hy => ?_) hcj
        have hyl := hl yc.1 (List.of_mem_zip hyc).1
        simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
        rw [← pc_eq G hyl, ← (hppc yc.2).1, ← pc_eq G hx,
          eqA_unpack (pc_canon G _ _) (pc_canon G _ _)]
        exact hy
      · simpa using hb2
      · rw [unpackP_get_canon hx]
        exact hbx
      · rw [List.all_map]
        refine all_of (fun y hy hyp => ?_) hbl
        have hyc := hl y hy
        simp only [Function.comp_apply]
        refine all_of (fun p _ hpp => ?_) hyp
        rw [unpackP_get_canon hyc]
        exact hpp
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hv
      · exact ih2 y hy

omit G in
theorem invRest_of {xs : List Nat} (hx : ∀ x ∈ xs, canon1 n w x = true ∧ pvalid n w x = true) :
    ∀ (wt : List Nat) (m : Nat) (im r : List Nat), m + wt.length ≤ 2 ^ xs.length →
      pinvRest n w xs m im wt = some r → invRest n (xs.map (unpackP n w)) m im wt = some r
  | [], _, _, _, _, h => h
  | x :: wt, m, im, r, hm, h => by
    have hm' : m + 1 + wt.length ≤ 2 ^ xs.length := by simp at hm; omega
    unfold pinvRest at h
    unfold invRest
    cases hh : Nat.beq (im.headD (2 ^ xs.length)) m
    · rw [hh] at h
      have hne : im.head? ≠ some m := by
        intro e
        cases im with
        | nil => simp at e
        | cons a im =>
          simp only [List.head?_cons, Option.some.injEq] at e
          subst e
          simp [Nat.beq_refl] at hh
      rw [ite_eq_right hne]
      change (bif _ then _ else none) = some r at h
      cases hc : (Nat.beq m 0 || (Nat.blt x n && !(Nat.beq (ppcAt w xs m (ppcAt w xs m x)) x)))
      · rw [hc] at h
        simp at h
      · rw [hc] at h
        have hcond : m = 0 ∨ (x < n ∧ (pcA n (xs.map (unpackP n w)) m)[(pcA n (xs.map
            (unpackP n w)) m)[x]!]! ≠ x) := by
          simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
            Bool.not_eq_true'] at hc
          rcases hc with hc | ⟨hxn, hne⟩
          · exact Or.inl hc
          · right
            obtain ⟨e1, l1⟩ := ppcAt_eq xs m x hx hxn
            obtain ⟨e2, -⟩ := ppcAt_eq xs m (ppcAt w xs m x) hx l1
            refine ⟨hxn, ?_⟩
            rw [← e1, ← e2]
            intro e
            rw [e, Nat.beq_refl] at hne
            exact Bool.noConfusion hne
        rw [ite_eq_left hcond]
        exact invRest_of hx wt (m + 1) im r hm' h
    · rw [hh] at h
      have hhd : im.head? = some m := by
        cases im with
        | nil =>
          have := Nat.eq_of_beq_eq_true hh
          simp only [List.headD_nil] at this
          simp at hm
          omega
        | cons a im =>
          have := Nat.eq_of_beq_eq_true hh
          simp only [List.headD_cons] at this
          simp [this]
      rw [ite_eq_left hhd]
      exact invRest_of hx wt (m + 1) im.tail r hm' h

theorem invOK_of {xs : List Nat} (hx : ∀ x ∈ xs, canon1 n w x = true ∧ pvalid n w x = true)
    {us : Array Nat} (hus : ∀ x ∈ us.toList, canon1 n w x = true) {im wt : List Nat}
    (h : pinvOK n w xs us im wt = true) :
    invOK n (xs.map (unpackP n w)) (us.map (unpackP n w)) im wt = true ∧
      ∀ ua ∈ us.toList.zip im, ua.1 = ppcA n w xs ua.2 := by
  have hxc : ∀ x ∈ xs, canon1 n w x = true := fun x hx' => (hx x hx').1
  unfold pinvOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hz : ∀ ua ∈ us.toList.zip im, ua.1 = ppcA n w xs ua.2 := fun ua hua =>
    (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h2 ua hua)).symm
  refine ⟨?_, hz⟩
  unfold invOK
  simp only [Bool.and_eq_true]
  have hl : wt.length = 2 ^ xs.length := Nat.eq_of_beq_eq_true h3
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Array.size_map]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h1)
  · rw [Array.toList_map, List.zip_map_left, List.all_map]
    refine List.all_eq_true.2 fun ua hua => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    have huc := hus ua.1 (List.of_mem_zip hua).1
    rw [hz ua hua] at huc ⊢
    rw [← (ppcA_eq G xs ua.2 hxc).1, eqA_unpack (ppcA_eq G xs ua.2 hxc).2 huc]
    exact Nat.beq_refl _
  · rw [List.length_map]
    exact beq_iff_eq.2 hl
  · have := invRest_of hx wt 0 im [] (by omega) (by simpa using h4)
    rw [this]
    rfl

theorem conjTabOK_of {xs : List Nat} (hxc : ∀ x ∈ xs, canon1 n w x = true) {cm : List Nat}
    {cs ci : Array Nat} (hcs : ∀ x ∈ cs.toList, canon1 n w x = true)
    (hci : ∀ x ∈ ci.toList, canon1 n w x = true) (h : ptabOK n w xs cm cs ci = true) :
    conjTabOK n (xs.map (unpackP n w)) cm (cs.map (unpackP n w)) (ci.map (unpackP n w)) = true ∧
      ci.size = cs.size := by
  unfold ptabOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, Nat.eq_of_beq_eq_true h2⟩
  unfold conjTabOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Array.size_map]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h1)
  · rw [Array.size_map, Array.size_map]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h2)
  · rw [Array.toList_map, List.zip_map_left, List.all_map]
    refine all_of (fun sm hsm hs => ?_) h3
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    have hsc := hcs sm.1 (List.of_mem_zip hsm).1
    rw [← (ppcA_eq G xs sm.2 hxc).1, eqA_unpack (ppcA_eq G xs sm.2 hxc).2 hsc]
    exact hs
  · rw [Array.toList_map, Array.toList_map, List.zip_map, List.all_map]
    refine all_of (fun p hp hpp => ?_) h4
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    have hp1 := hci p.1 (List.of_mem_zip hp).1
    rw [← pc_eq G hp1, eqA_pid G (pc_canon G _ _)]
    exact hpp

theorem pconjT_eq (hid : ∀ i < n, at' w (pid n w) i = i) {s t x : Nat}
    (hx : canon1 n w x = true) (hxl : ∀ i < n, at' w x i < n) :
    pconjT n w s t x = pc n w s (pc n w x t) := by
  unfold pconjT
  cases hst : (Nat.beq s (pid n w) && Nat.beq t (pid n w))
  · rfl
  · simp only [Bool.and_eq_true, Nat.beq_eq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    refine eq_of_at' hx (pc_canon G _ _) fun i hi => ?_
    have hpc : ∀ p q, at' w (pc n w p q) i = at' w p (at' w q i) := fun p q =>
      CFSG.KS.PF.pg_pcomp G.hn hi
    rw [hpc, hpc, hid i hi, hid _ (hxl i hi)]
    rfl

theorem conj_unpack (hid : ∀ i < n, at' w (pid n w) i = i) {s t x : Nat}
    (hs : canon1 n w s = true) (hx : canon1 n w x = true) (hxl : ∀ i < n, at' w x i < n) :
    compA n (unpackP n w s) (compA n (unpackP n w x) (unpackP n w t)) =
      unpackP n w (pconjT n w s t x) ∧ canon1 n w (pconjT n w s t x) = true := by
  rw [pconjT_eq G hid hx hxl, pc_eq G hs, pc_eq G hx]
  exact ⟨rfl, pc_canon G _ _⟩

omit G in
theorem nat_beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

structure CanonC (n w : Nat) (d : ConjDataP) : Prop where
  xs : ∀ x ∈ d.xs, canon1 n w x = true
  us : ∀ x ∈ d.us.toList, canon1 n w x = true
  cs : ∀ x ∈ d.cs.toList, canon1 n w x = true
  ci : ∀ x ∈ d.ci.toList, canon1 n w x = true
  basis : ∀ i : Nat, ∀ x ∈ (d.nodes[i]!).basis.toList, canon1 n w x = true
  wit : ∀ i : Nat, canonW n w (d.nodes[i]!).wit = true
  wcs : ∀ i j : Nat, ∀ x ∈ ((d.wcs[i]!)[j]!).pts.toList, canon1 n w x = true
  excs : ∀ r ∈ d.excs, canon1 n w r.w = true

omit G in
theorem canonC_facts {d : ConjDataP} (hc : canonC n w d = true) : CanonC n w d := by
  unfold canonC at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, fun i => ?_, fun i => ?_, fun i j => ?_, h7⟩
  · by_cases hi : i < d.nodes.size
    · rw [getElem!_pos d.nodes i hi]
      exact (h5 _ (Array.getElem_mem_toList hi)).1
    · rw [getElem!_neg d.nodes i hi, default_basis]
      simp
  · by_cases hi : i < d.nodes.size
    · rw [getElem!_pos d.nodes i hi]
      exact (h5 _ (Array.getElem_mem_toList hi)).2
    · rw [getElem!_neg d.nodes i hi]
      rfl
  · by_cases hi : i < d.wcs.size
    · rw [getElem!_pos d.wcs i hi]
      have hcs := h6 _ (Array.getElem_mem_toList hi)
      by_cases hj : j < d.wcs[i].size
      · rw [getElem!_pos d.wcs[i] j hj]
        exact hcs _ (Array.getElem_mem_toList hj)
      · rw [getElem!_neg d.wcs[i] j hj, default_pts]
        simp
    · rw [getElem!_neg d.wcs i hi, default_arr_get, default_pts]
      simp

theorem rootOKC_of (hid : ∀ i < n, at' w (pid n w) i = i) {nodes : Array NodeP}
    (Cb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList, canon1 n w x = true) {cs ci : Array Nat}
    (hcs : ∀ x ∈ cs.toList, canon1 n w x = true) (hsz : ci.size = cs.size) {u : Nat} (hu : canon1 n w u = true)
    (hul : ∀ i < n, at' w u i < n) {r : Nat × Nat}
    (h : prootOKC n w (nodes.map NodeP.basis) (pcN n w nodes) cs ci u r = true) :
    rootOKC n (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (cs.map (unpackP n w)) (ci.map (unpackP n w)) (unpackP n w u) r = true := by
  unfold prootOKC at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq,
    Array.size_map] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hbs : (nodes.map NodeP.basis)[r.1]! = (nodes[r.1]!).basis := map_get _ _ h1
  rw [hbs] at h3
  have hcsr : (cs.map (unpackP n w))[r.2]! = unpackP n w cs[r.2]! := map_get _ _ h2
  have hcir : (ci.map (unpackP n w))[r.2]! = unpackP n w ci[r.2]! := map_get _ _ (by omega)
  have hconj := conj_unpack G hid (t := ci[r.2]!) (canon_get hcs r.2 h2) hu hul
  have hnj : (nodes.map (NodeP.toMain n w))[r.1]! = (nodes[r.1]!).toMain n w := map_get _ _ h1
  have hbj : ((nodes[r.1]!).toMain n w).basis = (nodes[r.1]!).basis.map (unpackP n w) := rfl
  unfold rootOKC
  simp only [Bool.and_eq_true, Bool.or_eq_true, allLt_iff, decide_eq_true_eq, Array.size_map]
  rw [hnj, hbj, cN_get G Cb, hcsr, hcir, hconj.1, memA_eq (cN_canon G Cb r.1) hconj.2,
    Array.size_map]
  refine ⟨⟨⟨h1, h2⟩, fun l hl => ?_⟩, h4⟩
  have hlc := canon_get (Cb r.1) l hl
  rw [map_get _ _ hl, eqA_unpack hlc hconj.2, eqA_pid G hlc]
  exact h3 l hl

theorem entOK_of (hid : ∀ i < n, at' w (pid n w) i = i) {nodes : Array NodeP}
    (Cb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList, canon1 n w x = true)
    (Cv : ∀ i < nodes.size, ∀ k < (nodes[i]!).basis.size, pvalid n w (nodes[i]!).basis[k]! = true)
    {cs ci : Array Nat}
    (hcs : ∀ x ∈ cs.toList, canon1 n w x = true) (hsz : ci.size = cs.size) {i : Nat} (hi : i < nodes.size) {u : Nat}
    (hu : canon1 n w u = true) (hul : ∀ i < n, at' w u i < n) {e : Nat × Nat × Nat}
    (h : pentOK n w (nodes.map NodeP.basis) (pcN n w nodes) cs ci i u e = true) :
    entOK n (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (cs.map (unpackP n w)) (ci.map (unpackP n w)) i (unpackP n w u) e = true := by
  have hbs : (nodes.map NodeP.basis)[i]! = (nodes[i]!).basis := map_get _ _ hi
  have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
  unfold pentOK at h
  unfold entOK
  by_cases he0 : e.1 = 0
  · have hb : Nat.beq e.1 0 = true := by rw [he0]; rfl
    rw [hb] at h
    dsimp only at h
    rw [ite_eq_left he0]
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [hbs] at h1 h3
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    rw [hni, hbi, Array.size_map, map_get _ _ h1, unpackP_get_canon hu,
      unpackP_get_canon (canon_get (Cb i) _ h1), unpackP_get_canon (canon_get (Cb i) _ h1),
      unpackP_get_canon hu, ← nat_beq_eq]
    exact ⟨⟨h1, h2⟩, h3⟩
  · have hb : Nat.beq e.1 0 = false := by
      cases h' : Nat.beq e.1 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') he0
    rw [hb] at h
    dsimp only at h
    rw [ite_eq_right he0]
    by_cases he1 : e.1 = 1
    · have hb1 : Nat.beq e.1 1 = true := by rw [he1]; rfl
      rw [hb1] at h
      dsimp only at h
      rw [ite_eq_left he1, cN_get G Cb, memA_eq (cN_canon G Cb i) hu]
      exact h
    · have hb1 : Nat.beq e.1 1 = false := by
        cases h' : Nat.beq e.1 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') he1
      rw [hb1] at h
      dsimp only at h
      rw [ite_eq_right he1]
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true, List.mem_range,
        Array.size_map] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      rw [hbs] at h4
      have hcsr : (cs.map (unpackP n w))[e.2.2]! = unpackP n w cs[e.2.2]! := map_get _ _ h2
      have hcir : (ci.map (unpackP n w))[e.2.2]! = unpackP n w ci[e.2.2]! :=
        map_get _ _ (by omega)
      have hsc := canon_get hcs e.2.2 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Array.size_map, beq_iff_eq]
      rw [hni, hbi, cN_get G Cb, cN_get G Cb, hcsr, hcir,
        (conj_unpack G hid (t := ci[e.2.2]!) hsc hu hul).1,
        memA_eq (cN_canon G Cb e.2.1) (conj_unpack G hid (t := ci[e.2.2]!) hsc hu hul).2,
        Array.size_map]
      refine ⟨⟨⟨⟨h1, h2⟩, ?_⟩, fun l hl => ?_⟩, h5⟩
      · simp only [ArrCertP.toMain, Array.size_map]
        exact h3
      · have hlc := canon_get (Cb i) l hl
        have hll := (inj_of_pvalid (Cv i hi l hl)).1
        rw [map_get _ _ hl, (conj_unpack G hid (t := ci[e.2.2]!) hsc hlc hll).1,
          memA_eq (cN_canon G Cb e.2.1) (conj_unpack G hid (t := ci[e.2.2]!) hsc hlc hll).2]
        exact h4 l hl

theorem nodeOKC_of (hid : ∀ i < n, at' w (pid n w) i = i) {ps : List Nat}
    {inX outX inW : Array Nat → Bool} {inXP outXP inWP : Nat → Bool}
    {allowPW allowInX allowU : Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    {d : ConjDataP} (C : CanonC n w d) {e0 : Array Nat} (he0 : ∀ x ∈ e0.toList, canon1 n w x = true)
    (hsz : d.ci.size = d.cs.size) (hUV : ∀ u ∈ d.us.toList, pvalid n w u = true)
    (Cv : ∀ i < d.nodes.size, ∀ k < (d.nodes[i]!).basis.size,
      pvalid n w (d.nodes[i]!).basis[k]! = true)
    {i : Nat} (hi : i < d.nodes.size)
    (h : pnodeOKC n w ps inXP outXP inWP allowPW allowInX allowU d (pcN n w d.nodes) e0 i =
      true) :
    nodeOKC n ps inX outX inW allowPW allowInX allowU (d.toMain n w)
      ((d.nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (e0.map (unpackP n w)) i = true := by
  unfold pnodeOKC at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hE, hrest⟩ := h
  have hni : (d.nodes.map (NodeP.toMain n w))[i]! = (d.nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((d.nodes[i]!).toMain n w).basis = (d.nodes[i]!).basis.map (unpackP n w) := rfl
  have hwi : ((d.nodes[i]!).toMain n w).wit = (d.nodes[i]!).wit.toMain n w := rfl
  have hwcs : (d.wcs.map fun cs => cs.map (ArrCertP.toMain n w))[i]! =
      (d.wcs[i]!).map (ArrCertP.toMain n w) := map_get' _ (default_map _) d.wcs i
  have hcN := cN_canon G C.basis i
  have hW : ∀ hw : pwitOK n w ps inXP outXP allowPW allowInX allowU (d.nodes[i]!).basis
      (pcN n w d.nodes)[i]! d.wcs[i]! (d.nodes[i]!).wit = true,
      witOKW n ps inX outX allowPW allowInX allowU ((d.nodes[i]!).basis.map (unpackP n w))
        ((pcN n w d.nodes)[i]!.toMain n w) ((d.wcs[i]!).map (ArrCertP.toMain n w))
        ((d.nodes[i]!).wit.toMain n w) = true := fun hw =>
    witOKW_of G hin hout (C.basis i) (fun k hk => pvalid_of_penumOK hE hk)
      (fun x hx => ⟨hcN x hx, pvalid_pts_of_penumOK hE x hx⟩) (C.wcs i) (C.wit i) hw
  unfold nodeOKC
  simp only [Bool.and_eq_true, Bool.or_eq_true, ConjDataP.toMain]
  rw [hni, hbi, hwi, cN_get G C.basis, hwcs, isMono_toMain]
  refine ⟨enumOKK_of_penumOK G (C.basis i) hcN hE, ?_⟩
  rcases hrest with ⟨hw, hm⟩ | ⟨hwx, hents⟩
  · exact Or.inl ⟨hW hw, hm⟩
  · right
    unfold pentsOK at hents
    simp only [Bool.and_eq_true] at hents
    obtain ⟨hl, hall⟩ := hents
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases hwx with hw | hx
      · exact Or.inl (hW hw)
      · exact Or.inr (excOKW_of G hinW he0 C.excs C.basis hx)
    · rw [Array.size_map]
      exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hl)
    · rw [Array.toList_map, List.zip_map_left, List.all_map]
      refine all_of (fun ue hue hu => ?_) hall
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      have hu1 := (List.of_mem_zip hue).1
      exact entOK_of G hid C.basis Cv C.cs hsz hi (C.us _ hu1)
        (inj_of_pvalid (hUV _ hu1)).1 hu

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem pconjCensus_sound_proved {n w : Nat} {ps : List Nat} {inX outX inW : Array Nat → Bool}
    {inXP outXP inWP : Nat → Bool} {allowPW allowInX allowU : Bool} {d : ConjDataP}
    {e0 : Array Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hc : canonC n w d = true)
    (he0 : e0.toList.all (canon1 n w) = true)
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    (hpc : ppcOK n w d.xs d.rs d.cjs d.bs = true) (hinv : pinvOK n w d.xs d.us d.im d.wt = true)
    (htab : ptabOK n w d.xs d.cm d.cs d.ci = true)
    (hrl : Nat.beq d.roots.length d.us.size = true)
    (hR : (d.us.toList.zip d.roots).all
      (fun ur => prootOKC n w (d.nodes.map NodeP.basis) (pcN n w d.nodes) d.cs d.ci ur.1 ur.2) =
        true)
    (hN : ∀ i < d.nodes.size, pnodeOKC n w ps inXP outXP inWP allowPW allowInX allowU d
      (pcN n w d.nodes) e0 i = true) :
    conjCensusOKW n ps inX outX inW allowPW allowInX allowU (d.toMain n w)
      (e0.map (unpackP n w)) = true := by
  obtain ⟨e1, e2, hid⟩ := SP.pid_good24 hw h24
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  have hpidv : pvalid n w (pid n w) = true :=
    pvalid_of_inj hw (fun i hi => by rw [hid i hi]; exact hi)
      (fun i hi j hj e => by rwa [hid i hi, hid j hj] at e)
  have C := SP.canonC_facts hc
  have he0' : ∀ x ∈ e0.toList, canon1 n w x = true := List.all_eq_true.1 he0
  obtain ⟨hpcM, hxv⟩ := SP.pcOK_of G d.xs d.rs d.cjs d.bs C.xs hpc
  have hxcv : ∀ x ∈ d.xs, canon1 n w x = true ∧ pvalid n w x = true :=
    fun x hx => ⟨C.xs x hx, hxv x hx⟩
  obtain ⟨hinvM, hz⟩ := SP.invOK_of G hxcv C.us hinv
  obtain ⟨htabM, hsz⟩ := SP.conjTabOK_of G C.xs C.cs C.ci htab
  have hlen : d.im.length = d.us.size := by
    unfold pinvOK at hinv
    simp only [Bool.and_eq_true] at hinv
    exact Nat.eq_of_beq_eq_true hinv.1.1.1
  have hUV : ∀ u ∈ d.us.toList, pvalid n w u = true := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    have hk' : k < d.im.length := by simp at hk; omega
    have hm : (d.us.toList[k], d.im[k]) ∈ d.us.toList.zip d.im :=
      List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩
    have e := hz _ hm
    dsimp only at e
    rw [e]
    exact SP.ppcA_valid G hpidv d.xs _ hxcv
  have Cv : ∀ i < d.nodes.size, ∀ k < (d.nodes[i]!).basis.size,
      pvalid n w (d.nodes[i]!).basis[k]! = true := by
    intro i hi k hk
    have h := hN i hi
    unfold pnodeOKC at h
    simp only [Bool.and_eq_true] at h
    exact pvalid_of_penumOK h.1 hk
  unfold conjCensusOKW
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨⟨⟨⟨hpcM, hinvM⟩, htabM⟩, ?_⟩, ?_⟩, fun i hi => ?_⟩
  · simp only [ConjDataP.toMain, Array.size_map]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hrl)
  · simp only [ConjDataP.toMain]
    rw [Array.toList_map, List.zip_map_left, List.all_map]
    refine SP.all_of (fun ur hur hr => ?_) hR
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    have hu1 := (List.of_mem_zip hur).1
    exact SP.rootOKC_of G hid C.basis C.cs hsz (C.us _ hu1) (inj_of_pvalid (hUV _ hu1)).1 hr
  · have hi' : i < d.nodes.size := by simpa [ConjDataP.toMain] using hi
    exact SP.nodeOKC_of G hid hin hout hinW C he0' hsz hUV Cv hi' (hN i hi')

end CFSG.KC.Census

end
