module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.KC.MiscCoset.Act

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem allR_succ (lo n : ℕ) (p : ℕ → Bool) :
    allR lo (n + 1) p = (p (lo + n) && allR lo n p) := by
  rw [show allR lo (n + 1) p = andB (p (Nat.add lo n)) (allR lo n p) from rfl, andB_eq]
  rfl

theorem allR_spec {lo n : ℕ} {p : ℕ → Bool} (h : allR lo n p = true) :
    ∀ x, lo ≤ x → x < lo + n → p x = true := by
  induction n with
  | zero => intro x h1 h2; omega
  | succ n ih =>
    rw [allR_succ, Bool.and_eq_true] at h
    intro x h1 h2
    rcases Nat.lt_or_ge x (lo + n) with h3 | h3
    · exact ih h.2 x h1 h3
    · have : x = lo + n := by omega
      subst this
      exact h.1

theorem walk_eq (A : ℕ → ℕ) (L : ℕ) (w : List ℕ) (x : ℕ) :
    walk A L w x = w.foldl (step A L) x := by
  induction w generalizing x with
  | nil => rfl
  | cons c w ih => exact ih (step A L x c)

theorem walk_append (A : ℕ → ℕ) (L : ℕ) (u v : List ℕ) (x : ℕ) :
    walk A L (u ++ v) x = walk A L v (walk A L u x) := by
  rw [walk_eq, walk_eq, walk_eq, List.foldl_append]

theorem relsAt_spec {A : ℕ → ℕ} {L : ℕ} {rels : List (List ℕ)} {x : ℕ}
    (h : relsAt A L rels x = true) : ∀ r ∈ rels, walk A L r x = x := by
  induction rels with
  | nil => intro r hr; cases hr
  | cons r rs ih =>
    have h' : (Nat.beq (walk A L r x) x && relsAt A L rs x) = true := by
      rw [← andB_eq]
      exact h
    rw [Bool.and_eq_true] at h'
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact Nat.eq_of_beq_eq_true h'.1
    · exact ih h'.2 r' hr'

theorem relsAt_of {A : ℕ → ℕ} {L : ℕ} {rels : List (List ℕ)} {x : ℕ}
    (h : ∀ r ∈ rels, walk A L r x = x) : relsAt A L rels x = true := by
  induction rels with
  | nil => rfl
  | cons r rs ih =>
    change andB (Nat.beq (walk A L r x) x) (relsAt A L rs x) = true
    rw [andB_eq, Bool.and_eq_true]
    exact ⟨Nat.beq_eq_true_eq _ _ ▸ h r List.mem_cons_self,
      ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩

@[expose] def LetOK (A : ℕ → ℕ) (m N x : ℕ) : Prop :=
  (∀ c < m + m, step A (m + m) x c < N) ∧
    ∀ g < m, step A (m + m) (step A (m + m) x (g + g)) (g + g + 1) = x ∧
      step A (m + m) (step A (m + m) x (g + g + 1)) (g + g) = x

theorem letOK_of {A : ℕ → ℕ} {m N x : ℕ}
    (h1 : allR 0 (Nat.add m m) (fun c => Nat.blt (step A (Nat.add m m) x c) N) = true)
    (h2 : allR 0 m (fun g =>
      andB (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.add g g))
        (Nat.succ (Nat.add g g))) x)
      (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.succ (Nat.add g g)))
        (Nat.add g g)) x)) = true) : LetOK A m N x := by
  refine ⟨fun c hc => ?_, fun g hg => ?_⟩
  · have := allR_spec h1 c (Nat.zero_le c) (by simpa using hc)
    rwa [Nat.blt_eq] at this
  · have := allR_spec h2 g (Nat.zero_le g) (by simpa using hg)
    rw [andB_eq, Bool.and_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem pointOK_spec {A : ℕ → ℕ} {m N : ℕ} {rels : List (List ℕ)} {x : ℕ}
    (h : pointOK A m N rels x = true) : LetOK A m N x ∧ ∀ r ∈ rels, walk A (m + m) r x = x := by
  unfold pointOK at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨letOK_of h.1 h.2.1, relsAt_spec h.2.2⟩

theorem invCode_eq' (c : ℕ) : invCode c = if c % 2 = 0 then c + 1 else c - 1 := by
  unfold invCode
  by_cases h : c % 2 = 0
  · have : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
    rw [this]; simp [h]
  · have : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hb : Nat.beq (Nat.mod c 2) 0 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [this]; simp [h]

theorem step_invCode {A : ℕ → ℕ} {m N c : ℕ} (hl : LetOK A m N c) {x : ℕ} (hx : x < 2 * m) :
    step A (m + m) (step A (m + m) c x) (invCode x) = c := by
  rw [invCode_eq']
  by_cases h : x % 2 = 0
  · rw [ite_eq_left h]
    have e : x = x / 2 + x / 2 := by omega
    have := (hl.2 (x / 2) (by omega)).1
    rw [← e] at this
    exact this
  · rw [ite_eq_right h]
    have e : x = x / 2 + x / 2 + 1 := by omega
    have e' : x - 1 = x / 2 + x / 2 := by omega
    have := (hl.2 (x / 2) (by omega)).2
    rw [← e] at this
    rw [e']
    exact this

theorem letterCode_lt {m : ℕ} (x : Fin m × Bool) : letterCode x < m + m := by
  obtain ⟨i, b⟩ := x
  have := i.isLt
  simp only [letterCode]
  split <;> omega

theorem walk_lt {A : ℕ → ℕ} {m N : ℕ} (hl : ∀ x < N, LetOK A m N x) :
    ∀ (w : List ℕ), (∀ c ∈ w, c < m + m) → ∀ x < N, walk A (m + m) w x < N := by
  intro w
  induction w with
  | nil => intro _ x hx; exact hx
  | cons c w ih =>
    intro hw x hx
    exact ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) _
      ((hl x hx).1 c (hw c List.mem_cons_self))

theorem walk_invRev {A : ℕ → ℕ} {m N : ℕ} (hl : ∀ x < N, LetOK A m N x) :
    ∀ (u : List (Fin m × Bool)), ∀ x < N,
      walk A (m + m) ((FreeGroup.invRev u).map letterCode) (walk A (m + m) (u.map letterCode) x)
        = x := by
  intro u
  induction u with
  | nil => intro x _; rfl
  | cons a u ih =>
    intro x hx
    have hy := (hl x hx).1 _ (letterCode_lt a)
    rw [FreeGroup.invRev_cons, List.map_append, walk_append]
    change walk A (m + m) _ (walk A (m + m) _ (walk A (m + m) (u.map letterCode)
      (step A (m + m) x (letterCode a)))) = x
    rw [ih _ hy]
    obtain ⟨i, b⟩ := a
    have hi := i.isLt
    cases b
    · change step A (m + m) (step A (m + m) x (2 * i.val + 1)) (2 * i.val + 0) = x
      have := ((hl x hx).2 i.val hi).2
      rw [show 2 * i.val + 1 = i.val + i.val + 1 by omega, show 2 * i.val + 0 = i.val + i.val by
        omega]
      exact this
    · change step A (m + m) (step A (m + m) x (2 * i.val + 0)) (2 * i.val + 1) = x
      have := ((hl x hx).2 i.val hi).1
      rw [show 2 * i.val + 1 = i.val + i.val + 1 by omega, show 2 * i.val + 0 = i.val + i.val by
        omega]
      exact this

theorem cycleFrom_spec (A : ℕ → ℕ) (L : ℕ) (u : List ℕ) : ∀ k y, cycleFrom A L u k y = true →
    0 < k ∧ (fun c => walk A L u c)^[k] y = 0 ∧
      ∀ j, 0 < j → j < k → (fun c => walk A L u c)^[j] y ≠ 0
  | 0, _, h => absurd (h : false = true) Bool.false_ne_true
  | k + 1, y, h => by
    cases hk : Nat.beq k 0 with
    | true =>
      have hk0 : k = 0 := Nat.eq_of_beq_eq_true hk
      subst hk0
      have h' : Nat.beq (walk A L u y) 0 = true := h
      exact ⟨Nat.one_pos, Nat.eq_of_beq_eq_true h', fun j hj hj1 => absurd hj1 (by omega)⟩
    | false =>
      have e : cycleFrom A L u (k + 1) y = Bool.rec (motive := fun _ => Bool)
          (andB (notB (Nat.beq (walk A L u y) 0)) (cycleFrom A L u k (walk A L u y)))
          (Nat.beq (walk A L u y) 0) (Nat.beq k 0) := rfl
      rw [e, hk, andB_eq, Bool.and_eq_true] at h
      have hne : walk A L u y ≠ 0 := by
        intro e0
        rw [e0] at h
        exact absurd h.1 (by decide)
      obtain ⟨-, hret, hmin⟩ := cycleFrom_spec A L u k _ h.2
      refine ⟨Nat.succ_pos k, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]
        exact hret
      · intro j hj hjk
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [Function.iterate_succ_apply]
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact hne
        · exact hmin i hi (by omega)

theorem exists_act {m N : ℕ} (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)}
    (hrels : ∀ r ∈ codes ws, r ∈ rels) {A : ℕ → ℕ}
    (hpt : ∀ x < N, pointOK A m N rels x = true) :
    ∃ ψ : PG m ws →* (Equiv.Perm {c : ℕ // c < N})ᵐᵒᵖ, ∀ y < 2 * m, ∀ c : {c : ℕ // c < N},
      ((ψ (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} y)).unop c).1 =
        step A (m + m) c.1 y :=
  exists_action_step ws (fun c => c < N) (fun c x => step A (m + m) c x)
    (fun c hc x hx => (pointOK_spec (hpt c hc)).1.1 x (by omega))
    (fun c hc x hx => step_invCode (pointOK_spec (hpt c hc)).1 hx)
    (fun c hc r hr => by rw [← walk_eq]; exact (pointOK_spec (hpt c hc)).2 r (hrels r hr))

theorem codes_lt {m : ℕ} (u : List (Fin m × Bool)) : ∀ y ∈ u.map letterCode, y < 2 * m := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
  have := letterCode_lt x
  omega

theorem act_mk {m N : ℕ} {ws : List (List (Fin m × Bool))} {A : ℕ → ℕ}
    (ψ : PG m ws →* (Equiv.Perm {c : ℕ // c < N})ᵐᵒᵖ)
    (hψ : ∀ y < 2 * m, ∀ c : {c : ℕ // c < N},
      ((ψ (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} y)).unop c).1 =
        step A (m + m) c.1 y) (u : List (Fin m × Bool)) (c : {c : ℕ // c < N}) :
    ((ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop c).1 = walk A (m + m) (u.map letterCode) c.1 := by
  rw [← evalWord_presLetter, act_evalWord_step ψ hψ _ (codes_lt u) c, walk_eq]

theorem cycleOK_sound {m N : ℕ} (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)}
    (hrels : codes ws = rels) {A : ℕ → ℕ} (hN : 0 < N)
    (hpt : ∀ x < N, pointOK A m N rels x = true) (u : List (Fin m × Bool)) {ℓ : ℕ}
    (hc : cycleOK A (Nat.add m m) (u.map letterCode) ℓ = true) :
    ℓ ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u)) := by
  obtain ⟨ψ, hψ⟩ := exists_act ws (fun r hr => hrels ▸ hr) hpt
  obtain ⟨hℓ, hret, hmin⟩ := cycleFrom_spec A (m + m) (u.map letterCode) ℓ 0 hc
  have hf : (fun c' => List.foldl (fun c x => step A (m + m) c x) c' (u.map letterCode)) =
      fun c => walk A (m + m) (u.map letterCode) c := funext fun c => (walk_eq _ _ _ c).symm
  have := cycle_dvd_orderOf_step ψ hψ (codes_lt u) ⟨0, hN⟩ hℓ (by rw [hf]; exact hret)
    (fun j hj hjl => by rw [hf]; exact hmin j hj hjl)
  rwa [evalWord_presLetter] at this

theorem movesOK_sound {m N : ℕ} (ws fix : List (List (Fin m × Bool)))
    {rels : List (List ℕ)} (hrels : codes ws ++ codes fix = rels) {A : ℕ → ℕ} (hN : 0 < N)
    (hpt : ∀ x < N, pointOK A m N rels x = true) (move : List (List (Fin m × Bool)))
    (hmove : movesOK A (Nat.add m m) (codes move) = true) :
    ∃ (E : Type) (_ : Group E) (ψ : PG m ws →* E),
      (∀ u ∈ fix, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) = 1) ∧
        ∀ u ∈ move, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := exists_act ws (fun r hr => hrels ▸ List.mem_append_left _ hr) hpt
  refine ⟨_, inferInstance, ψ, fun u hu => ?_, fun u hu h1 => ?_⟩
  · apply MulOpposite.unop_injective
    ext c
    rw [act_mk ψ hψ u c]
    exact (pointOK_spec (hpt c.1 c.2)).2 _
      (hrels ▸ List.mem_append_right _ (List.mem_map_of_mem hu))
  · have hm : ∀ v ∈ codes move, walk A (m + m) v 0 ≠ 0 := by
      clear hu h1
      induction move with
      | nil => intro v hv; cases hv
      | cons v vs ih =>
        have h' : (notB (fixOK A (Nat.add m m) (v.map letterCode)) &&
            movesOK A (Nat.add m m) (codes vs)) = true := by
          rw [← andB_eq]
          exact hmove
        rw [Bool.and_eq_true] at h'
        intro v' hv'
        rcases List.mem_cons.1 hv' with rfl | hv'
        · intro e
          have : fixOK A (Nat.add m m) (v.map letterCode) = true := by
            change Nat.beq _ 0 = true
            rw [Nat.beq_eq]
            exact e
          rw [this] at h'
          exact absurd h'.1 (by decide)
        · exact ih h'.2 v' hv'
    have := act_mk ψ hψ u ⟨0, hN⟩
    rw [h1] at this
    exact hm _ (List.mem_map_of_mem hu) this.symm

theorem coverPointOK_sound {m N : ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) (extra : List (List (Fin m × Bool)))
    {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) ++ codes extra = Wc)
    {A B : ℕ → ℕ} (h : ∀ x < N, coverPointOK A B m N Rc Wc x = true) :
    ∀ x < N, pointOK A m N (codes (CFSG.LieType.Multipliers.coverWords R w ++ extra)) x = true := by
  have hs : ∀ x < N, LetOK A m N x ∧ (∀ j (hj : j < Rc.length), walk A (m + m) Rc[j] x = B (j * N + x) ∧
      ∀ g < m, B (j * N + step A (m + m) x (g + g)) = step A (m + m) (B (j * N + x)) (g + g)) ∧
      ∀ r ∈ Wc, walk A (m + m) r x = x := by
    intro x hx
    have h0 := h x hx
    unfold coverPointOK at h0
    rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h0
    refine ⟨letOK_of h0.1 h0.2.1, ?_, relsAt_spec h0.2.2.2⟩
    have key : ∀ (L : List (List ℕ)) (k : ℕ), List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun r _ ih k => andB
          (Nat.beq (walk A (Nat.add m m) r x) (B (Nat.add (Nat.mul k N) x)))
          (andB (allR 0 m fun g => Nat.beq
            (B (Nat.add (Nat.mul k N) (step A (Nat.add m m) x (Nat.add g g))))
            (step A (Nat.add m m) (B (Nat.add (Nat.mul k N) x)) (Nat.add g g)))
          (ih (Nat.succ k)))) L k = true →
        ∀ j (hj : j < L.length), walk A (m + m) L[j] x = B ((k + j) * N + x) ∧
          ∀ g < m, B ((k + j) * N + step A (m + m) x (g + g)) =
            step A (m + m) (B ((k + j) * N + x)) (g + g) := by
      intro L
      induction L with
      | nil => intro k _ j hj; cases hj
      | cons r L ih =>
        intro k hk j hj
        change andB _ (andB _ _) = true at hk
        rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hk
        rcases j with _ | j
        · refine ⟨Nat.eq_of_beq_eq_true hk.1, fun g hg => ?_⟩
          exact Nat.eq_of_beq_eq_true (allR_spec hk.2.1 g (Nat.zero_le g) (by omega))
        · have := ih (k + 1) hk.2.2 j (by simpa using hj)
          rw [show k + 1 + j = k + (j + 1) by omega] at this
          exact this
    intro j hj
    have := key Rc 0 h0.2.2.1 j hj
    rw [Nat.zero_add] at this
    exact this
  intro x hx
  unfold pointOK
  rw [andB_eq, andB_eq]
  have hl := (hs x hx).1
  refine Bool.and_eq_true_iff.2 ⟨?_, Bool.and_eq_true_iff.2 ⟨?_, ?_⟩⟩
  · have h0 := h x hx
    unfold coverPointOK at h0
    rw [andB_eq, Bool.and_eq_true] at h0
    exact h0.1
  · have h0 := h x hx
    unfold coverPointOK at h0
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h0
    exact h0.2.1
  · apply relsAt_of
    intro r hr
    simp only [codes, List.map_append, List.mem_append, CFSG.LieType.Multipliers.coverWords,
      List.map_flatMap, List.mem_flatMap, List.map_map] at hr
    rcases hr with (⟨i, -, hr⟩ | hr) | hr
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hv
      have hjc : j < Rc.length := by rw [← hR]; simpa [codes] using hj
      have hRj : Rc[j] = R[j].map letterCode := by subst hR; simp [codes]
      have hi := i.isLt
      change walk A (m + m) _ x = x
      simp only [Function.comp_apply, CFSG.LieType.Multipliers.commWord, List.map_append,
        walk_append]
      have ey : walk A (m + m) ([(i, true)].map letterCode) x =
          step A (m + m) x (i.val + i.val) := by
        change step A (m + m) x (2 * i.val + 0) = _
        rw [show 2 * i.val + 0 = i.val + i.val by omega]
      have hyN : step A (m + m) x (i.val + i.val) < N := hl.1 _ (by omega)
      have e1 := ((hs _ hyN).2.1 j hjc).1
      have e2 := ((hs x hx).2.1 j hjc).2 i.val hi
      have e3 := ((hs x hx).2.1 j hjc).1
      rw [hRj] at e1 e3
      rw [ey, e1, e2]
      have hb : B (j * N + x) < N := by
        rw [← e3]
        exact walk_lt (fun z hz => (hs z hz).1) _ (fun c hc => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc
          exact letterCode_lt l) x hx
      have e4 : walk A (m + m) ((FreeGroup.invRev [(i, true)]).map letterCode)
          (step A (m + m) (B (j * N + x)) (i.val + i.val)) = B (j * N + x) := by
        change step A (m + m) (step A (m + m) (B (j * N + x)) (i.val + i.val))
          (2 * i.val + 1) = B (j * N + x)
        rw [show 2 * i.val + 1 = i.val + i.val + 1 by omega]
        exact (((hs _ hb).1).2 i.val hi).1
      rw [e4, ← e3]
      exact walk_invRev (fun z hz => (hs z hz).1) _ x hx
    · exact (hs x hx).2.2 _ (hW ▸ List.mem_append_left _ (by simpa [codes] using hr))
    · exact (hs x hx).2.2 _ (hW ▸ List.mem_append_right _ (by simpa [codes] using hr))

theorem allR_join {lo a b : ℕ} {p : ℕ → Bool} (h1 : allR lo a p = true)
    (h2 : allR (Nat.add lo a) b p = true) : allR lo (Nat.add a b) p = true := by
  induction b with
  | zero => exact h1
  | succ b ih =>
    rw [allR_succ, Bool.and_eq_true] at h2
    rw [show Nat.add a (b + 1) = Nat.add a b + 1 from rfl, allR_succ, Bool.and_eq_true]
    refine ⟨?_, ih h2.2⟩
    have e : lo + Nat.add a b = Nat.add lo a + b := by simp only [Nat.add_eq]; omega
    rw [e]
    exact h2.1

theorem allR_join' {lo a c b d : ℕ} {p : ℕ → Bool} (h1 : allR lo a p = true)
    (h2 : allR c b p = true) (hc : Nat.beq (Nat.add lo a) c = true)
    (hd : Nat.beq (Nat.add a b) d = true) : allR lo d p = true := by
  rw [← Nat.eq_of_beq_eq_true hc] at h2
  rw [← Nat.eq_of_beq_eq_true hd]
  exact allR_join h1 h2

theorem pointOK_of_allR {A : ℕ → ℕ} {m N : ℕ} {rels : List (List ℕ)}
    (h : allR 0 N (pointOK A m N rels) = true) : ∀ x < N, pointOK A m N rels x = true :=
  fun x hx => allR_spec h x (Nat.zero_le x) (by omega)

theorem coverPointOK_of_allR {A B : ℕ → ℕ} {m N : ℕ} {R W : List (List ℕ)}
    (h : allR 0 N (coverPointOK A B m N R W) = true) : ∀ x < N, coverPointOK A B m N R W x = true :=
  fun x hx => allR_spec h x (Nat.zero_le x) (by omega)

end CFSG.KC.MiscCoset.Act

end
