module

public import CFSG.Certificates.Kernel.BabyMonster.RegRun

public section

namespace CFSG.KC.BM.Reg

open CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned

@[expose] def pwOf : List (ℕ × ℕ × ℕ) → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | (l, b, e) :: t, x => cond (Nat.beq l x) (some (b, e)) (pwOf t x)

@[expose] def sumPw (P : List (ℕ × ℕ × ℕ)) (b : ℕ) : List ℕ → Option ℕ
  | [] => some 0
  | x :: w =>
    match pwOf P x, sumPw P b w with
    | some (c, e), some s => cond (Nat.beq c b) (some (e + s)) none
    | _, _ => none

@[expose] def pwOK (tab : List Ent) : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | done, (l, b, e) :: t =>
    (Nat.beq l b && Nat.beq e 1 ||
      match defOf l tab with
      | none => false
      | some d => oeqB (sumPw done b (lhsW d)) (some e)) && pwOK tab ((l, b, e) :: done) t

@[expose] def ordsOK (tab : List Ent) (P : List (ℕ × ℕ × ℕ)) (ords : List (ℕ × ℕ)) : Bool :=
  ords.all fun o => Nat.blt 0 o.2 &&
    tab.any fun e => weq (rhsW e) [] && oeqB (sumPw P o.1 (lhsW e)) (some o.2)

@[expose] def ordOf : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (a, n) :: t, b => cond (Nat.beq a b) n (ordOf t b)

@[expose] def ruleOKP (tab : List Ent) (P : List (ℕ × ℕ × ℕ)) (ords : List (ℕ × ℕ)) :
    ℕ × ℕ × Option ℕ → Bool
  | (x, y, z) => ruleOK tab (x, y, z) ||
    match pwOf P x, pwOf P y with
    | some (b, i), some (c, j) =>
      Nat.beq b c &&
        match z with
        | none => Nat.blt 0 (ordOf ords b) && Nat.beq ((i + j) % ordOf ords b) 0
        | some w =>
          match pwOf P w with
          | some (d, k) => Nat.beq d b &&
              cond (Nat.beq (ordOf ords b) 0) (Nat.beq (i + j) k)
                (Nat.beq ((i + j) % ordOf ords b) (k % ordOf ords b))
          | none => false
    | _, _ => false

@[expose] def powOK (P : List (ℕ × ℕ × ℕ)) (ords : List (ℕ × ℕ)) (v p e : ℕ) : Bool :=
  match pwOf P v, pwOf P p with
  | some (b, i), some (c, k) => Nat.beq b c &&
      cond (Nat.beq (ordOf ords b) 0) (Nat.beq (i * e) k)
        (Nat.beq ((i * e) % ordOf ords b) (k % ordOf ords b))
  | _, _ => false

@[expose] def stepOKP (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (P : List (ℕ × ℕ × ℕ)) (ords : List (ℕ × ℕ)) (σ : ℕ → Option (List ℕ)) (ins : Ins)
    (o : List ℕ × ℕ) : Bool :=
  stepOK rs Fs tab σ ins o ||
    match ins with
    | .pwr e i _ =>
      match σ i with
      | some u => isLit rs Fs tab u o.2 &&
          match o.1 with
          | [p] => powOK P ords o.2 p e
          | _ => false
      | none => false
    | _ => false

@[expose] def runOKP (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (P : List (ℕ × ℕ × ℕ)) (ords : List (ℕ × ℕ)) :
    List Ins → List (List ℕ × ℕ) → (ℕ → Option (List ℕ)) → Bool
  | [], [], _ => true
  | ins :: p, o :: os, σ =>
    stepOKP rs Fs tab P ords σ ins o && runOKP rs Fs tab P ords p os (upd σ (insOut ins) o.1)
  | _, _, _ => false

section Monoid

variable {M : Type*} [Monoid M] {val : ℕ → M}

@[expose] def PwSound (val : ℕ → M) (P : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ p ∈ P, val p.1 = val p.2.1 ^ p.2.2

theorem pwOf_sound : ∀ {P : List (ℕ × ℕ × ℕ)}, PwSound val P → ∀ {x b e : ℕ},
    pwOf P x = some (b, e) → val x = val b ^ e
  | [], _, _, _, _, h => by simp [pwOf] at h
  | (l, c, d) :: t, hP, x, b, e, h => by
    unfold pwOf at h
    cases hc : Nat.beq l x
    · rw [hc, cond_false] at h
      exact pwOf_sound (fun p hp => hP p (List.mem_cons_of_mem _ hp)) h
    · rw [hc, cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← Nat.eq_of_beq_eq_true hc]
      exact hP _ List.mem_cons_self

theorem sumPw_sound {P : List (ℕ × ℕ × ℕ)} (hP : PwSound val P) {b : ℕ} :
    ∀ {w : List ℕ} {s : ℕ}, sumPw P b w = some s → wv val w = val b ^ s
  | [], s, h => by
    simp only [sumPw, Option.some.injEq] at h
    rw [← h, pow_zero]
    rfl
  | x :: w, s, h => by
    unfold sumPw at h
    cases hx : pwOf P x with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some ce =>
      obtain ⟨c, e⟩ := ce
      cases hw : sumPw P b w with
      | none => rw [hx, hw] at h; exact absurd h (by simp)
      | some t =>
        rw [hx, hw] at h
        dsimp only at h
        cases hc : Nat.beq c b
        · rw [hc, cond_false] at h; exact absurd h (by simp)
        · rw [hc, cond_true, Option.some.injEq] at h
          rw [← h, wv_cons, pwOf_sound hP hx, sumPw_sound hP hw, Nat.eq_of_beq_eq_true hc,
            pow_add]

theorem pwOK_sound {tab : List Ent} (ht : TabSound val tab) :
    ∀ (done P : List (ℕ × ℕ × ℕ)), PwSound val done → pwOK tab done P = true →
      PwSound val P
  | _, [], _, _ => fun _ hp => by simp at hp
  | done, (l, b, e) :: t, hd, h => by
    simp only [pwOK, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hl : val l = val b ^ e := by
      rcases h1 with ⟨hlb, he⟩ | h1
      · rw [Nat.eq_of_beq_eq_true hlb, Nat.eq_of_beq_eq_true he, pow_one]
      · cases hdf : defOf l tab with
        | none => rw [hdf] at h1; exact absurd h1 (by simp)
        | some d =>
          rw [hdf] at h1
          obtain ⟨hd', hx⟩ := defOf_spec hdf
          have := ht d hd'
          rw [hx, wv_single] at this
          rw [← this]
          exact sumPw_sound hd (oeqB_spec h1)
    have hd2 : PwSound val ((l, b, e) :: done) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hl
      · exact hd p hp
    have ht' := pwOK_sound ht ((l, b, e) :: done) t hd2 h2
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hl
    · exact ht' p hp

theorem ordOf_sound {tab : List Ent} {P : List (ℕ × ℕ × ℕ)} {ords : List (ℕ × ℕ)}
    (ht : TabSound val tab) (hP : PwSound val P) (h : ordsOK tab P ords = true) :
    ∀ b, val b ^ ordOf ords b = 1 := by
  intro b
  have key : ∀ (os : List (ℕ × ℕ)), (∀ o ∈ os, o ∈ ords) → val b ^ ordOf os b = 1 := by
    intro os
    induction os with
    | nil => intro _; exact pow_zero _
    | cons o os ih =>
      intro hos
      obtain ⟨a, n⟩ := o
      unfold ordOf
      cases hc : Nat.beq a b
      · rw [cond_false]
        exact ih fun o ho => hos o (List.mem_cons_of_mem _ ho)
      · rw [cond_true, ← Nat.eq_of_beq_eq_true hc]
        have h1 := List.all_eq_true.1 h _ (hos _ List.mem_cons_self)
        simp only [Bool.and_eq_true, List.any_eq_true] at h1
        obtain ⟨_, e, he, hr, hs⟩ := h1
        have := ht e he
        rw [weq_spec hr, wv_nil, sumPw_sound hP (oeqB_spec hs)] at this
        exact this
  exact key ords fun _ h => h

theorem pow_mod_of {a : M} {n : ℕ} (h : a ^ n = 1) (m : ℕ) : a ^ m = a ^ (m % n) := by
  conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, h, one_pow, one_mul]

theorem rulesP_sound {tab : List Ent} {P : List (ℕ × ℕ × ℕ)} {ords : List (ℕ × ℕ)}
    (ht : TabSound val tab) (hP : PwSound val P) (ho : ordsOK tab P ords = true)
    (hcomm : ∀ x y, val x * val y = 1 → val y * val x = 1) :
    ∀ {rs : List (ℕ × ℕ × Option ℕ)}, rs.all (ruleOKP tab P ords) = true → RulesSound val rs := by
  intro rs hrs r hr
  obtain ⟨x, y, z⟩ := r
  have h := List.all_eq_true.1 hrs _ hr
  simp only [ruleOKP, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [ruleOK, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h
    obtain ⟨e, he, h⟩ := h
    have hte := ht e he
    rcases h with ⟨h1, h2⟩ | ⟨⟨h0, h1⟩, h2⟩
    · rw [weq_spec h1, weq_spec h2] at hte
      simpa [wv_cons, wv_nil] using hte
    · rw [weq_spec h1, weq_spec h2] at hte
      rw [oeqB_spec h0]
      simp only [wv_cons, wv_nil, mul_one] at hte
      simpa [wv_nil] using hcomm _ _ hte
  · have hord := ordOf_sound ht hP ho
    cases hx : pwOf P x with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some bi =>
      cases hy : pwOf P y with
      | none => rw [hx, hy] at h; exact absurd h (by simp)
      | some cj =>
        obtain ⟨b, i⟩ := bi
        obtain ⟨c, j⟩ := cj
        rw [hx, hy, Bool.and_eq_true] at h
        obtain ⟨hbc, h⟩ := h
        have hbc := Nat.eq_of_beq_eq_true hbc
        subst hbc
        have hxy : val x * val y = val b ^ (i + j) := by
          rw [pwOf_sound hP hx, pwOf_sound hP hy, pow_add]
        change val x * val y = wv val (z.elim [] fun c => [c])
        rw [hxy]
        cases z with
        | none =>
          simp only [Bool.and_eq_true] at h
          rw [pow_mod_of (hord b), Nat.eq_of_beq_eq_true h.2, pow_zero]
          rfl
        | some w =>
          simp only at h
          cases hw : pwOf P w with
          | none => rw [hw] at h; exact absurd h (by simp)
          | some dk =>
            obtain ⟨d, k⟩ := dk
            rw [hw, Bool.and_eq_true] at h
            obtain ⟨hd, h⟩ := h
            have hd := Nat.eq_of_beq_eq_true hd
            subst hd
            simp only [Option.elim_some, wv_single]
            rw [pwOf_sound hP hw]
            cases hn : Nat.beq (ordOf ords d) 0
            · rw [hn, cond_false] at h
              rw [pow_mod_of (hord d), Nat.eq_of_beq_eq_true h, ← pow_mod_of (hord d)]
            · rw [hn, cond_true] at h
              rw [Nat.eq_of_beq_eq_true h]

theorem powOK_sound {P : List (ℕ × ℕ × ℕ)} {ords : List (ℕ × ℕ)} (hP : PwSound val P)
    (hord : ∀ b, val b ^ ordOf ords b = 1) {v p e : ℕ} (h : powOK P ords v p e = true) :
    val v ^ e = val p := by
  unfold powOK at h
  cases hv : pwOf P v with
  | none => rw [hv] at h; exact absurd h (by simp)
  | some bi =>
    cases hp : pwOf P p with
    | none => rw [hv, hp] at h; exact absurd h (by simp)
    | some ck =>
      obtain ⟨b, i⟩ := bi
      obtain ⟨c, k⟩ := ck
      rw [hv, hp] at h
      dsimp only at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hbc, h⟩ := h
      have hbc := Nat.eq_of_beq_eq_true hbc
      subst hbc
      rw [pwOf_sound hP hv, pwOf_sound hP hp, ← pow_mul]
      cases hn : Nat.beq (ordOf ords b) 0
      · rw [hn, cond_false] at h
        rw [pow_mod_of (hord b), Nat.eq_of_beq_eq_true h, ← pow_mod_of (hord b)]
      · rw [hn, cond_true] at h
        rw [Nat.eq_of_beq_eq_true h]

end Monoid

section Run

variable {G : Type*} [Group G] {M : Type*} [Monoid M] {f : G →* M} {val : ℕ → M}
  {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} {tab : List Ent}
  {P : List (ℕ × ℕ × ℕ)} {ords : List (ℕ × ℕ)}

theorem stepP_sound (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i)
    (ht : TabSound val tab) (hP : PwSound val P) (hord : ∀ b, val b ^ ordOf ords b = 1)
    {ρ : ℕ → G} {σ : ℕ → Option (List ℕ)} (h : Inv f val ρ σ) (ins : Ins) (o : List ℕ × ℕ)
    (hs : stepOKP rs Fs tab P ords σ ins o = true) :
    Inv f val (insStepG ρ ins) (upd σ (insOut ins) o.1) := by
  unfold stepOKP at hs
  simp only [Bool.or_eq_true] at hs
  rcases hs with hs | hs
  · exact step_sound hr hF ht h ins o hs
  · obtain ⟨o, v⟩ := o
    cases ins with
    | mu i j k => exact absurd hs (by simp)
    | iv i k => exact absurd hs (by simp)
    | pwr e i k =>
      dsimp only at hs
      cases hi : σ i with
      | none => rw [hi] at hs; exact absurd hs (by simp)
      | some u =>
        rw [hi, Bool.and_eq_true] at hs
        obtain ⟨hl, hp⟩ := hs
        match o, hp with
        | [p], hp =>
          refine inv_upd h k _ [p] ?_
          rw [map_pow, h i u hi, isLit_sound hr hF ht hl, powOK_sound hP hord hp, wv_single]

theorem runOKP_sound (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i)
    (ht : TabSound val tab) (hP : PwSound val P) (hord : ∀ b, val b ^ ordOf ords b = 1) :
    ∀ (prog : List Ins) (outs : List (List ℕ × ℕ)) (ρ : ℕ → G) (σ : ℕ → Option (List ℕ)),
      Inv f val ρ σ → runOKP rs Fs tab P ords prog outs σ = true →
        Inv f val (prog.foldl insStepG ρ) (finSt prog outs σ)
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, h => by simp [runOKP] at h
  | _ :: _, [], _, _, _, h => by simp [runOKP] at h
  | ins :: p, o :: os, ρ, σ, h, hs => by
    simp only [runOKP, Bool.and_eq_true] at hs
    rw [List.foldl_cons]
    exact runOKP_sound hr hF ht hP hord p os _ _ (stepP_sound hr hF ht hP hord h ins o hs.1) hs.2

end Run

theorem regCertM {L : List (List ℕ)} {tab : List Ent} {wl : List ℕ}
    {rs : List (ℕ × ℕ × Option ℕ)} {P : List (ℕ × ℕ × ℕ)} {ords : List (ℕ × ℕ)}
    {Fs : List (List ℕ)} {S : List ℕ} {prog : List Ins} {outs : List (List ℕ × ℕ)}
    {initI : List (ℕ × Option ℕ)} {dflt : Bool} {regs idx : List ℕ}
    {init : List (ℕ × Option (List ℕ))} {tgt : List (List ℕ)}
    (hwl : WfL L wl) (htab : TabOK L tab) (hwf : wfOK wl tab = true)
    (hpw : pwOK tab [] P = true) (hord : ordsOK tab P ords = true)
    (hrs : rs.all (ruleOKP tab P ords) = true) (hfl : flOK rs Fs tab S L.length = true)
    (hrun : runOKP rs Fs tab P ords prog outs (init0 initI dflt) = true)
    (hfin : finOK rs Fs tab (finSt prog outs (init0 initI dflt)) regs idx = true)
    (hinit : initI.map (fun p => (p.1, p.2.map fun i => L.getD i idStrips)) = init)
    (htgt : idx.map (fun i => L.getD i idStrips) = tgt) :
    RegsOK prog init dflt regs tgt := by
  intro G _ f ρ hi hd k hk
  have ht := wfOK_sound tab wl (wfL_spec hwl) hwf htab
  have hP := pwOK_sound ht [] P (fun _ h => by simp at h) hpw
  have ho := ordOf_sound ht hP hord
  have hr := rulesP_sound ht hP hord (fun _ _ h => mul_eq_one_comm.1 h) hrs
  have hn : ∀ i, L.length ≤ i → litV L i = 1 := fun i hi => by
    rw [litV, List.getD_eq_default _ _ hi, stripMat_idStrips]
  have hF := flOK_sound hr ht hn hfl
  have h0 : Inv f (litV L) ρ (init0 initI dflt) := by
    refine init0_sound (fun p hp => ?_) (fun hdf r hr' => hd hdf r ?_)
    · have := hi (p.1, p.2.map fun i => L.getD i idStrips)
        (by rw [← hinit]; exact List.mem_map_of_mem hp)
      rw [this]
      cases p.2 <;> rfl
    · rw [← hinit, List.map_map]
      exact hr'
  have hR := runOKP_sound hr hF ht hP ho prog outs ρ _ h0 hrun
  obtain ⟨hl, hv⟩ := finOK_sound hr hF ht hR regs idx hfin
  have hk' : k < idx.length := hl ▸ hk
  rw [hv k hk, ← htgt, List.getD_eq_getElem _ _ hk',
    List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map]
  rfl

example : pwOK [(0, [0], some 1, [])] [] [(0, 0, 1), (1, 0, 2)] = true := by decide
example : pwOK [(0, [0], some 1, [])] [] [(0, 0, 1), (1, 0, 3)] = false := by decide
example : pwOK [(0, [0], some 1, [])] [] [(1, 0, 2), (0, 0, 1)] = false := by decide
example : ordsOK [(0, [1], none, [])] [(0, 0, 1), (1, 0, 2)] [(0, 3)] = true := by decide
example : ordsOK [(0, [1], none, [])] [(0, 0, 1), (1, 0, 2)] [(0, 2)] = false := by decide
example : ruleOKP [] [(0, 0, 1), (1, 0, 2)] [(0, 3)] (1, 0, none) = true := by decide
example : ruleOKP [] [(0, 0, 1), (1, 0, 2)] [(0, 3)] (1, 1, some 0) = true := by decide
example : ruleOKP [] [(0, 0, 1), (1, 0, 2)] [(0, 3)] (1, 1, none) = false := by decide
example : ruleOKP [] [(0, 0, 1), (1, 0, 2)] [] (0, 0, some 1) = true := by decide
example : ruleOKP [] [(0, 0, 1), (1, 0, 2)] [] (1, 0, none) = false := by decide
example : powOK [(0, 0, 1), (1, 0, 2)] [(0, 3)] 0 1 5 = true := by decide
example : powOK [(0, 0, 1), (1, 0, 2)] [(0, 3)] 0 1 4 = false := by decide
example : powOK [(0, 0, 1), (1, 0, 2)] [] 0 1 5 = false := by decide
example : runOKP [] [[0], [1]] [] [(0, 0, 1), (1, 0, 2)] [] [.pwr 2 1 3] [([1], 0)]
    (init0 [(1, some 0)] false) = true := by decide
example : runOKP [] [[0], [1]] [] [(0, 0, 1), (1, 0, 2)] [] [.pwr 3 1 3] [([1], 0)]
    (init0 [(1, some 0)] false) = false := by decide

end CFSG.KC.BM.Reg

end
