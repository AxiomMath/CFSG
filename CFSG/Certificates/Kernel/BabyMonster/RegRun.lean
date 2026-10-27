module

public import CFSG.Certificates.Kernel.BabyMonster.WfProd
public import CFSG.Monster.B.Pinned.Primes.Program

public section

namespace CFSG.KC.BM.Reg

open CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned CFSG.KC.BM.SL

abbrev Mat : Type := Matrix (Fin 4370) (Fin 4370) (ZMod 2)

abbrev Ent : Type := ℕ × List ℕ × Option ℕ × List ℕ

@[expose] def memB (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: t => Nat.beq x y || memB x t

@[expose] def weq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: u, y :: w => Nat.beq x y && weq u w
  | _, _ => false

@[expose] def oeqB : Option ℕ → Option ℕ → Bool
  | none, none => true
  | some x, some y => Nat.beq x y
  | _, _ => false

@[expose] def lhsW (e : Ent) : List ℕ := e.1 :: e.2.1

@[expose] def rhsW (e : Ent) : List ℕ :=
  match e.2.2.1 with
  | none => e.2.2.2
  | some c => c :: e.2.2.2

@[expose] def look : List (ℕ × ℕ × Option ℕ) → ℕ → ℕ → Option (Option ℕ)
  | [], _, _ => none
  | (a, b, c) :: t, x, y => cond (Nat.beq a x && Nat.beq b y) (some c) (look t x y)

@[expose] def push (rs : List (ℕ × ℕ × Option ℕ)) (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: t =>
    match look rs x y with
    | none => x :: y :: t
    | some none => t
    | some (some z) => push rs z t

@[expose] def red (rs : List (ℕ × ℕ × Option ℕ)) (w : List ℕ) : List ℕ := w.foldr (push rs) []

@[expose] def cat (Fs : List (List ℕ)) (w : List ℕ) : List ℕ := w.foldr (fun x acc => Fs.getD x [] ++ acc) []

@[expose] def flatW (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (w : List ℕ) : List ℕ :=
  red rs (cat Fs w)

@[expose] def defOf (x : ℕ) : List Ent → Option Ent
  | [] => none
  | e :: t => cond (oeqB e.2.2.1 (some x) && weq e.2.2.2 []) (some e) (defOf x t)

@[expose] def expand (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent) (x : ℕ) :
    List ℕ :=
  match defOf x tab with
  | none => [x]
  | some e => flatW rs Fs (lhsW e)

@[expose] def allLt (n : ℕ) : List ℕ → Bool
  | [] => true
  | x :: t => Nat.blt x n && allLt n t

@[expose] def ruleOK (tab : List Ent) : ℕ × ℕ × Option ℕ → Bool
  | (x, y, z) => tab.any fun e =>
      (weq (lhsW e) [x, y] && weq (rhsW e) (z.elim [] fun c => [c])) ||
        (oeqB z none && weq (lhsW e) [y, x] && weq (rhsW e) [])

@[expose] def flOK (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (S : List ℕ) (n : ℕ) : Bool :=
  Nat.ble Fs.length n && (List.range n).all fun i =>
    cond (memB i S) (weq (Fs.getD i []) [i])
      (match defOf i tab with
        | none => false
        | some e => allLt i (lhsW e) && weq (Fs.getD i []) (flatW rs Fs (lhsW e)))

@[expose] def wfOK : List ℕ → List Ent → Bool
  | _, [] => true
  | K, e :: t => (lhsW e).all (memB · K) &&
      match e.2.2.1 with
      | none => weq e.2.2.2 [] && wfOK K t
      | some c => cond (weq e.2.2.2 []) (wfOK (c :: K) t) ((rhsW e).all (memB · K) && wfOK K t)

@[expose] def rep (u : List ℕ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => u ++ rep u e

@[expose] def eqW (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (raw o : List ℕ) : Bool :=
  weq (flatW rs Fs raw) (flatW rs Fs o) ||
    match o with
    | [x] => weq (flatW rs Fs raw) (expand rs Fs tab x)
    | _ => false

@[expose] def isLit (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (u : List ℕ) (v : ℕ) : Bool :=
  weq u [v] || weq (flatW rs Fs u) (expand rs Fs tab v)

@[expose] def isInv (rs : List (ℕ × ℕ × Option ℕ)) (x y : ℕ) : Bool :=
  match look rs x y with
  | some none => true
  | _ => false

@[expose] def stepOK (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (σ : ℕ → Option (List ℕ)) : Ins → List ℕ × ℕ → Bool
  | .mu i j _, (o, _) =>
    match σ i, σ j with
    | some u, some w => eqW rs Fs tab (u ++ w) o
    | _, _ => false
  | .pwr e i _, (o, _) =>
    match σ i with
    | some u => eqW rs Fs tab (rep u e) o
    | none => false
  | .iv i _, (o, v) =>
    match σ i with
    | some [] => weq o []
    | some u => isLit rs Fs tab u v &&
        match o with
        | [y] => isInv rs v y
        | _ => false
    | none => false

@[expose] def upd (σ : ℕ → Option (List ℕ)) (k : ℕ) (o : List ℕ) : ℕ → Option (List ℕ) :=
  fun i => cond (Nat.beq i k) (some o) (σ i)

@[expose] def runOK (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent) :
    List Ins → List (List ℕ × ℕ) → (ℕ → Option (List ℕ)) → Bool
  | [], [], _ => true
  | ins :: p, o :: os, σ => stepOK rs Fs tab σ ins o && runOK rs Fs tab p os (upd σ (insOut ins) o.1)
  | _, _, _ => false

@[expose] def finSt : List Ins → List (List ℕ × ℕ) → (ℕ → Option (List ℕ)) → ℕ → Option (List ℕ)
  | ins :: p, o :: os, σ => finSt p os (upd σ (insOut ins) o.1)
  | _, _, σ => σ

@[expose] def finOK (rs : List (ℕ × ℕ × Option ℕ)) (Fs : List (List ℕ)) (tab : List Ent)
    (σ : ℕ → Option (List ℕ)) : List ℕ → List ℕ → Bool
  | [], [] => true
  | r :: rg, i :: is =>
    (match σ r with
      | some u => isLit rs Fs tab u i
      | none => false) && finOK rs Fs tab σ rg is
  | _, _ => false

@[expose] def lookI : List (ℕ × Option ℕ) → ℕ → Option (Option ℕ)
  | [], _ => none
  | (a, o) :: t, r => cond (Nat.beq a r) (some o) (lookI t r)

@[expose] def init0 (init : List (ℕ × Option ℕ)) (dflt : Bool) (r : ℕ) : Option (List ℕ) :=
  match lookI init r with
  | some none => some []
  | some (some l) => some [l]
  | none => cond dflt (some []) none

@[expose] def TabOK (L : List (List ℕ)) (tab : List Ent) : Prop :=
  List.rec (motive := fun _ => Prop) True
    (fun e _ ih => AllStrips (e.2.1.map fun i => L.getD i idStrips) (L.getD e.1 idStrips)
      ((e.2.2.1.elim idStrips fun c => L.getD c idStrips).map
        (mulW (e.2.2.2.map fun i => L.getD i idStrips))) ∧ ih) tab

@[expose] def WfL (L : List (List ℕ)) (wl : List ℕ) : Prop :=
  List.rec (motive := fun _ => Prop) True (fun i _ ih => wfMat (L.getD i idStrips) = true ∧ ih) wl

@[expose] def RegsOK (prog : List Ins) (init : List (ℕ × Option (List ℕ))) (dflt : Bool)
    (regs : List ℕ) (tgt : List (List ℕ)) : Prop :=
  ∀ {G : Type} [Group G] (f : G →* Mat) (ρ : ℕ → G),
    (∀ p ∈ init, f (ρ p.1) = (p.2.map stripMat).getD 1) →
    (dflt = true → ∀ r, r ∉ init.map Prod.fst → ρ r = 1) →
    ∀ k < regs.length, f (prog.foldl insStepG ρ (regs.getD k 0)) = stripMat (tgt.getD k [])

theorem memB_spec {x : ℕ} : ∀ {l : List ℕ}, memB x l = true → x ∈ l
  | [], h => by simp [memB] at h
  | y :: t, h => by
    simp only [memB, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memB_spec h)

theorem weq_spec : ∀ {u w : List ℕ}, weq u w = true → u = w
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [weq] at h
  | _ :: _, [], h => by simp [weq] at h
  | x :: u, y :: w, h => by
    simp only [weq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, weq_spec h.2]

theorem oeqB_spec : ∀ {a b : Option ℕ}, oeqB a b = true → a = b
  | none, none, _ => rfl
  | some x, some y, h => by rw [Nat.eq_of_beq_eq_true h]
  | none, some _, h => by simp [oeqB] at h
  | some _, none, h => by simp [oeqB] at h

theorem allLt_spec {n : ℕ} : ∀ {w : List ℕ}, allLt n w = true → ∀ x ∈ w, x < n
  | [], _, _, hx => by simp at hx
  | y :: t, h, x, hx => by
    simp only [allLt, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_of_ble_eq_true h.1
    · exact allLt_spec h.2 x hx

section Monoid

variable {M : Type*} [Monoid M] (val : ℕ → M)

@[expose] def wv (w : List ℕ) : M := (w.map val).prod

@[expose] def RulesSound (rs : List (ℕ × ℕ × Option ℕ)) : Prop :=
  ∀ r ∈ rs, val r.1 * val r.2.1 = wv val (r.2.2.elim [] fun c => [c])

@[expose] def TabSound (tab : List Ent) : Prop := ∀ e ∈ tab, wv val (lhsW e) = wv val (rhsW e)

variable {val}

theorem wv_nil : wv val [] = 1 := rfl

theorem wv_cons (x : ℕ) (w : List ℕ) : wv val (x :: w) = val x * wv val w := by
  simp [wv]

theorem wv_append (u w : List ℕ) : wv val (u ++ w) = wv val u * wv val w := by
  simp [wv]

theorem wv_single (x : ℕ) : wv val [x] = val x := by simp [wv]

theorem look_sound : ∀ {rs : List (ℕ × ℕ × Option ℕ)}, RulesSound val rs → ∀ {x y : ℕ}
    {z : Option ℕ}, look rs x y = some z → val x * val y = wv val (z.elim [] fun c => [c])
  | [], _, _, _, _, h => by simp [look] at h
  | (a, b, c) :: t, ht, x, y, z, h => by
    unfold look at h
    cases hc : (Nat.beq a x && Nat.beq b y)
    · rw [hc, cond_false] at h
      exact look_sound (fun p hp => ht p (List.mem_cons_of_mem _ hp)) h
    · rw [hc, cond_true, Option.some.injEq] at h
      rw [Bool.and_eq_true] at hc
      have e1 := Nat.eq_of_beq_eq_true hc.1
      have e2 := Nat.eq_of_beq_eq_true hc.2
      subst e1 e2 h
      exact ht _ List.mem_cons_self

theorem push_sound {rs : List (ℕ × ℕ × Option ℕ)} (hr : RulesSound val rs) :
    ∀ (w : List ℕ) (x : ℕ), wv val (push rs x w) = val x * wv val w
  | [], x => by rw [push, wv_single, wv_nil, mul_one]
  | y :: t, x => by
    unfold push
    cases hl : look rs x y with
    | none => rfl
    | some z =>
      have e := look_sound hr hl
      cases z with
      | none =>
        simp only [Option.elim_none] at e
        rw [wv_cons, ← mul_assoc, e, wv_nil, one_mul]
      | some z =>
        simp only [Option.elim_some, wv_single] at e
        rw [push_sound hr t z, wv_cons, ← mul_assoc, e]

theorem red_sound {rs : List (ℕ × ℕ × Option ℕ)} (hr : RulesSound val rs) :
    ∀ w : List ℕ, wv val (red rs w) = wv val w
  | [] => rfl
  | x :: w => by
    change wv val (push rs x (red rs w)) = _
    rw [push_sound hr, red_sound hr w, wv_cons]

theorem cat_sound {Fs : List (List ℕ)} (hF : ∀ i, wv val (Fs.getD i []) = val i) :
    ∀ w : List ℕ, wv val (cat Fs w) = wv val w
  | [] => rfl
  | x :: w => by
    change wv val (Fs.getD x [] ++ cat Fs w) = _
    rw [wv_append, hF, cat_sound hF w, wv_cons]

theorem flatW_sound {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} (hr : RulesSound val rs)
    (hF : ∀ i, wv val (Fs.getD i []) = val i) (w : List ℕ) :
    wv val (flatW rs Fs w) = wv val w := by
  rw [flatW, red_sound hr, cat_sound hF]

theorem defOf_spec {x : ℕ} : ∀ {tab : List Ent} {e : Ent}, defOf x tab = some e →
    e ∈ tab ∧ rhsW e = [x]
  | [], _, h => by simp [defOf] at h
  | d :: t, e, h => by
    unfold defOf at h
    cases hc : (oeqB d.2.2.1 (some x) && weq d.2.2.2 [])
    · rw [hc, cond_false] at h
      exact ⟨List.mem_cons_of_mem _ (defOf_spec h).1, (defOf_spec h).2⟩
    · rw [hc, cond_true, Option.some.injEq] at h
      subst h
      rw [Bool.and_eq_true] at hc
      refine ⟨List.mem_cons_self, ?_⟩
      unfold rhsW
      rw [oeqB_spec hc.1, weq_spec hc.2]

theorem expand_sound {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} {tab : List Ent}
    (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i) (ht : TabSound val tab)
    (x : ℕ) : wv val (expand rs Fs tab x) = val x := by
  unfold expand
  cases hd : defOf x tab with
  | none => exact wv_single x
  | some e =>
    obtain ⟨he, hx⟩ := defOf_spec hd
    rw [flatW_sound hr hF, ht e he, hx, wv_single]

theorem rep_sound (u : List ℕ) : ∀ e : ℕ, wv val (rep u e) = wv val u ^ e
  | 0 => by rw [rep, pow_zero]; rfl
  | e + 1 => by rw [rep, wv_append, rep_sound u e, pow_succ']

theorem eqW_sound {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} {tab : List Ent}
    (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i) (ht : TabSound val tab)
    {raw o : List ℕ} (h : eqW rs Fs tab raw o = true) : wv val raw = wv val o := by
  unfold eqW at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [← flatW_sound hr hF raw, weq_spec h, flatW_sound hr hF]
  · match o, h with
    | [x], h => rw [← flatW_sound hr hF raw, weq_spec h, expand_sound hr hF ht, wv_single]

theorem isLit_sound {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} {tab : List Ent}
    (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i) (ht : TabSound val tab)
    {u : List ℕ} {v : ℕ} (h : isLit rs Fs tab u v = true) : wv val u = val v := by
  unfold isLit at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [weq_spec h, wv_single]
  · rw [← flatW_sound hr hF u, weq_spec h, expand_sound hr hF ht]

end Monoid

section Run

variable {G : Type*} [Group G] {M : Type*} [Monoid M] {f : G →* M} {val : ℕ → M}
  {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)} {tab : List Ent}

@[expose] def Inv (f : G →* M) (val : ℕ → M) (ρ : ℕ → G) (σ : ℕ → Option (List ℕ)) : Prop :=
  ∀ r w, σ r = some w → f (ρ r) = wv val w

theorem inv_upd {ρ : ℕ → G} {σ : ℕ → Option (List ℕ)} (h : Inv f val ρ σ) (k : ℕ) (g : G)
    (o : List ℕ) (hg : f g = wv val o) : Inv f val (Function.update ρ k g) (upd σ k o) := by
  intro r w hr
  unfold upd at hr
  by_cases e : r = k
  · subst e
    rw [Nat.beq_refl, cond_true, Option.some.injEq] at hr
    rw [Function.update_self, hg, hr]
  · have hb : Nat.beq r k = false := by
      cases hb : Nat.beq r k
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) e
    rw [hb, cond_false] at hr
    rw [Function.update_of_ne e]
    exact h r w hr

theorem map_inv_of {g : G} {y : M} (hg : f g * y = 1) : f g⁻¹ = y := by
  calc f g⁻¹ = f g⁻¹ * (f g * y) := by rw [hg, mul_one]
    _ = y := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem step_sound (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i)
    (ht : TabSound val tab) {ρ : ℕ → G} {σ : ℕ → Option (List ℕ)} (h : Inv f val ρ σ) (ins : Ins)
    (o : List ℕ × ℕ) (hs : stepOK rs Fs tab σ ins o = true) :
    Inv f val (insStepG ρ ins) (upd σ (insOut ins) o.1) := by
  obtain ⟨o, v⟩ := o
  cases ins with
  | mu i j k =>
    simp only [stepOK] at hs
    cases hi : σ i with
    | none => rw [hi] at hs; exact absurd hs (by simp)
    | some u =>
      cases hj : σ j with
      | none => rw [hi, hj] at hs; exact absurd hs (by simp)
      | some w =>
        rw [hi, hj] at hs
        refine inv_upd h k _ o ?_
        rw [map_mul, h i u hi, h j w hj, ← wv_append, eqW_sound hr hF ht hs]
  | pwr e i k =>
    simp only [stepOK] at hs
    cases hi : σ i with
    | none => rw [hi] at hs; exact absurd hs (by simp)
    | some u =>
      rw [hi] at hs
      refine inv_upd h k _ o ?_
      rw [map_pow, h i u hi, ← rep_sound, eqW_sound hr hF ht hs]
  | iv i k =>
    simp only [stepOK] at hs
    cases hi : σ i with
    | none => rw [hi] at hs; exact absurd hs (by simp)
    | some u =>
      rw [hi] at hs
      refine inv_upd h k _ o ?_
      match u, hs with
      | [], hs =>
        rw [weq_spec hs]
        exact map_inv_of (by rw [h i [] hi, wv_nil, one_mul])
      | x :: u', hs =>
        simp only [Bool.and_eq_true] at hs
        obtain ⟨hl, hy⟩ := hs
        match o, hy with
        | [y], hy =>
          have hlk : look rs v y = some none := by
            cases hk : look rs v y with
            | none => simp [isInv, hk] at hy
            | some z =>
              cases z with
              | none => rfl
              | some _ => simp [isInv, hk] at hy
          have e := look_sound hr hlk
          simp only [Option.elim_none, wv_nil] at e
          rw [wv_single]
          refine map_inv_of ?_
          rw [h i _ hi, isLit_sound hr hF ht hl, e]

theorem runOK_sound (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i)
    (ht : TabSound val tab) :
    ∀ (prog : List Ins) (outs : List (List ℕ × ℕ)) (ρ : ℕ → G) (σ : ℕ → Option (List ℕ)),
      Inv f val ρ σ → runOK rs Fs tab prog outs σ = true →
        Inv f val (prog.foldl insStepG ρ) (finSt prog outs σ)
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, h => by simp [runOK] at h
  | _ :: _, [], _, _, _, h => by simp [runOK] at h
  | ins :: p, o :: os, ρ, σ, h, hs => by
    simp only [runOK, Bool.and_eq_true] at hs
    rw [List.foldl_cons]
    exact runOK_sound hr hF ht p os _ _ (step_sound hr hF ht h ins o hs.1) hs.2

theorem finOK_sound (hr : RulesSound val rs) (hF : ∀ i, wv val (Fs.getD i []) = val i)
    (ht : TabSound val tab) {ρ : ℕ → G} {σ : ℕ → Option (List ℕ)} (h : Inv f val ρ σ) :
    ∀ (rg is : List ℕ), finOK rs Fs tab σ rg is = true →
      rg.length = is.length ∧ ∀ k < rg.length, f (ρ (rg.getD k 0)) = val (is.getD k 0)
  | [], [], _ => ⟨rfl, fun k hk => by simp at hk⟩
  | [], _ :: _, hs => by simp [finOK] at hs
  | _ :: _, [], hs => by simp [finOK] at hs
  | r :: rg, i :: is, hs => by
    simp only [finOK, Bool.and_eq_true] at hs
    obtain ⟨h1, h2⟩ := hs
    obtain ⟨hl, hk⟩ := finOK_sound hr hF ht h rg is h2
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    cases k with
    | zero =>
      cases hσ : σ r with
      | none => rw [hσ] at h1; exact absurd h1 (by simp)
      | some u =>
        rw [hσ] at h1
        simpa [h r u hσ] using isLit_sound hr hF ht h1
    | succ k => simpa using hk k (by simpa using hk')

theorem lookI_mem : ∀ {init : List (ℕ × Option ℕ)} {r : ℕ} {o : Option ℕ}, lookI init r = some o →
    (r, o) ∈ init
  | [], _, _, h => by simp [lookI] at h
  | (a, b) :: t, r, o, h => by
    unfold lookI at h
    cases hc : Nat.beq a r
    · rw [hc, cond_false] at h
      exact List.mem_cons_of_mem _ (lookI_mem h)
    · rw [hc, cond_true, Option.some.injEq] at h
      rw [← Nat.eq_of_beq_eq_true hc, ← h]
      exact List.mem_cons_self

theorem lookI_none : ∀ {init : List (ℕ × Option ℕ)} {r : ℕ}, lookI init r = none →
    r ∉ init.map Prod.fst
  | [], _, _ => by simp
  | (a, b) :: t, r, h => by
    unfold lookI at h
    cases hc : Nat.beq a r
    · rw [hc, cond_false] at h
      have := lookI_none h
      have hne : a ≠ r := Nat.ne_of_beq_eq_false hc
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun e => hne e.symm, this⟩
    · rw [hc, cond_true] at h
      exact absurd h (by simp)

theorem init0_sound {ρ : ℕ → G} {init : List (ℕ × Option ℕ)} {dflt : Bool}
    (hi : ∀ p ∈ init, f (ρ p.1) = (p.2.map val).getD 1)
    (hd : dflt = true → ∀ r, r ∉ init.map Prod.fst → ρ r = 1) : Inv f val ρ (init0 init dflt) := by
  intro r w hr
  unfold init0 at hr
  cases hl : lookI init r with
  | none =>
    rw [hl] at hr
    cases dflt with
    | false => exact absurd hr (by simp)
    | true =>
      rw [cond_true, Option.some.injEq] at hr
      rw [← hr, hd rfl r (lookI_none hl), map_one, wv_nil]
  | some o =>
    rw [hl] at hr
    have := hi _ (lookI_mem hl)
    cases o with
    | none =>
      simp only [Option.some.injEq] at hr
      rw [← hr, wv_nil]
      simpa using this
    | some l =>
      simp only [Option.some.injEq] at hr
      rw [← hr, wv_single]
      simpa using this

end Run

@[expose] noncomputable def litV (L : List (List ℕ)) (i : ℕ) : Mat := stripMat (L.getD i idStrips)

theorem stripMat_idStrips : stripMat idStrips = 1 := by
  rw [stripMat_eq]
  exact stripMatG_id (by norm_num) idStrips_eq

theorem mulW_nil (a : ℕ) : mulW [] a = a := rfl

theorem allStrips_map (Ds : List (List ℕ)) : ∀ C : List ℕ, AllStrips Ds C (C.map (mulW Ds))
  | [] => AllStrips.nil
  | c :: C => AllStrips.cons c _ C _ (Nat.beq_refl _) (allStrips_map Ds C)

theorem foldl_mul_eq (a : Mat) : ∀ l : List Mat, l.foldl (· * ·) a = a * l.prod
  | [] => by simp
  | b :: l => by rw [List.foldl_cons, foldl_mul_eq _ l, List.prod_cons, mul_assoc]

theorem wv_litV (L : List (List ℕ)) (w : List ℕ) :
    wv (litV L) w = ((w.map fun i => L.getD i idStrips).map stripMat).prod := by
  rw [wv, List.map_map]
  rfl

theorem map_mulW_nil (l : List ℕ) : l.map (mulW []) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, mulW_nil]

theorem wfOK_sound {L : List (List ℕ)} : ∀ (tab : List Ent) (K : List ℕ),
    (∀ i ∈ K, wfMat (L.getD i idStrips) = true) → wfOK K tab = true → TabOK L tab →
      TabSound (litV L) tab
  | [], _, _, _, _ => fun _ he => by simp at he
  | (A, Ws, C, Ds) :: t, K, hK, hw, htab => by
    obtain ⟨hs, htab⟩ := htab
    dsimp only at hs
    unfold wfOK at hw
    rw [Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨hl, hw⟩ := hw
    have hlk : ∀ i ∈ A :: Ws, wfMat (L.getD i idStrips) = true := fun i hi =>
      hK i (memB_spec (hl i (by simpa [lhsW] using hi)))
    have hA := hlk A List.mem_cons_self
    have hWs : ∀ W ∈ Ws.map fun i => L.getD i idStrips, wfMat W = true := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hW
      exact hlk i (List.mem_cons_of_mem _ hi)
    have hcons : ∀ (K' : List ℕ), (∀ i ∈ K', wfMat (L.getD i idStrips) = true) →
        wfOK K' t = true → wv (litV L) (lhsW (A, Ws, C, Ds)) = wv (litV L) (rhsW (A, Ws, C, Ds)) →
        TabSound (litV L) ((A, Ws, C, Ds) :: t) := by
      intro K' hK' hw' he d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact he
      · exact wfOK_sound t K' hK' hw' htab d hd
    cases C with
    | none =>
      dsimp only at hw
      rw [Bool.and_eq_true] at hw
      obtain ⟨hD, hw⟩ := hw
      have hD := weq_spec hD
      subst hD
      refine hcons K hK hw ?_
      simp only [Option.elim_none, List.map_nil, map_mulW_nil] at hs
      have hlhs := stripMat_mul_of_allStrips hWs hA hs
      rw [foldl_mul_eq, stripMat_idStrips] at hlhs
      change wv (litV L) (A :: Ws) = 1
      rw [wv_cons, wv_litV]
      exact hlhs
    | some c =>
      dsimp only at hw
      simp only [Option.elim_some] at hs
      cases hD : weq Ds []
      · rw [hD, cond_false, Bool.and_eq_true, List.all_eq_true] at hw
        obtain ⟨hr, hw⟩ := hw
        refine hcons K hK hw ?_
        have hrk : ∀ i ∈ c :: Ds, wfMat (L.getD i idStrips) = true := fun i hi =>
          hK i (memB_spec (hr i (by simpa [rhsW] using hi)))
        have hDs : ∀ W ∈ Ds.map fun i => L.getD i idStrips, wfMat W = true := by
          intro W hW
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hW
          exact hrk i (List.mem_cons_of_mem _ hi)
        have hlhs := stripMat_mul_of_allStrips hWs hA hs
        have hrhs := stripMat_mul_of_allStrips hDs (hrk c List.mem_cons_self) (allStrips_map _ _)
        rw [foldl_mul_eq] at hlhs hrhs
        change wv (litV L) (A :: Ws) = wv (litV L) (c :: Ds)
        rw [wv_cons, wv_cons, wv_litV, wv_litV]
        exact hlhs.trans hrhs.symm
      · rw [hD, cond_true] at hw
        have hD := weq_spec hD
        subst hD
        simp only [List.map_nil, map_mulW_nil] at hs
        have hc : wfMat (L.getD c idStrips) = true := wfMat_of_allStrips hA hs
        refine hcons (c :: K) (fun i hi => ?_) hw ?_
        · rcases List.mem_cons.1 hi with rfl | hi
          · exact hc
          · exact hK i hi
        · have hlhs := stripMat_mul_of_allStrips hWs hA hs
          rw [foldl_mul_eq] at hlhs
          change wv (litV L) (A :: Ws) = wv (litV L) [c]
          rw [wv_cons, wv_single, wv_litV]
          exact hlhs

theorem wfL_spec {L : List (List ℕ)} : ∀ {wl : List ℕ}, WfL L wl →
    ∀ i ∈ wl, wfMat (L.getD i idStrips) = true
  | [], _, _, hi => by simp at hi
  | j :: wl, h, i, hi => by
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact wfL_spec h.2 i hi

theorem rules_sound {val : ℕ → Mat} {tab : List Ent} (ht : TabSound val tab) :
    ∀ {rs : List (ℕ × ℕ × Option ℕ)}, rs.all (ruleOK tab) = true → RulesSound val rs := by
  intro rs hrs r hr
  obtain ⟨x, y, z⟩ := r
  have h := List.all_eq_true.1 hrs _ hr
  simp only [ruleOK, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨e, he, h⟩ := h
  have hte := ht e he
  rcases h with ⟨h1, h2⟩ | ⟨⟨h0, h1⟩, h2⟩
  · rw [weq_spec h1, weq_spec h2] at hte
    simpa [wv_cons, wv_nil] using hte
  · rw [weq_spec h1, weq_spec h2] at hte
    rw [oeqB_spec h0]
    simp only [wv_cons, wv_nil, mul_one] at hte
    simpa [wv_nil] using mul_eq_one_comm.1 hte

theorem flOK_sound {val : ℕ → Mat} {rs : List (ℕ × ℕ × Option ℕ)} {Fs : List (List ℕ)}
    {tab : List Ent} {S : List ℕ} {n : ℕ} (hr : RulesSound val rs) (ht : TabSound val tab)
    (hn : ∀ i, n ≤ i → val i = 1) (h : flOK rs Fs tab S n = true) :
    ∀ i, wv val (Fs.getD i []) = val i := by
  simp only [flOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, h⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < n
    · have hc := h i hi
      cases hm : memB i S
      · rw [hm, cond_false] at hc
        cases hd : defOf i tab with
        | none => rw [hd] at hc; exact absurd hc (by simp)
        | some e =>
          rw [hd, Bool.and_eq_true] at hc
          obtain ⟨hlt, hw⟩ := hc
          obtain ⟨he, hx⟩ := defOf_spec hd
          have hlt := allLt_spec hlt
          rw [weq_spec hw, flatW, red_sound hr]
          have hc : ∀ w : List ℕ, (∀ x ∈ w, x < i) → wv val (cat Fs w) = wv val w := by
            intro w
            induction w with
            | nil => intro _; rfl
            | cons x w ihw =>
              intro hw'
              change wv val (Fs.getD x [] ++ cat Fs w) = _
              rw [wv_append, ih x (hw' x List.mem_cons_self),
                ihw (fun y hy => hw' y (List.mem_cons_of_mem _ hy)), wv_cons]
          rw [hc _ hlt, ht e he, hx, wv_single]
      · rw [hm, cond_true] at hc
        rw [weq_spec hc, wv_single]
    · have : Fs.getD i [] = [] := by
        rw [List.getD_eq_default _ _ (by have := Nat.le_of_ble_eq_true hlen; omega)]
      rw [this, wv_nil, hn i (by omega)]

theorem regCert {L : List (List ℕ)} {tab : List Ent} {wl : List ℕ} {rs : List (ℕ × ℕ × Option ℕ)}
    {Fs : List (List ℕ)} {S : List ℕ} {prog : List Ins} {outs : List (List ℕ × ℕ)}
    {initI : List (ℕ × Option ℕ)} {dflt : Bool} {regs idx : List ℕ}
    {init : List (ℕ × Option (List ℕ))} {tgt : List (List ℕ)}
    (hwl : WfL L wl) (htab : TabOK L tab) (hwf : wfOK wl tab = true)
    (hrs : rs.all (ruleOK tab) = true) (hfl : flOK rs Fs tab S L.length = true)
    (hrun : runOK rs Fs tab prog outs (init0 initI dflt) = true)
    (hfin : finOK rs Fs tab (finSt prog outs (init0 initI dflt)) regs idx = true)
    (hinit : initI.map (fun p => (p.1, p.2.map fun i => L.getD i idStrips)) = init)
    (htgt : idx.map (fun i => L.getD i idStrips) = tgt) :
    RegsOK prog init dflt regs tgt := by
  intro G _ f ρ hi hd k hk
  have ht := wfOK_sound tab wl (wfL_spec hwl) hwf htab
  have hr := rules_sound ht hrs
  have hn : ∀ i, L.length ≤ i → litV L i = 1 := fun i hi => by
    rw [litV, List.getD_eq_default _ _ hi, stripMat_idStrips]
  have hF := flOK_sound hr ht hn hfl
  have h0 : Inv f (litV L) ρ (init0 initI dflt) := by
    refine init0_sound (fun p hp => ?_) (fun hdf r hr' => hd hdf r ?_)
    · have := hi (p.1, p.2.map fun i => L.getD i idStrips) (by rw [← hinit]; exact List.mem_map_of_mem hp)
      rw [this]
      cases p.2 <;> rfl
    · rw [← hinit, List.map_map]
      exact hr'
  have hR := runOK_sound hr hF ht prog outs ρ _ h0 hrun
  obtain ⟨hl, hv⟩ := finOK_sound hr hF ht hR regs idx hfin
  have hk' : k < idx.length := hl ▸ hk
  rw [hv k hk, ← htgt, List.getD_eq_getElem _ _ hk',
    List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map]
  rfl

theorem RegsOK.runG {prog : List Ins} {A B : List ℕ} {regs : List ℕ} {tgt : List (List ℕ)}
    (h : RegsOK prog [(1, some A), (2, some B)] true regs tgt)
    (a b : GL (Fin 4370) (ZMod 2)) (ha : (a : Mat) = stripMat A) (hb : (b : Mat) = stripMat B) :
    ∀ k < regs.length, ((CFSG.Monster.B.Pinned.runG prog a b (regs.getD k 0) :
      GL (Fin 4370) (ZMod 2)) : Mat) = stripMat (tgt.getD k []) := by
  intro k hk
  refine h (Units.coeHom Mat) (CFSG.Monster.B.progInit a b) ?_ ?_ k hk
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa [CFSG.Monster.B.progInit] using ha
    · simpa [CFSG.Monster.B.progInit] using hb
  · intro _ r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp [CFSG.Monster.B.progInit, hr.1, hr.2]

example : red [(0, 1, none), (1, 0, none)] [2, 0, 1, 3] = [2, 3] := by decide
example : red [(0, 0, some 1)] [0, 0, 0] = [0, 1] := by decide
example : ruleOK [(0, [1], none, [])] (1, 0, none) = true := by decide
example : ruleOK [(0, [1], none, [])] (1, 0, some 2) = false := by decide
example : ruleOK [(0, [1], some 2, [])] (1, 0, some 2) = false := by decide
example : wfOK [0] [(0, [1], some 2, [])] = false := by decide
example : wfOK [0, 1] [(0, [1], some 2, []), (2, [2], some 3, [])] = true := by decide
example : wfOK [0] [(0, [0], some 1, [2])] = false := by decide
example : flOK [] [[0], [0, 0]] [(0, [0], some 1, [])] [0] 2 = true := by decide
example : flOK [] [[0], [0]] [(0, [0], some 1, [])] [0] 2 = false := by decide
example : flOK [] [[0], [1]] [(1, [0], some 1, [])] [0] 2 = false := by decide
example : runOK [] [[0], [1]] [] [.mu 1 2 3] [([0, 1], 0)] (init0 [(1, some 0), (2, some 1)] true)
    = true := by decide
example : runOK [] [[0], [1]] [] [.mu 1 2 3] [([1, 0], 0)] (init0 [(1, some 0), (2, some 1)] true)
    = false := by decide
example : runOK [] [[0], [1]] [] [.iv 1 3] [([1], 0)] (init0 [(1, some 0)] false) = false := by
  decide
example : runOK [(0, 1, none)] [[0], [1]] [] [.iv 1 3] [([1], 0)] (init0 [(1, some 0)] false)
    = true := by decide
example : runOK [] [[0], [1]] [] [.mu 1 2 3] [([0, 1], 0)] (init0 [(1, some 0)] false)
    = false := by decide

end CFSG.KC.BM.Reg

end
