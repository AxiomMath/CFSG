module

public import Certificates.Data.Kernel.Spor.ONCSOp
public import CFSG.Certificates.Kernel.Spor.ONTauSound

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KC.Ord CFSG.KS.Ord CFSG.RankThree.Native.ONTriple

variable {G : Type*} [Group G] {φ : G →* Matrix (Fin 154) (Fin 154) (ZMod 3)}

theorem chunkK_conj {mul : Nat → Nat → Nat → Nat → Nat → Nat → Nat}
    {bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat}
    {cs₀ ds₀ L₀ H₀ cm₀ rm₀ one₀ a b bi pre post : Nat} {FA FB : Nat → Nat} {w : List Int}
    (ha : bat cs₀ ds₀ FA (nat_lit 0) (nat_lit 154) = a)
    (hb : bat cs₀ ds₀ FB (nat_lit 0) (nat_lit 154) = b)
    (hbi : mul L₀ H₀ cm₀ rm₀ (mul L₀ H₀ cm₀ rm₀ b b) b = bi)
    (h : (strictB cs₀ fun cs => strictB ds₀ fun ds => strictB L₀ fun L => strictB H₀ fun H =>
      strictB cm₀ fun cm => strictB rm₀ fun rm => strictB one₀ fun one =>
      strictB (bat cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
      strictB (bat cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
      strictB (mul L H cm rm (mul L H cm rm b b) b) fun bi =>
        bAnd(Nat.beq (mul L H cm rm a a) one, bAnd(Nat.beq (mul L H cm rm b bi) one,
          Nat.beq (wordK (mul L H cm rm) (seedL a a b bi) w pre) post))) = true) :
    mul L₀ H₀ cm₀ rm₀ a a = one₀ ∧ mul L₀ H₀ cm₀ rm₀ b bi = one₀ ∧
      wordK (mul L₀ H₀ cm₀ rm₀) (seedL a a b bi) w pre = post := by
  subst ha hb hbi
  simp only [strictB_eq'] at h
  rw [bAnd_iff', bAnd_iff'] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem chunkK_sound {FA FB : Nat → Nat} {w : List Int} {pre post : Nat} {gA gB x : G}
    (h : chunkK FA FB w pre post = true) (ha : Reps φ (batK CS DS FA 0 154) gA)
    (hb : Reps φ (batK CS DS FB 0 154) gB) (hpre : Reps φ pre x) :
    Reps φ post (x * CFSG.Sporadic.Th.wordG (seedG gA gB) w) := by
  obtain ⟨h1, h2, h3⟩ := chunkK_conj (mul := mul3) (bat := batK) (cs₀ := CS) (ds₀ := DS)
    (L₀ := LL) (H₀ := HH) (cm₀ := CM) (rm₀ := RM) (one₀ := ONE) (a := batK CS DS FA 0 154)
    (b := batK CS DS FB 0 154) (pre := pre) (post := post) (w := w) rfl rfl rfl h
  have hbi := (mul3_sound (mul3_sound hb.1 hb.1).1 hb.1).1
  have hL := seedL_reps ha (reps_inv ha ha.1 h1) hb (reps_inv hb hbi h2)
  rw [← h3]
  exact wordK_reps hL w pre x hpre

@[expose] def sopLt : Nat → List SOp → Bool
  | _, [] => true
  | n, .word w :: p => w.all (fun l => decide (l.1 < n)) && sopLt (n + 1) p
  | n, .pow _ i :: p => decide (i < n) && sopLt (n + 1) p

theorem invS_sound {VI : Nat → Nat} {r x : Nat} {g : G}
    (h : invS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI r x = true) (hx : Reps φ x g) :
    VI r ≠ 0 → Reps φ (VI r) g⁻¹ := by
  intro hv
  have hb : Nat.beq (VI r) 0 = false := by
    cases e : Nat.beq (VI r) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hv
  unfold invS at h
  rw [strictB_eq', hb] at h
  have h' : bAnd(vld3 LL HH (VI r), Nat.beq (mul3 LL HH CM RM x (VI r)) ONE) = true := h
  rw [bAnd_iff'] at h'
  exact reps_inv hx (vld3_canon h'.1) (Nat.eq_of_beq_eq_true h'.2)

theorem initS_spec {VI : Nat → Nat} {R : List Nat} : ∀ {n : Nat},
    initS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI R n = true →
      ∀ r < n, invS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI r (R.getD r 0) = true
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, h, r, hr => by
    change bAnd(invS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI n (List.getD R n 0),
      initS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI R n) = true at h
    rw [bAnd_iff'] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · exact initS_spec h.2 r hr
    · exact h.1

theorem powS_zero (mul : Nat → Nat → Nat) (x acc : Nat) : powS mul x 0 acc = acc := rfl

theorem powS_succ (mul : Nat → Nat → Nat) (x e acc : Nat) :
    powS mul x (e + 1) acc = strictN (powS mul x e acc) (fun y => mul y x) := rfl

theorem powS_reps {x : Nat} {g : G} (hx : Reps φ x g) :
    ∀ e, Reps φ (powS (mul3 LL HH CM RM) x e ONE) (g ^ e)
  | 0 => by
    rw [pow_zero, powS_zero]
    exact reps_one
  | e + 1 => by
    rw [powS_succ, strictN_eq', pow_succ]
    exact reps_mul (powS_reps hx e) hx

variable (φ) in
def sopInv (VI : Nat → Nat) (R : List Nat) (ok : Bool) (Gs : Array G) : Prop :=
  R.length = Gs.size ∧ (ok = true → ∀ r < R.length, Reps φ (R.getD r 0) (Gs.getD r 1) ∧
    (VI r ≠ 0 → Reps φ (VI r) (Gs.getD r 1)⁻¹))

theorem sopInv_push {VI : Nat → Nat} {R : List Nat} {ok ok' : Bool} {Gs : Array G} {x : Nat}
    {y : G} (H : sopInv φ VI R ok Gs) (hok : ok' = true → ok = true)
    (hx : ok' = true → Reps φ x y ∧ (VI R.length ≠ 0 → Reps φ (VI R.length) y⁻¹)) :
    sopInv φ VI (R ++ [x]) ok' (Gs.push y) := by
  refine ⟨by simp [H.1], fun h' r hr => ?_⟩
  rw [List.length_append, List.length_singleton] at hr
  rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
  · have e1 : (R ++ [x]).getD r 0 = R.getD r 0 := List.getD_append _ _ _ _ hr
    have e2 : (Gs.push y).getD r 1 = Gs.getD r 1 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, H.1 ▸ hr, Nat.ne_of_lt (H.1 ▸ hr)]
    rw [e1, e2]
    exact H.2 (hok h') r hr
  · have e1 : (R ++ [x]).getD R.length 0 = x := by simp [List.getD_eq_getElem?_getD]
    have e2 : (Gs.push y).getD R.length 1 = y := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, H.1]
    rw [e1, e2]
    exact hx h'

theorem letV_reps {VI : Nat → Nat} {R : List Nat} {Gs : Array G}
    (H2 : ∀ r < R.length, Reps φ (R.getD r 0) (Gs.getD r 1) ∧
      (VI r ≠ 0 → Reps φ (VI r) (Gs.getD r 1)⁻¹)) {i : Nat} {b : Bool} (hl : i < R.length)
    (hrec : Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (VI i) 0)) true b = true) :
    Reps φ (letV R VI (i, b)) (if b then Gs.getD i 1 else (Gs.getD i 1)⁻¹) := by
  cases b
  · change Bool.rec (motive := fun _ => Bool) true false (Nat.beq (VI i) 0) = true at hrec
    have hv : VI i ≠ 0 := by
      intro e
      rw [e] at hrec
      exact absurd hrec (by decide)
    rw [if_neg Bool.false_ne_true]
    exact (H2 i hl).2 hv
  · rw [if_pos rfl]
    exact (H2 i hl).1

theorem wordS_reps {VI : Nat → Nat} {R : List Nat} {Gs : Array G}
    (H2 : ∀ r < R.length, Reps φ (R.getD r 0) (Gs.getD r 1) ∧
      (VI r ≠ 0 → Reps φ (VI r) (Gs.getD r 1)⁻¹)) :
    ∀ (w : List (Nat × Bool)), (∀ l ∈ w, l.1 < R.length) → recS VI w = true →
      ∀ (acc : Nat) (x : G), Reps φ acc x →
        Reps φ (wordS (mul3 LL HH CM RM) R VI w acc)
          (x * CFSG.RankThree.Native.ONTriple.wordG Gs w)
  | [], _, _, acc, x, h => by
    change Reps φ acc _
    simpa [CFSG.RankThree.Native.ONTriple.wordG] using h
  | (i, b) :: w, hw, hr, acc, x, h => by
    change bAnd(Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (VI i) 0)) true b,
      recS VI w) = true at hr
    rw [bAnd_iff'] at hr
    change Reps φ (strictN (mul3 LL HH CM RM acc (letV R VI (i, b)))
      (fun a => wordS (mul3 LL HH CM RM) R VI w a)) _
    rw [strictN_eq']
    have := wordS_reps H2 w (fun l hl => hw l (List.mem_cons_of_mem _ hl)) hr.2 _ _
      (reps_mul h (letV_reps H2 (hw (i, b) List.mem_cons_self) hr.1))
    have e : CFSG.RankThree.Native.ONTriple.wordG Gs ((i, b) :: w) =
        (if b then Gs.getD i 1 else (Gs.getD i 1)⁻¹) *
          CFSG.RankThree.Native.ONTriple.wordG Gs w := by
      simp only [CFSG.RankThree.Native.ONTriple.wordG, List.map_cons, List.prod_cons]
    rw [e, ← mul_assoc]
    exact this

theorem stepW_inv {VI : Nat → Nat} {R : List Nat} {ok : Bool} {Gs : Array G}
    (H : sopInv φ VI R ok Gs) (w : List (Nat × Bool)) (hw : ∀ l ∈ w, l.1 < R.length) :
    sopInv φ VI (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) (.word w)).1
      (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) (.word w)).2
      (CFSG.RankThree.Native.ONTriple.stepG Gs (.word w)) := by
  simp only [stepS, strictS_eq, CFSG.RankThree.Native.ONTriple.stepG]
  refine sopInv_push H (fun h => ?_) (fun h => ?_)
  · rw [bAnd_iff'] at h
    exact h.1
  · rw [bAnd_iff', bAnd_iff'] at h
    obtain ⟨hok, hrec, hinv⟩ := h
    have hx := wordS_reps (H.2 hok) w hw hrec ONE 1 reps_one
    rw [one_mul] at hx
    exact ⟨hx, invS_sound hinv hx⟩

theorem stepP_inv {VI : Nat → Nat} {R : List Nat} {ok : Bool} {Gs : Array G}
    (H : sopInv φ VI R ok Gs) (e i : Nat) :
    sopInv φ VI (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) (.pow e i)).1
      (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) (.pow e i)).2
      (CFSG.RankThree.Native.ONTriple.stepG Gs (.pow e i)) := by
  simp only [stepS, strictS_eq, CFSG.RankThree.Native.ONTriple.stepG]
  refine sopInv_push H (fun h => ?_) (fun h => ?_)
  · rw [bAnd_iff'] at h
    exact h.1
  · rw [bAnd_iff', bAnd_iff'] at h
    obtain ⟨hok, hi, hinv⟩ := h
    have hx := powS_reps (H.2 hok i (Nat.blt_eq.mp hi)).1 e
    exact ⟨hx, invS_sound hinv hx⟩

theorem runS_inv {VI : Nat → Nat} {fin : List Nat × Bool → Bool} :
    ∀ (prog : List SOp) (R : List Nat) (ok : Bool) (Gs : Array G), sopInv φ VI R ok Gs →
      sopLt R.length prog = true →
      runS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI fin prog (R, ok) = true →
      ∃ st : List Nat × Bool, fin st = true ∧ (st.2 = true →
        st.1.length = R.length + prog.length ∧ ∀ r < st.1.length,
          Reps φ (st.1.getD r 0) ((runG Gs prog).getD r 1) ∧
            (VI r ≠ 0 → Reps φ (VI r) ((runG Gs prog).getD r 1)⁻¹))
  | [], R, ok, Gs, H, _, h => ⟨(R, ok), h, fun hok => ⟨by simp, H.2 hok⟩⟩
  | o :: prog, R, ok, Gs, H, hp, h => by
    have e : runS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI fin (o :: prog) (R, ok) =
        runS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI fin prog
          (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o) := by
      change Prod.rec (motive := fun _ => Bool)
        (fun R ok => runS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI fin prog (R, ok))
        (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o) = _
      obtain ⟨R', ok'⟩ := stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o
      rfl
    rw [e] at h
    have hlen : (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o).1.length =
        R.length + 1 := by
      cases o <;> simp [stepS, strictS_eq]
    have hH : sopInv φ VI (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o).1
        (stepS (mul3 LL HH CM RM) (vld3 LL HH) ONE VI (R, ok) o).2
        (CFSG.RankThree.Native.ONTriple.stepG Gs o) := by
      cases o with
      | word w =>
        simp only [sopLt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hp
        exact stepW_inv H w hp.1
      | pow k i => exact stepP_inv H k i
    have hp' : sopLt (R.length + 1) prog = true := by
      cases o <;> simp only [sopLt, Bool.and_eq_true] at hp <;> exact hp.2
    obtain ⟨st, hst, hst2⟩ := runS_inv prog _ _ _ hH (by rw [hlen]; exact hp') h
    refine ⟨st, hst, fun hok => ?_⟩
    obtain ⟨h1, h2⟩ := hst2 hok
    exact ⟨by rw [h1, hlen, List.length_cons]; omega, h2⟩

theorem sopK_sound {init : List Nat} {VI : Nat → Nat} {fin : List Nat × Bool → Bool}
    {prog : List SOp} {g : Array G} (h : sopK init VI fin prog = true)
    (hprog : sopLt init.length prog = true) (hg : g.size = init.length)
    (hinit : ∀ r < init.length, Reps φ (init.getD r 0) (g.getD r 1)) :
    ∃ st : List Nat × Bool, fin st = true ∧ (st.2 = true →
      st.1.length = init.length + prog.length ∧ ∀ r < st.1.length,
        Reps φ (st.1.getD r 0) ((runG g prog).getD r 1) ∧
          (VI r ≠ 0 → Reps φ (VI r) ((runG g prog).getD r 1)⁻¹)) := by
  simp only [sopK, strictB_eq', bAnd_iff'] at h
  obtain ⟨hinitS, hrun⟩ := h
  exact runS_inv prog init true g ⟨hg.symm, fun _ r hr =>
    ⟨hinit r hr, invS_sound (initS_spec hinitS r hr) (hinit r hr)⟩⟩ hprog hrun

end CFSG.KS.ONC

end
