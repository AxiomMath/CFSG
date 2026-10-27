module

public import CFSG.Certificates.Kernel.P0RankK.VisFark
public import CFSG.Certificates.Kernel.P0RankK.VisFix
public import Mathlib.Algebra.Order.Ring.Nat

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb

theorem none_ne_some {l : List Cand} (h : (none : Option (List Cand)) = some l) : False := by
  cases h

theorem entV_sound {C : Ctx} {ds : List ℕ} {a M : ℕ} {e : YEnt} {cands : List Cand}
    {l : List Cand} (h : entV C ds a M e cands = some l) (h1 : 16384 < a * e.2.2)
    (h2 : 16384 < a * pc (Nat.land M e.2.1)) :
    ∃ c ∈ cands, candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1)
      (pc (Nat.land M e.2.1)) c = true := by
  unfold entV at h
  rw [ble_false h1, cond_false] at h
  simp only at h
  rw [ble_false h2, cond_false] at h
  cases cands with
  | nil => exact (none_ne_some h).elim
  | cons c rest =>
    refine ⟨c, List.mem_cons_self, ?_⟩
    change (bif candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1) (pc (Nat.land M e.2.1)) c
      then some rest else none) = some l at h
    cases hc : candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1) (pc (Nat.land M e.2.1)) c
    · rw [hc] at h
      exact (none_ne_some h).elim
    · rfl

theorem entV_sub {C : Ctx} {ds : List ℕ} {a M : ℕ} {e : YEnt} {cands l : List Cand}
    (h : entV C ds a M e cands = some l) : ∀ x ∈ l, x ∈ cands := by
  unfold entV at h
  cases h1 : Nat.ble (a * e.2.2) 16384
  · rw [h1, cond_false] at h
    simp only at h
    cases h2 : Nat.ble (a * pc (Nat.land M e.2.1)) 16384
    · rw [h2, cond_false] at h
      cases cands with
      | nil => exact (none_ne_some h).elim
      | cons c rest =>
        change (bif candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1)
          (pc (Nat.land M e.2.1)) c then some rest else none) = some l at h
        cases hc : candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1)
          (pc (Nat.land M e.2.1)) c
        · rw [hc] at h
          exact (none_ne_some h).elim
        · rw [hc, cond_true, Option.some.injEq] at h
          subst h
          exact fun x hx => List.mem_cons_of_mem _ hx
    · rw [h2, cond_true, Option.some.injEq] at h
      subst h
      exact fun x hx => hx
  · rw [h1, cond_true, Option.some.injEq] at h
    subst h
    exact fun x hx => hx

theorem entsV_cons (C : Ctx) (ds : List ℕ) (a M : ℕ) (e : YEnt) (es : List YEnt)
    (cands : List Cand) :
    entsV C ds a M (e :: es) cands =
      Option.rec (motive := fun _ => Option (List Cand)) none (fun cs => entsV C ds a M es cs)
        (entV C ds a M e cands) := rfl

theorem entsV_sound {C : Ctx} {ds : List ℕ} {a M : ℕ} :
    ∀ (es : List YEnt) (cands : List Cand) (l : List Cand), entsV C ds a M es cands = some l →
      ∀ e ∈ es, 16384 < a * e.2.2 → 16384 < a * pc (Nat.land M e.2.1) →
        ∃ c ∈ cands, candOK C.AT C.BT C.BC C.FK C.FC ds a (Nat.land M e.2.1)
          (pc (Nat.land M e.2.1)) c = true
  | [], _, _, _, _, he, _, _ => absurd he (by simp)
  | e₀ :: es, cands, l, h, e, he, h1, h2 => by
    rw [entsV_cons] at h
    cases h0 : entV C ds a M e₀ cands with
    | none =>
      rw [h0] at h
      exact (none_ne_some h).elim
    | some l₀ =>
      rw [h0] at h
      rcases List.mem_cons.1 he with rfl | he'
      · exact entV_sound h0 h1 h2
      · obtain ⟨c, hc, hok⟩ := entsV_sound es l₀ l h e he' h1 h2
        exact ⟨c, entV_sub h0 c hc, hok⟩

theorem entsV_sub {C : Ctx} {ds : List ℕ} {a M : ℕ} :
    ∀ (es : List YEnt) (cands l : List Cand), entsV C ds a M es cands = some l →
      ∀ x ∈ l, x ∈ cands
  | [], cands, l, h => by
    change some cands = some l at h
    rw [Option.some.injEq] at h
    subst h
    exact fun x hx => hx
  | e₀ :: es, cands, l, h => by
    rw [entsV_cons] at h
    cases h0 : entV C ds a M e₀ cands with
    | none =>
      rw [h0] at h
      exact (none_ne_some h).elim
    | some l₀ =>
      rw [h0] at h
      exact fun x hx => entV_sub h0 x (entsV_sub es l₀ l h x hx)

theorem grpsV_sound {C : Ctx} {ds : List ℕ} {d M nM : ℕ} :
    ∀ (gs : List (List YEnt)) (s : ℕ) (cands l : List Cand), grpsV C ds d M nM s gs cands = some l →
      ∀ t < gs.length, ∀ e ∈ gs.getD t [], 16384 < 2 ^ (d + 4 + (s + t)) * nM →
        16384 < 2 ^ (d + 4 + (s + t)) * e.2.2 →
        16384 < 2 ^ (d + 4 + (s + t)) * pc (Nat.land M e.2.1) →
        ∃ c ∈ cands, candOK C.AT C.BT C.BC C.FK C.FC ds (2 ^ (d + 4 + (s + t)))
          (Nat.land M e.2.1) (pc (Nat.land M e.2.1)) c = true
  | [], _, _, _, _, _, ht, _, _, _, _, _ => absurd ht (by simp)
  | g :: gs, s, cands, l, h, t, ht, e, he, h0, h1, h2 => by
    rw [grpsV] at h
    cases t with
    | zero =>
      have h0' : 16384 < 2 ^ (d + 4 + s) * nM := h0
      have h1' : 16384 < 2 ^ (d + 4 + s) * e.2.2 := h1
      have h2' : 16384 < 2 ^ (d + 4 + s) * pc (Nat.land M e.2.1) := h2
      rw [ble_false h0', cond_false] at h
      cases hE : entsV C ds (2 ^ (d + 4 + s)) M g cands with
      | none =>
        rw [hE] at h
        exact (none_ne_some h).elim
      | some l₀ => exact entsV_sound g cands l₀ hE e (by simpa using he) h1' h2'
    | succ t =>
      have hs : s + (t + 1) = s + 1 + t := by omega
      rw [hs] at h0 h1 h2 ⊢
      have ht' : t < gs.length := by simpa using ht
      have he' : e ∈ gs.getD t [] := by simpa using he
      cases hb : Nat.ble (2 ^ (d + 4 + s) * nM) 16384
      · rw [hb, cond_false] at h
        cases hE : entsV C ds (2 ^ (d + 4 + s)) M g cands with
        | none =>
          rw [hE] at h
          exact (none_ne_some h).elim
        | some l₀ =>
          rw [hE] at h
          obtain ⟨c, hc, hok⟩ := grpsV_sound gs (s + 1) l₀ l h t ht' e he' h0 h1 h2
          exact ⟨c, entsV_sub g cands l₀ hE c hc, hok⟩
      · rw [hb, cond_true] at h
        exact grpsV_sound gs (s + 1) cands l h t ht' e he' h0 h1 h2

theorem visitOK_sound {C : Ctx} {RT FA : ℕ} {YG : List (List YEnt)} {r : ℕ} {row : VRow}
    (h : visitOK C RT FA YG r row = true) :
    labsOK C.AT RT (sbasis (slot RT r)) row.1 = true ∧
      ∀ s < YG.length, ∀ e ∈ YG.getD s [],
        16384 < 2 ^ (Nat.shiftRight (slot RT r) 80 + 4 + s) * pc (fixOf FA row.1) →
        16384 < 2 ^ (Nat.shiftRight (slot RT r) 80 + 4 + s) * e.2.2 →
        16384 < 2 ^ (Nat.shiftRight (slot RT r) 80 + 4 + s) *
          pc (Nat.land (fixOf FA row.1) e.2.1) →
        ∃ c ∈ row.2, candOK C.AT C.BT C.BC C.FK C.FC (sbasis (slot RT r))
          (2 ^ (Nat.shiftRight (slot RT r) 80 + 4 + s)) (Nat.land (fixOf FA row.1) e.2.1)
          (pc (Nat.land (fixOf FA row.1) e.2.1)) c = true := by
  rw [visitOK] at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro s hs e he h0 h1 h2
  cases hg : grpsV C (sbasis (slot RT r)) (Nat.shiftRight (slot RT r) 80) (fixOf FA row.1)
      (pc (fixOf FA row.1)) 0 YG row.2 with
  | none =>
    have h2' := h.2
    rw [hg] at h2'
    exact Bool.noConfusion (h2' : false = true)
  | some l =>
    have := grpsV_sound YG 0 row.2 l hg s hs e he (by simpa using h0) (by simpa using h1)
      (by simpa using h2)
    simpa using this

theorem testBit_foldl_land (g : Nat × Nat → ℕ) (κ : ℕ) : ∀ (labs : List (Nat × Nat)) (m : ℕ),
    (labs.foldl (fun m l => Nat.land m (g l)) m).testBit κ = true ↔
      m.testBit κ = true ∧ ∀ l ∈ labs, (g l).testBit κ = true
  | [], m => by simp
  | l :: labs, m => by
    rw [List.foldl_cons, testBit_foldl_land g κ labs]
    change (m &&& g l).testBit κ = true ∧ _ ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem testBit_fixOf (FA : ℕ) (labs : List (Nat × Nat)) (κ : ℕ) :
    (fixOf FA labs).testBit κ = true ↔
      κ < 1024 ∧ ∀ l ∈ labs, (fld FA (1024 * l.1) m1024).testBit κ = true := by
  rw [fixOf, testBit_foldl_land, testBit_m1024, decide_eq_true_iff]

theorem fix_act_iff {A : ℕ → ℕ → ℕ} (h0 : ∀ x < 2 ^ 16, A 0 x = x)
    (hc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16, A κ (A μ x) = A (κ ^^^ μ) x)
    (hlt : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, A κ x < 2 ^ 16) {κ μ v : ℕ} (hκ : κ < 2 ^ 10)
    (hμ : μ < 2 ^ 10) (hv : v < 2 ^ 16) : A κ (A μ v) = A μ v ↔ A κ v = v := by
  have hsw : A κ (A μ v) = A μ (A κ v) := by
    rw [hc κ hκ μ hμ v hv, hc μ hμ κ hκ v hv, Nat.xor_comm]
  have hinv : ∀ y < 2 ^ 16, A μ (A μ y) = y := fun y hy => by
    rw [hc μ hμ μ hμ y hy, Nat.xor_self, h0 y hy]
  rw [hsw]
  constructor
  · intro h
    have := congrArg (A μ) h
    rwa [hinv _ (hlt κ hκ v hv), hinv v hv] at this
  · intro h
    rw [h]

theorem labsOK_fix {AT RT : ℕ} (h0 : ∀ x < 2 ^ 16, aAct AT 0 x = x)
    (hc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ (aAct AT μ x) = aAct AT (κ ^^^ μ) x)
    (hlt : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x < 2 ^ 16) {κ : ℕ} (hκ : κ < 2 ^ 10) :
    ∀ (bs : List ℕ) (labs : List (Nat × Nat)), labsOK AT RT bs labs = true →
      ((∀ l ∈ labs, l.1 < 68 ∧ aAct AT κ (vO RT l.1) = vO RT l.1) ↔ ∀ b ∈ bs, aAct AT κ b = b)
  | [], [], _ => by simp
  | b :: bs, l :: labs, h => by
    rw [labsOK] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨h68, hμ⟩, hb⟩, hrest⟩ := h
    have ih := labsOK_fix h0 hc hlt hκ bs labs hrest
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [ih, ← hb, fix_act_iff h0 hc hlt hκ hμ (vO_lt RT l.1)]
    tauto
  | [], _ :: _, h => by simp [labsOK] at h
  | _ :: _, [], h => by simp [labsOK] at h

theorem testBit_fixOf_fix {AT RT FA : ℕ} {bs : List ℕ} {labs : List (Nat × Nat)}
    (hfa : ∀ o < 68, faOK FA AT RT o = true) (hlabs : labsOK AT RT bs labs = true)
    (h0 : ∀ x < 2 ^ 16, aAct AT 0 x = x)
    (hc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ (aAct AT μ x) = aAct AT (κ ^^^ μ) x)
    (hlt : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x < 2 ^ 16) (κ : ℕ) :
    (fixOf FA labs).testBit κ = true ↔ κ < 1024 ∧ ∀ b ∈ bs, aAct AT κ b = b := by
  have h68 : ∀ l ∈ labs, l.1 < 68 := by
    intro l hl
    have key : ∀ (bs : List ℕ) (labs : List (Nat × Nat)), labsOK AT RT bs labs = true →
        ∀ l ∈ labs, l.1 < 68 := by
      intro bs labs
      induction labs generalizing bs with
      | nil => simp
      | cons l labs ih =>
        cases bs with
        | nil => simp [labsOK]
        | cons b bs =>
          intro h l' hl'
          rw [labsOK] at h
          simp only [Bool.and_eq_true, Nat.blt_eq] at h
          rcases List.mem_cons.1 hl' with rfl | hl''
          · exact h.1.1.1
          · exact ih bs h.2 l' hl''
    exact key bs labs hlabs l hl
  rw [testBit_fixOf]
  constructor
  · rintro ⟨hκ, hall⟩
    refine ⟨hκ, (labsOK_fix h0 hc hlt hκ bs labs hlabs).1 fun l hl => ?_⟩
    exact ⟨h68 l hl, ((faOK_iff (hfa _ (h68 l hl)) κ).1 (hall l hl)).2⟩
  · rintro ⟨hκ, hall⟩
    refine ⟨hκ, fun l hl => (faOK_iff (hfa _ (h68 l hl)) κ).2 ⟨hκ, ?_⟩⟩
    exact (((labsOK_fix h0 hc hlt hκ bs labs hlabs).2 hall) l hl).2

theorem visitsOK_spec {C : Ctx} {RT FA : ℕ} {YG : List (List YEnt)} :
    ∀ (rows : List VRow) (r₀ : ℕ), visitsOK C RT FA YG r₀ rows = true →
      ∀ t (ht : t < rows.length), visitOK C RT FA YG (r₀ + t) rows[t] = true
  | [], _, _, t, ht => absurd ht (by simp)
  | row :: rows, r₀, h, t, ht => by
    rw [visitsOK, Bool.and_eq_true] at h
    cases t with
    | zero => exact h.1
    | succ t =>
      have := visitsOK_spec rows (r₀ + 1) h.2 t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

end CFSG.KC.P0Vis

end
