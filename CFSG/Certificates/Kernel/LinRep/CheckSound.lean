module

public import Certificates.Data.Kernel.LinRep
public import CFSG.Certificates.Kernel.LinRep.Sound
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.LinRepCheck

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.PSL3Four.Native CFSG.KS.BfsReplay

theorem c6_eq_col (x i : Nat) : c6 x i = col x i := rfl

theorem bm_eq_term (v i y : Nat) : bm v i y = term (v.testBit i) y := by
  unfold bm term
  change ((v >>> i) &&& 1) * y = _
  have e : v.testBit i = decide ((v >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [Nat.and_one_is_mod, e]
  rcases Nat.mod_two_eq_zero_or_one (v >>> i) with h | h <;> simp [h]

theorem appW_eq_ev (a v : Nat) : appW a v = ev (col a) v := by
  unfold appW ev
  simp only [bm_eq_term]
  rfl

theorem col_eq (x i : Nat) : col x i = x / 2 ^ (6 * i) % 64 := by
  have h63 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  unfold col
  change (x >>> (6 * i)) &&& 63 = _
  rw [h63, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem col_w6 {x0 x1 x2 x3 x4 x5 : Nat} (h0 : x0 < 64) (h1 : x1 < 64) (h2 : x2 < 64)
    (h3 : x3 < 64) (h4 : x4 < 64) (h5 : x5 < 64) :
    col (w6 x0 x1 x2 x3 x4 x5) 0 = x0 ∧ col (w6 x0 x1 x2 x3 x4 x5) 1 = x1 ∧
      col (w6 x0 x1 x2 x3 x4 x5) 2 = x2 ∧ col (w6 x0 x1 x2 x3 x4 x5) 3 = x3 ∧
      col (w6 x0 x1 x2 x3 x4 x5) 4 = x4 ∧ col (w6 x0 x1 x2 x3 x4 x5) 5 = x5 := by
  have e : w6 x0 x1 x2 x3 x4 x5 =
      x0 + 64 * (x1 + 64 * (x2 + 64 * (x3 + 64 * (x4 + 64 * x5)))) := rfl
  simp only [col_eq, e]
  norm_num
  omega

@[expose] def tsum6 (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun v acc => Nat.add acc (Nat.shiftLeft (f v) (Nat.mul 6 v))) n

theorem tabW_eq (a : Nat) : tabW a = tsum6 (appW a) 64 := rfl

theorem tsum6_succ (f : Nat → Nat) (n : Nat) : tsum6 f (n + 1) = tsum6 f n + f n * 2 ^ (6 * n) := by
  unfold tsum6
  change Nat.add _ ((f n) <<< (6 * n)) = _
  rw [Nat.shiftLeft_eq]
  rfl

theorem tsum6_lt (f : Nat → Nat) (hf : ∀ v, f v < 64) (n : Nat) : tsum6 f n < 2 ^ (6 * n) := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have hp : 2 ^ (6 * (n + 1)) = 64 * 2 ^ (6 * n) := by
      rw [Nat.mul_succ, pow_add]
      ring
    rw [tsum6_succ, hp]
    have := hf n
    nlinarith

theorem tsum6_get (f : Nat → Nat) (hf : ∀ v, f v < 64) (n : Nat) :
    ∀ v < n, tsum6 f n / 2 ^ (6 * v) % 64 = f v := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    rw [tsum6_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hlt | rfl
    · have hn : 6 * n = 6 * v + 6 + 6 * (n - v - 1) := by omega
      have hk : f n * 2 ^ (6 * n) = 64 * (f n * 2 ^ (6 * (n - v - 1))) * 2 ^ (6 * v) := by
        rw [hn, pow_add, pow_add]
        ring
      rw [hk, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih v hlt
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (tsum6_lt f hf v), zero_add,
        Nat.mod_eq_of_lt (hf v)]

theorem appW_lt (a v : Nat) : appW a v < 64 := by
  rw [appW_eq_ev]
  exact ev_lt (fun i _ => col_lt a i) v

theorem c6_tabW (a : Nat) {v : Nat} (hv : v < 64) : c6 (tabW a) v = appW a v := by
  rw [c6_eq_col, col_eq, tabW_eq]
  exact tsum6_get (appW a) (appW_lt a) 64 v hv

theorem col_mulT_tabW (a w : Nat) {i : Nat} (hi : i < 6) :
    col (mulT (tabW a) w) i = ev (col a) (col w i) := by
  have hc : ∀ k, c6 (tabW a) (c6 w k) = appW a (c6 w k) := fun k => c6_tabW a (col_lt w k)
  have hm : mulT (tabW a) w = w6 (appW a (c6 w 0)) (appW a (c6 w 1)) (appW a (c6 w 2))
      (appW a (c6 w 3)) (appW a (c6 w 4)) (appW a (c6 w 5)) := by
    unfold mulT
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := col_w6 (appW_lt a (c6 w 0)) (appW_lt a (c6 w 1))
    (appW_lt a (c6 w 2)) (appW_lt a (c6 w 3)) (appW_lt a (c6 w 4)) (appW_lt a (c6 w 5))
  rw [hm]
  rcases six_cases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e0, appW_eq_ev]
    rfl
  · rw [e1, appW_eq_ev]
    rfl
  · rw [e2, appW_eq_ev]
    rfl
  · rw [e3, appW_eq_ev]
    rfl
  · rw [e4, appW_eq_ev]
    rfl
  · rw [e5, appW_eq_ev]
    rfl

theorem col_idW : ∀ i < 6, col idW i = 2 ^ i := by decide

theorem key_lt (s : Nat) : key s < 2 ^ 36 := by
  unfold key
  change s &&& (2 ^ 36 - 1) < 2 ^ 36
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem bIf_true_or {c e : Bool} (h : bIf(c, true, e) = true) : c = true ∨ e = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

theorem lexB_iff (a b c d : Nat) : lexB a b c d = true ↔ LexLt a b c d := by
  have e1 : Nat.blt a c = decide (a < c) := Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])
  have e2 : Nat.beq a c = decide (a = c) := Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])
  have e3 : Nat.blt b d = decide (b < d) := Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])
  unfold lexB LexLt
  rw [e1, e2, e3]
  by_cases h1 : a < c <;> by_cases h2 : a = c <;> by_cases h3 : b < d <;> simp [h1, h2, h3] <;> omega

theorem tabsK_sound : ∀ {GW GT : List Nat}, tabsK GW GT = true →
    GW.length = GT.length ∧ ∀ j < GT.length, nthN GT j = tabW (nthN GW j)
  | [], [], _ => ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | [], t :: T, h => by
    have e : tabsK [] (t :: T) = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | a :: GW, [], h => by
    have e : tabsK (a :: GW) [] = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | a :: GW, t :: T, h => by
    delta tabsK at h
    dsimp only at h
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨ih1, ih2⟩ := tabsK_sound h.2
    refine ⟨by simp [ih1], fun j hj => ?_⟩
    cases j with
    | zero => exact h.1.symm
    | succ j => exact ih2 j (by simpa using hj)

theorem incK_cons (E : Nat → Nat) (cnt i : Nat) (L : List Nat) (prev c : Nat) :
    incK E cnt (i :: L) prev c = bAnd(Nat.blt i cnt, strictB (key (slot E i)) fun x =>
      bAnd(Nat.blt prev x, strictB (Nat.succ c) (incK E cnt L x))) := rfl

theorem incK_sound {E : Nat → Nat} {cnt : Nat} : ∀ (L : List Nat) (prev c : Nat),
    incK E cnt L prev c = true →
      (∀ i ∈ L, i < cnt ∧ prev < key (slot E i)) ∧
        L.Pairwise (fun a b => key (slot E a) < key (slot E b)) ∧ c + L.length = cnt
  | [], prev, c, h => by
    have e : incK E cnt [] prev c = Nat.beq c cnt := rfl
    rw [e, Nat.beq_eq] at h
    exact ⟨by simp, List.Pairwise.nil, by simpa using h⟩
  | i :: L, prev, c, h => by
    rw [incK_cons] at h
    simp only [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := incK_sound L _ _ h3
    refine ⟨fun j hj => ?_, List.Pairwise.cons (fun b hb => (ih1 b hb).2) ih2, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨h1, h2⟩
      · exact ⟨(ih1 j hj).1, Nat.lt_trans h2 (ih1 j hj).2⟩
    · simp only [List.length_cons]
      omega

theorem pairwise_ne_inj {E : Nat → Nat} : ∀ L : List Nat,
    L.Pairwise (fun a b => key (slot E a) ≠ key (slot E b)) →
      ∀ a ∈ L, ∀ b ∈ L, key (slot E a) = key (slot E b) → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: L, hp, a, ha, b, hb, e => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha'] at e
      exact absurd e (hp.1 b hb')
    · rw [hb'] at e
      exact absurd e.symm (hp.1 a ha')
    · exact pairwise_ne_inj L hp.2 a ha' b hb' e

theorem ordK_inj {E : Nat → Nat} {cnt : Nat} {ORD : List Nat} (h : ordK E cnt ORD = true) :
    ∀ a < cnt, ∀ b < cnt, key (slot E a) = key (slot E b) → a = b := by
  obtain ⟨h1, h2, h3⟩ := incK_sound ORD 0 0 h
  have hne : ORD.Pairwise (fun a b => key (slot E a) ≠ key (slot E b)) :=
    h2.imp fun hab => Nat.ne_of_lt hab
  have hnd : ORD.Nodup :=
    List.Pairwise.imp (fun {a b} (hk : key (slot E a) ≠ key (slot E b)) (hab : a = b) =>
      hk (by rw [hab])) hne
  have hsub : ORD ⊆ List.range cnt := fun x hx => List.mem_range.2 (h1 x hx).1
  have hp := (hnd.subperm hsub).perm_of_length_le (by rw [List.length_range]; omega)
  have hmem : ∀ a < cnt, a ∈ ORD := fun a ha => hp.mem_iff.2 (List.mem_range.2 ha)
  intro a ha b hb e
  exact pairwise_ne_inj ORD hne a (hmem a ha) b (hmem b hb) e

theorem closeJ_gen {E : Nat → Nat} {cnt w h r : Nat} (F : List Nat → Nat → Bool)
    (hF : ∀ G GS j, F (G :: GS) j = strictB (pos16 r j) fun p => strictB (slot E p) fun s =>
      bAnd(Nat.blt p cnt, bAnd(Nat.beq (mulT G w) (key s),
        bAnd(bIf(Nat.beq p 0, true, nB (lexB h j (spar s) (slab s))), strictB (Nat.succ j) (F GS))))) :
    ∀ (GS : List Nat) (j0 : Nat), F GS j0 = true → ∀ t < GS.length,
      pos16 r (j0 + t) < cnt ∧ mulT (nthN GS t) w = key (slot E (pos16 r (j0 + t))) ∧
      (pos16 r (j0 + t) = 0 ∨
        ¬ LexLt h (j0 + t) (spar (slot E (pos16 r (j0 + t)))) (slab (slot E (pos16 r (j0 + t))))) := by
  intro GS
  induction GS with
  | nil => exact fun _ _ t ht => absurd ht (Nat.not_lt_zero _)
  | cons G GS ih =>
    intro j0 hc t ht
    rw [hF] at hc
    simp only [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases t with
    | zero =>
      simp only [Nat.add_zero]
      refine ⟨h1, h2, ?_⟩
      by_cases hp : pos16 r j0 = 0
      · exact Or.inl hp
      · right
        intro hl
        rcases bIf_true_or h3 with h3 | h3
        · exact hp (Nat.eq_of_beq_eq_true h3)
        · rw [(lexB_iff _ _ _ _).2 hl] at h3
          exact Bool.false_ne_true h3
    | succ t =>
      have e := ih (Nat.succ j0) h4 t (by simpa using ht)
      rw [show j0 + (t + 1) = Nat.succ j0 + t by omega]
      exact e

theorem closeJ_sound {E : Nat → Nat} {cnt w h r : Nat} {GS : List Nat}
    (hc : closeJ E cnt w h r GS = true) : ∀ j < GS.length,
      pos16 r j < cnt ∧ mulT (nthN GS j) w = key (slot E (pos16 r j)) ∧
      (pos16 r j = 0 ∨ ¬ LexLt h j (spar (slot E (pos16 r j))) (slab (slot E (pos16 r j)))) := by
  intro j hj
  have e := closeJ_gen (E := E) (cnt := cnt) (w := w) (h := h) (r := r)
    (fun GS => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun G _ ih j => strictB (pos16 r j) fun p => strictB (slot E p) fun s =>
        bAnd(Nat.blt p cnt, bAnd(Nat.beq (mulT G w) (key s),
          bAnd(bIf(Nat.beq p 0, true, nB (lexB h j (spar s) (slab s))), strictB (Nat.succ j) ih))))
      GS) (fun _ _ _ => rfl) GS 0 hc j hj
  simp only [Nat.zero_add] at e
  exact e

theorem rec_of_checks {E R : Nat → Nat} {GW GT ORD : List Nat} {cnt k : Nat}
    (hk : GT.length = k) (hh : headK E GW GT cnt = true) (ho : ordK E cnt ORD = true)
    (hr : ∀ h < cnt, rowK E GT k cnt (row (R (h / 1024)) (h % 1024)) h = true) :
    GW.length = k ∧ (∀ j < k, nthN GT j = tabW (nthN GW j)) ∧ 0 < cnt ∧
    (∀ i < 6, col (key (slot E 0)) i = 2 ^ i) ∧ spar (slot E 0) = 0 ∧ slab (slot E 0) = 0 ∧
    (∀ a < cnt, ∀ b < cnt, key (slot E a) = key (slot E b) → a = b) ∧
    (∀ i, 0 < i → i < cnt → spar (slot E i) < i ∧ slab (slot E i) < k ∧
      key (slot E i) = mulT (nthN GT (slab (slot E i))) (key (slot E (spar (slot E i))))) ∧
    (∀ i, 0 < i → i + 1 < cnt → LexLt (spar (slot E i)) (slab (slot E i))
      (spar (slot E (i + 1))) (slab (slot E (i + 1)))) ∧
    (∀ h < cnt, ∀ j < k, pos16 (row (R (h / 1024)) (h % 1024)) j < cnt ∧
      mulT (nthN GT j) (key (slot E h)) = key (slot E (pos16 (row (R (h / 1024)) (h % 1024)) j)) ∧
      (pos16 (row (R (h / 1024)) (h % 1024)) j = 0 ∨
        ¬ LexLt h j (spar (slot E (pos16 (row (R (h / 1024)) (h % 1024)) j)))
          (slab (slot E (pos16 (row (R (h / 1024)) (h % 1024)) j))))) := by
  unfold headK at hh
  simp only [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hh
  obtain ⟨hc0, hid, hp0, hl0, ht⟩ := hh
  obtain ⟨hlen, hnth⟩ := tabsK_sound ht
  have hrow : ∀ h < cnt, (h ≠ 0 → spar (slot E h) < h ∧ slab (slot E h) < k ∧
        key (slot E h) = mulT (nthN GT (slab (slot E h))) (key (slot E (spar (slot E h))))) ∧
      (h ≠ 0 → h + 1 < cnt → LexLt (spar (slot E h)) (slab (slot E h))
        (spar (slot E (h + 1))) (slab (slot E (h + 1)))) ∧
      closeJ E cnt (key (slot E h)) h (row (R (h / 1024)) (h % 1024)) GT = true := by
    intro h hh
    have e := hr h hh
    unfold rowK at e
    simp only [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at e
    obtain ⟨e1, e2, e3⟩ := e
    refine ⟨fun h0 => ?_, fun h0 h1 => ?_, e3⟩
    · rcases bIf_true_or e1 with e1 | e1
      · exact absurd (Nat.eq_of_beq_eq_true e1) h0
      · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e1
        exact e1
    · rcases bIf_true_or e2 with e2 | e2
      · exact absurd (Nat.eq_of_beq_eq_true e2) h0
      · have hb : Nat.blt (Nat.succ h) cnt = true := by
          rw [Nat.blt_eq]
          exact h1
        rw [hb] at e2
        exact (lexB_iff _ _ _ _).1 e2
  refine ⟨hlen.trans hk, fun j hj => hnth j (by rw [hk]; exact hj), hc0, ?_, hp0, hl0,
    ordK_inj ho, fun i hi0 hi => (hrow i hi).1 (by omega),
    fun i hi0 hi => (hrow i (by omega)).2.1 (by omega) hi, ?_⟩
  · intro i hi
    rw [hid]
    exact col_idW i hi
  · intro h hh j hj
    exact closeJ_sound (hrow h hh).2.2 j (by rw [hk]; exact hj)

end CFSG.KC.LinRepCheck

end
