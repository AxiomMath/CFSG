module

public import Certificates.Data.Kernel.Foote82StabK
public import Certificates.Data.Foote82OmegaEightMax
public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.KC.StabT919

open CFSG.KC.Census (at' pset unpackP canon1)
open CFSG.CGT.Foote82.OmegaEight CFSG.EvenSmallLie.OmegaEightMinus

theorem foldl_ok {α τ : Type} {G : τ → α → τ} {ok : τ → Bool}
    (hmono : ∀ t a, ok (G t a) = true → ok t = true) :
    ∀ (l : List α) (t : τ), ok (l.foldl G t) = true → ok t = true
  | [], _, h => h
  | a :: l, t, h => hmono t a (foldl_ok hmono l (G t a) h)

theorem foldl_pres {α τ : Type} {G : τ → α → τ} {ok : τ → Bool} {I : τ → Prop}
    (hmono : ∀ t a, ok (G t a) = true → ok t = true) :
    ∀ (l : List α), (∀ a ∈ l, ∀ t, I t → ok (G t a) = true → I (G t a)) →
      ∀ t, I t → ok (l.foldl G t) = true → I (l.foldl G t)
  | [], _, _, hI, _ => hI
  | a :: l, hp, t, hI, hok =>
    foldl_pres hmono l (fun b hb => hp b (List.mem_cons_of_mem a hb)) (G t a)
      (hp a List.mem_cons_self t hI (foldl_ok hmono l (G t a) hok)) hok

theorem foldl_eq {α τ β : Type} {G : τ → α → τ} (f : τ → β) (hf : ∀ t a, f (G t a) = f t) :
    ∀ (l : List α) (t : τ), f (l.foldl G t) = f t
  | [], _ => rfl
  | a :: l, t => (foldl_eq f hf l (G t a)).trans (hf t a)

theorem forIn_eq {α σ τ : Type} {body : α → σ → Id (ForInStep σ)} {G : τ → α → τ}
    {dec : τ → σ} {ok : τ → Bool} {I : τ → Prop}
    (hmono : ∀ t a, ok (G t a) = true → ok t = true) :
    ∀ (l : List α), (∀ a ∈ l, ∀ t, I t → ok (G t a) = true → I (G t a)) →
      (∀ a ∈ l, ∀ t, I t → ok (G t a) = true →
        body a (dec t) = pure (ForInStep.yield (dec (G t a)))) →
      ∀ t, I t → ok (l.foldl G t) = true → ∀ s, s = dec t →
        forIn l s body = pure (dec (l.foldl G t))
  | [], _, _, t, _, _, s, hs => by subst hs; rfl
  | a :: l, hp, hs, t, hI, hok, s, hst => by
    subst hst
    have hok1 : ok (G t a) = true := foldl_ok hmono l (G t a) hok
    have e := forIn_eq hmono l (fun b hb => hp b (List.mem_cons_of_mem a hb))
      (fun b hb => hs b (List.mem_cons_of_mem a hb)) (G t a)
      (hp a List.mem_cons_self t hI hok1) hok _ rfl
    rw [List.forIn_cons, hs a List.mem_cons_self t hI hok1]
    exact e

@[expose] def Inv (t : St) : Prop :=
  canon1 136 8 t.P = true ∧ canon1 136 8 t.L = true ∧ canon1 136 16 t.D = true ∧
    canon1 136 8 t.C = true ∧ canon1 136 8 t.Q = true

theorem dec_get {w P : Nat} (h : canon1 136 w P = true) (x : Nat) : (dec w P)[x]! = at' w P x :=
  CFSG.KC.Census.SP.unpackP_get_canon h x

theorem dec_set {w P y v : Nat} (h : canon1 136 w P = true) (hy : y < 136) (hv : v < 2 ^ w) :
    (dec w P).set! y v = dec w (pset w P y v) :=
  (CFSG.KC.Census.SP.unpackP_pset h hy hv).symm

theorem canon_set {w P y v : Nat} (h : canon1 136 w P = true) (hy : y < 136) (hv : v < 2 ^ w) :
    canon1 136 w (pset w P y v) = true :=
  CFSG.KC.Census.SP.canon_pset h hy hv

theorem decQ_size (Q n : Nat) : (decQ Q n).size = n := by simp [decQ]

theorem decQ_get {Q n h : Nat} (hh : h < n) : (decQ Q n)[h]! = at' 8 Q h := by
  rw [getElem!_pos _ _ (by rw [decQ_size]; exact hh)]
  simp [decQ]

theorem decQ_push {Q n y : Nat} (hy : y < 2 ^ 8) : (decQ Q n).push y = decQ (pset 8 Q n y) (n + 1) := by
  apply Array.ext
  · simp [decQ]
  · intro i h1 h2
    simp only [decQ, Array.getElem_push, Array.size_ofFn, Array.getElem_ofFn,
      CFSG.KC.Census.at'_pset hy]
    by_cases hi : i < n
    · rw [dif_pos hi, if_neg (by omega)]
    · have : i = n := by simp [decQ] at h1; omega
      rw [dif_neg hi, if_pos this]

theorem decQ_one {r : Nat} (hr : r < 2 ^ 8) : #[r] = decQ (pset 8 0 0 r) 1 := by
  apply Array.ext
  · simp [decQ]
  · intro i h1 h2
    have : i = 0 := by simpa using h1
    subst this
    simp [decQ, CFSG.KC.Census.at'_pset hr]

theorem lt8 {y : Nat} (h : y < 256) : y < 2 ^ 8 := by norm_num; exact h

variable {G : Nat → Nat → Nat}

theorem innerK_mono (c x : Nat) (t : St) (l : Nat) : (innerK G c x t l).ok = true → t.ok = true := by
  unfold innerK
  dsimp only
  cases (G l x < 136 && G l x != 0 && at' 8 t.C (G l x) == 0)
  · exact id
  · intro h
    simp only [cond_true, Bool.and_eq_true] at h
    exact h.1.1.1

theorem innerK_h (c x : Nat) (t : St) (l : Nat) : (innerK G c x t l).h = t.h := by
  unfold innerK
  dsimp only
  cases (G l x < 136 && G l x != 0 && at' 8 t.C (G l x) == 0) <;> rfl

theorem innerK_R (c x : Nat) (t : St) (l : Nat) : (innerK G c x t l).R = t.R := by
  unfold innerK
  dsimp only
  cases (G l x < 136 && G l x != 0 && at' 8 t.C (G l x) == 0) <;> rfl

theorem innerK_pres {c x : Nat} (hc : c < 2 ^ 8) {l : Nat} (hl : l < 2 ^ 8) {t : St} (hI : Inv t)
    (hok : (innerK G c x t l).ok = true) : Inv (innerK G c x t l) := by
  unfold innerK at hok ⊢
  dsimp only at hok ⊢
  cases hb : (G l x < 136 && G l x != 0 && at' 8 t.C (G l x) == 0)
  · exact hI
  · rw [hb] at hok
    simp only [cond_true, Bool.and_eq_true, decide_eq_true_eq] at hok hb
    obtain ⟨⟨⟨-, hx⟩, hd⟩, hn⟩ := hok
    have hy : G l x < 136 := hb.1.1
    exact ⟨canon_set hI.1 hy (lt8 hx), canon_set hI.2.1 hy hl,
      canon_set hI.2.2.1 hy (by norm_num; omega), canon_set hI.2.2.2.1 hy hc,
      canon_set hI.2.2.2.2 hn (lt8 (by omega))⟩

theorem queueK_mono (c : Nat) (t : St) (a : Nat) : (queueK G c t a).ok = true → t.ok = true := by
  unfold queueK
  intro h
  cases hh : decide (t.h < t.n)
  · rw [hh, cond_false] at h
    exact h
  · rw [hh, cond_true] at h
    exact foldl_ok (G := innerK G c (at' 8 t.Q t.h)) (fun t l => innerK_mono c _ t l)
      (List.range' 0 16) ⟨t.P, t.L, t.D, t.C, t.Q, t.n, t.h + 1, t.R, t.ok⟩ h

theorem queueK_R (c : Nat) (t : St) (a : Nat) : (queueK G c t a).R = t.R := by
  unfold queueK
  cases hh : decide (t.h < t.n)
  · rw [cond_false]
  · rw [cond_true]
    exact foldl_eq (G := innerK G c (at' 8 t.Q t.h)) St.R (fun t l => innerK_R c _ t l)
      (List.range' 0 16) ⟨t.P, t.L, t.D, t.C, t.Q, t.n, t.h + 1, t.R, t.ok⟩

theorem queueK_pres {c : Nat} (hc : c < 2 ^ 8) (a : Nat) {t : St} (hI : Inv t)
    (hok : (queueK G c t a).ok = true) : Inv (queueK G c t a) := by
  unfold queueK at hok ⊢
  cases hh : decide (t.h < t.n)
  · rw [cond_false]
    exact hI
  · rw [hh, cond_true] at hok
    rw [cond_true]
    exact foldl_pres (G := innerK G c (at' 8 t.Q t.h)) (I := Inv)
      (fun t l => innerK_mono c _ t l) (List.range' 0 16)
      (fun l hl t hI h => innerK_pres hc
        (by simp [List.mem_range'] at hl; norm_num; omega) hI h)
      ⟨t.P, t.L, t.D, t.C, t.Q, t.n, t.h + 1, t.R, t.ok⟩ hI hok

theorem colK_mono (t : St) (c : Nat) : (colK G t c).ok = true → t.ok = true := by
  unfold colK
  dsimp only
  generalize (List.range' 1 135).foldl (rootK t.C) 0 = r
  intro h
  cases hr : (r != 0)
  · rw [hr, cond_false] at h
    exact h
  · rw [hr, cond_true] at h
    have := foldl_ok (G := queueK G c) (fun t a => queueK_mono c t a) (List.range' 0 136)
      ⟨t.P, t.L, pset 16 t.D r 0, pset 8 t.C r c, pset 8 0 0 r, 1, 0, t.R.push r,
        t.ok && decide (r < 136)⟩ h
    simp only [Bool.and_eq_true] at this
    exact this.1

theorem colK_pres {c : Nat} (hc : c < 2 ^ 8) {t : St} (hI : Inv t) (hok : (colK G t c).ok = true) :
    Inv (colK G t c) := by
  unfold colK at hok ⊢
  dsimp only at hok ⊢
  generalize (List.range' 1 135).foldl (rootK t.C) 0 = r at hok ⊢
  cases hr : (r != 0)
  · rw [cond_false]
    exact hI
  · rw [hr, cond_true] at hok
    rw [cond_true]
    have h1 := foldl_ok (G := queueK G c) (fun t a => queueK_mono c t a) (List.range' 0 136)
      ⟨t.P, t.L, pset 16 t.D r 0, pset 8 t.C r c, pset 8 0 0 r, 1, 0, t.R.push r,
        t.ok && decide (r < 136)⟩ hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact foldl_pres (G := queueK G c) (I := Inv) (fun t a => queueK_mono c t a) (List.range' 0 136)
      (fun a _ t hI h => queueK_pres hc a hI h)
      ⟨t.P, t.L, pset 16 t.D r 0, pset 8 t.C r c, pset 8 0 0 r, 1, 0, t.R.push r,
        t.ok && decide (r < 136)⟩
      ⟨hI.1, hI.2.1, canon_set hI.2.2.1 h1.2 (by norm_num), canon_set hI.2.2.2.1 h1.2 hc,
        canon_set (by rfl) (by omega) (lt8 (by omega))⟩ hok

@[expose] noncomputable def decI (t : St) : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  (dec 8 t.P, dec 8 t.L, dec 16 t.D, dec 8 t.C, decQ t.Q t.n)

@[expose] noncomputable def decL (t : St) : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ × ℕ :=
  (dec 8 t.P, dec 8 t.L, dec 16 t.D, dec 8 t.C, decQ t.Q t.n, t.h)

@[expose] noncomputable def decC (t : St) : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  (dec 8 t.P, dec 8 t.L, dec 16 t.D, dec 8 t.C, t.R)

@[expose] def gs0 : Array (Array ℕ) := (stabIdx.map fun j => omegaS[j]!).toArray

theorem gs0_size : gs0.size = 16 := by simp [gs0, stabIdx]

theorem dec_zero (w : Nat) : dec w 0 = Array.replicate 136 0 := by
  apply Array.ext
  · simp [dec]
  · intro i h1 h2
    simp [dec, at', CFSG.KC.Enum.pg]

theorem dec_dInit (h : (List.range 136).all (fun i => at' 16 dInit i == 1000) = true) :
    dec 16 dInit = Array.replicate 136 1000 := by
  apply Array.ext
  · simp [dec]
  · intro i h1 h2
    have hi : i < 136 := by simpa [dec] using h1
    simp only [dec, Array.getElem_ofFn, Array.getElem_replicate]
    have := List.all_eq_true.1 h i (List.mem_range.2 hi)
    simpa using this

theorem canon_dInit : canon1 136 16 dInit = true := by
  unfold dInit
  suffices h : ∀ k ≤ 136,
      canon1 136 16 ((List.range k).foldl (fun a i => pset 16 a i 1000) 0) = true from h 136 le_rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact canon_set (ih (by omega)) (by omega) (by norm_num)

theorem stabTree_eq (hG : ∀ l < 16, ∀ x, (gs0[l]!)[x]! = G l x) (hok : (stabTreeK G).ok = true)
    (hD : (List.range 136).all (fun i => at' 16 dInit i == 1000) = true)
    (hDc : canon1 136 16 dInit = true) : stabTree () = outK G := by
  unfold stabTreeK at hok
  unfold stabTree
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [show (List.map (fun j => omegaS[j]!) stabIdx).toArray = gs0 from rfl, gs0_size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_eq (G := colK G) (dec := decC) (ok := St.ok) (I := Inv) (fun t c => colK_mono t c)
    (List.range' 1 2 1) (fun c hc t hI h => colK_pres (by simp [List.mem_range'] at hc; norm_num; omega) hI h)
    ?cstep ⟨0, 0, dInit, 0, 0, 0, 0, #[], true⟩ ⟨rfl, rfl, hDc, rfl, rfl⟩ hok _ ?hst]
  case hst =>
    simp only [decC, dec_zero, dec_dInit hD]
  · simp only [pure_bind, Id.run, decC, outK, stabTreeK]
    try rfl
  case cstep =>
    intro c hc t hI hokc
    have hc8 : c < 2 ^ 8 := by simp [List.mem_range'] at hc; norm_num; omega
    simp only [decC]
    rw [forIn_eq (G := rootK t.C) (dec := id) (ok := fun _ => true) (I := fun _ => True)
      (fun _ _ _ => rfl) (List.range' 1 135 1) (fun _ _ _ _ _ => trivial) ?pstep 0 trivial rfl _ ?hp0]
    case hp0 => rfl
    case pstep =>
      intro p _ r _ _
      simp only [id, rootK, dec_get hI.2.2.2.1]
      cases (r == 0 && at' 8 t.C p == 0) <;> rfl
    simp only [pure_bind, id]
    unfold colK at hokc ⊢
    dsimp only at hokc ⊢
    generalize (List.range' 1 135 1).foldl (rootK t.C) 0 = r at hokc ⊢
    cases hr : (r != 0)
    · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
    · rw [hr] at hokc
      simp only [↓reduceIte, cond_true] at hokc ⊢
      have h1 := foldl_ok (fun t a => queueK_mono c t a) _ _ hokc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      have hr8 : r < 2 ^ 8 := lt8 (by omega)
      rw [dec_set hI.2.2.1 h1.2 (by norm_num), dec_set hI.2.2.2.1 h1.2 hc8, decQ_one hr8]
      rw [forIn_eq (G := queueK G c) (dec := decL) (ok := St.ok) (I := Inv)
        (fun t a => queueK_mono c t a) (List.range' 0 136 1)
        (fun a _ t hI h => queueK_pres hc8 a hI h) ?qstep
        ⟨t.P, t.L, pset 16 t.D r 0, pset 8 t.C r c, pset 8 0 0 r, 1, 0, t.R.push r,
          t.ok && decide (r < 136)⟩
        ⟨hI.1, hI.2.1, canon_set hI.2.2.1 h1.2 (by norm_num), canon_set hI.2.2.2.1 h1.2 hc8,
          canon_set (by rfl) (by omega) hr8⟩ hokc _ ?hq0]
      case hq0 => rfl
      · simp only [pure_bind, decL, decC]
        rw [foldl_eq St.R (fun t a => queueK_R c t a)]
      case qstep =>
        intro a _ t hI hq
        simp only [decL, decQ_size]
        unfold queueK at hq ⊢
        by_cases hh : t.h < t.n
        · simp only [hh, decide_true, cond_true, ↓reduceIte] at hq ⊢
          simp only [decQ_get hh]
          rw [forIn_eq (G := innerK G c (at' 8 t.Q t.h)) (dec := decI) (ok := St.ok) (I := Inv)
            (fun t l => innerK_mono c _ t l) (List.range' 0 16 1)
            (fun l hl t hI h => innerK_pres hc8
              (by simp [List.mem_range'] at hl; norm_num; omega) hI h) ?istep
            ⟨t.P, t.L, t.D, t.C, t.Q, t.n, t.h + 1, t.R, t.ok⟩ hI hq _ ?hi0]
          case hi0 => rfl
          · simp only [pure_bind, decI]
            rw [foldl_eq St.h (fun t l => innerK_h c _ t l)]
          case istep =>
            intro l hl u hIu hi
            have hl16 : l < 16 := by simp [List.mem_range'] at hl; omega
            simp only [decI]
            simp only [hG l hl16 (at' 8 t.Q t.h), dec_get hIu.2.2.2.1 (G l (at' 8 t.Q t.h))]
            unfold innerK at hi ⊢
            dsimp only at hi ⊢
            cases hb : (G l (at' 8 t.Q t.h) < 136 && G l (at' 8 t.Q t.h) != 0 &&
                at' 8 u.C (G l (at' 8 t.Q t.h)) == 0)
            · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
            · rw [hb] at hi
              simp only [↓reduceIte, cond_true] at hi ⊢
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hi hb
              obtain ⟨⟨⟨-, hx⟩, hd⟩, hn⟩ := hi
              have hy := hb.1.1
              simp only [dec_get hIu.2.2.1 (at' 8 t.Q t.h), dec_set hIu.1 hy (lt8 hx),
                dec_set hIu.2.1 hy (lt8 (by omega : l < 256)),
                dec_set hIu.2.2.1 hy (by norm_num; omega), dec_set hIu.2.2.2.1 hy hc8,
                decQ_push (Q := u.Q) (n := u.n) (lt8 (by omega : G l (at' 8 t.Q t.h) < 256))]
        · simp only [hh, decide_false, cond_false, ↓reduceIte]

theorem countP_range (g : ℕ → Bool) :
    ∀ n, (List.range n).countP g = ∑ i ∈ Finset.range n, if g i = true then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range g n, Finset.sum_range_succ]
    simp [List.countP_cons]

theorem card_filter_fin (f : ℕ → ℕ) (v n : ℕ) :
    (Finset.univ.filter fun p : Fin n => f p = v).card = (List.range n).countP (fun p => f p == v) := by
  rw [Finset.card_filter, countP_range]
  simp only [beq_iff_eq]
  exact Fin.sum_univ_eq_sum_range (fun i => if f i = v then 1 else 0) n

theorem stabTreeOK_eq {S : ℕ → ℕ → ℕ} (hS : ∀ j x, (omegaS[j]!)[x]! = S j x) {P L D C : ℕ}
    (hP : canon1 136 8 P = true) (hL : canon1 136 8 L = true) (hD : canon1 136 16 D = true)
    (hC : canon1 136 8 C = true) (r₁ r₂ : ℕ) :
    stabTreeOK (dec 8 P) (dec 8 L) (dec 16 D) (dec 8 C) r₁ r₂ = stabTreeOKP S P L D C r₁ r₂ := by
  unfold stabTreeOK stabTreeOKP
  simp only [dec_get hP, dec_get hL, dec_get hD, dec_get hC, hS, card_filter_fin]

theorem stabTreeK_inv (hok : (stabTreeK G).ok = true) (hDc : canon1 136 16 dInit = true) :
    Inv (stabTreeK G) := by
  unfold stabTreeK at hok ⊢
  exact foldl_pres (G := colK G) (I := Inv) (fun t c => colK_mono t c) (List.range' 1 2 1)
    (fun c hc t hI h => colK_pres (by simp [List.mem_range'] at hc; norm_num; omega) hI h)
    ⟨0, 0, dInit, 0, 0, 0, 0, #[], true⟩ ⟨rfl, rfl, hDc, rfl, rfl⟩ hok

end CFSG.KC.StabT919
