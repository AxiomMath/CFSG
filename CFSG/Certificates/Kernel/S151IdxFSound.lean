module

public import Certificates.Data.Kernel.S151IdxF
public import CFSG.Certificates.Kernel.SporLatOmegaSound

public section

namespace CFSG.KC.IdxF

open CFSG.KC.E64F CFSG.KC.SLOm CFSG.Quasithin.S151S9T CFSG.QuasithinUnique.Ch1.SporLat

variable {n : Nat}

theorem good_three1 {s : Array Nat} {f g h : Nat → Nat} (hs : Good n s f) :
    ∀ l < (#[s] : Array (Array Nat)).size, Good n ((#[s] : Array (Array Nat)).getD l #[])
      (three f g h l)
  | 0, _ => hs
  | _ + 1, hl => absurd hl (by simp)

theorem good_three2 {s t : Array Nat} {f g h : Nat → Nat} (hs : Good n s f) (ht : Good n t g) :
    ∀ l < (#[s, t] : Array (Array Nat)).size, Good n ((#[s, t] : Array (Array Nat)).getD l #[])
      (three f g h l)
  | 0, _ => hs
  | 1, _ => ht
  | _ + 2, hl => absurd hl (by simp)

theorem good_three3 {s t u : Array Nat} {f g h : Nat → Nat} (hs : Good n s f) (ht : Good n t g)
    (hu : Good n u h) :
    ∀ l < (#[s, t, u] : Array (Array Nat)).size,
      Good n ((#[s, t, u] : Array (Array Nat)).getD l #[]) (three f g h l)
  | 0, _ => hs
  | 1, _ => ht
  | 2, _ => hu
  | _ + 3, hl => absurd hl (by simp)

theorem good_idTabN (n : Nat) : Good n (idTab n) (fun p => p) := by
  refine ⟨by simp [idTab], fun p hp => ⟨?_, hp⟩⟩
  simp [idTab, Array.getD_eq_getD_getElem?, hp]

theorem idOn_iff {f : Nat → Nat} : idOn n f = true ↔ ∀ p < n, f p = p := by
  unfold idOn
  simp

theorem eqOn_iff {f g : Nat → Nat} : eqOn n f g = true ↔ ∀ p < n, f p = g p := by
  unfold eqOn
  simp

theorem tab_eq_iff {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g) :
    s = t ↔ ∀ p < n, f p = g p := by
  refine ⟨fun e p hp => ?_, good_ext hs ht⟩
  rw [← (hs.2 p hp).1, ← (ht.2 p hp).1, e]

theorem tab_eq_of_eqOn {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g)
    (h : eqOn n f g = true) : s = t :=
  (tab_eq_iff hs ht).2 (eqOn_iff.1 h)

theorem tab_ne_of_eqOn {s t : Array Nat} {f g : Nat → Nat} (hs : Good n s f) (ht : Good n t g)
    (h : (!eqOn n f g) = true) : s ≠ t := by
  intro e
  have h' : eqOn n f g = true := eqOn_iff.2 ((tab_eq_iff hs ht).1 e)
  rw [h'] at h
  exact absurd h (by decide)

theorem distinct5_spec {d : Nat → Nat → Nat} {T : Nat → Array Nat}
    (hT : ∀ i < 5, Good n (T i) (d i)) (h : distinct5 n d = true) :
    ∀ i < 5, ∀ i' < 5, T i = T i' → i = i' := by
  intro i hi i' hi' e
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hi)) i'
    (List.mem_range.2 hi')
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact beq_iff_eq.1 h1
  · exact absurd e (tab_ne_of_eqOn (hT i hi) (hT i' hi') h1)

theorem fixLab_spec {Δ : List Nat} (hD : ∀ p ∈ Δ, p < n) {t : Array Nat} {f : Nat → Nat}
    (ht : Good n t f) (h : fixLab Δ f = true) : ptAct t Δ = Δ := by
  rw [ptAct_good ht hD]
  exact beq_iff_eq.1 h

theorem getD_append_left {A B : List (Array Nat)} {l : Nat} (hl : l < A.length) :
    (A ++ B).toArray.getD l #[] = A.toArray.getD l #[] := by
  simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left hl, hl]

theorem getD_append_right {A B : List (Array Nat)} {k : Nat} (hk : k < B.length) :
    (A ++ B).toArray.getD (A.length + k) #[] = B[k] := by
  simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, hk]

theorem getElem!_list_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) : l[i]! = l.getD i default := by
  simp [List.getD_eq_getElem?_getD]

section Sound

variable {Δ : List Nat} {D : LatData (List Nat)} {nm ns : Nat} {mlen : Nat → Nat}
  {M : Nat → Nat → Nat → Nat} {Sl : Nat → Nat → Nat}

structure Hyp (n : Nat) (D : LatData (List Nat)) (nm ns : Nat) (mlen : Nat → Nat)
    (M : Nat → Nat → Nat → Nat) (Sl : Nat → Nat → Nat) : Prop where
  nm_eq : D.mw.size = nm
  ns_eq : D.sTabs.length = ns
  len : ∀ j < nm, (D.mt[j]!).length = mlen j
  goodM : ∀ j < nm, ∀ l < (D.sTabs ++ D.mt[j]!).toArray.size,
    Good n ((D.sTabs ++ D.mt[j]!).toArray.getD l #[]) (M j l)
  goodS : ∀ l < D.sTabs.toArray.size, Good n (D.sTabs.toArray.getD l #[]) (Sl l)

theorem Hyp.good_gen (H : Hyp n D nm ns mlen M Sl) {j : Nat} (hj : j < nm) {k : Nat}
    (hk : k < (D.mt[j]!).length) : Good n (D.mt[j]!)[k] (M j (ns + k)) := by
  have e := getD_append_right (A := D.sTabs) hk
  rw [H.ns_eq] at e
  rw [← e]
  exact H.goodM j hj _ (by simp [H.ns_eq, hk])

theorem Hyp.good_mword (H : Hyp n D nm ns mlen M Sl) {j : Nat} (hj : j < nm) (h1 : mlen j = 1)
    {w : List Nat} (hw : w.all (fun l => decide (l < ns + 1)) = true) :
    Good n (wordTabA (D.sTabs ++ D.mt[j]!).toArray n w) (wordF (M j) w) := by
  refine good_word (H.goodM j hj) fun l hl => ?_
  have := of_decide_eq_true (List.all_eq_true.1 hw l hl)
  simp [H.ns_eq, H.len j hj, h1]
  omega

theorem Hyp.good_sword (H : Hyp n D nm ns mlen M Sl) {w : List Nat}
    (hw : w.all (fun l => decide (l < ns)) = true) :
    Good n (wordTabA D.sTabs.toArray n w) (wordF Sl w) := by
  refine good_word H.goodS fun l hl => ?_
  have := of_decide_eq_true (List.all_eq_true.1 hw l hl)
  simpa [H.ns_eq] using this

theorem lt_of_all {w : List Nat} {m : Nat} (hw : w.all (fun l => decide (l < m)) = true) :
    ∀ l ∈ w, l < m := fun l hl => of_decide_eq_true (List.all_eq_true.1 hw l hl)

theorem czv_spec (H : Hyp n D nm ns mlen M Sl) {zT : Array Nat} {z : Nat → Nat} (hz : Good n zT z)
    {j : Nat} (hj : j < nm) :
    ((List.range (mlen j)).all fun k =>
        eqOn n (fun p => z (M j (ns + k) p)) (fun p => M j (ns + k) (z p))) = true ↔
      ∀ t ∈ D.mt[j]!, wordTabA #[zT, t] n [0, 1] = wordTabA #[zT, t] n [1, 0] := by
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    have g := H.good_gen hj hk
    have h2 := h k (List.mem_range.2 (by rw [← H.len j hj]; exact hk))
    exact tab_eq_of_eqOn (good_word (good_three2 (h := id) hz g) (by simp))
      (good_word (good_three2 (h := id) hz g) (by simp)) h2
  · intro h k hk
    have hk' : k < (D.mt[j]!).length := by rw [H.len j hj]; exact List.mem_range.1 hk
    have g := H.good_gen hj hk'
    have e := h _ (List.getElem_mem hk')
    exact eqOn_iff.2 ((tab_eq_iff (good_word (good_three2 (h := id) hz g) (by simp))
      (good_word (good_three2 (h := id) hz g) (by simp))).1 e)

theorem idx3OkF_sound (H : Hyp n D nm ns mlen M Sl) {zT : Array Nat} {z : Nat → Nat}
    (hz : Good n zT z) {W : Idx3Wit} (h : idx3OkF W n Δ nm ns mlen M Sl z = true) :
    W.Ok n ptAct Δ D zT := by
  unfold idx3OkF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hp⟩, h1⟩, hxw⟩, hczl⟩, hcz⟩, hx3⟩, hx1⟩, hrl⟩, hril⟩, hr⟩, hdc⟩ := h
  have hD' := lt_of_all hD
  have hp' : W.p < nm := of_decide_eq_true hp
  have h1' : mlen W.p = 1 := beq_iff_eq.1 h1
  have hx : Good n (W.xT n D) (xF W M) := H.good_mword hp' h1' hxw
  have hrT : ∀ i < 5, Good n (W.rT n D i) (wordF Sl (W.rw.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx3Wit.rT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.1.1
  have hriT : ∀ i < 5, Good n (W.riT n D i) (wordF Sl (W.ri.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx3Wit.riT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.1.2
  refine ⟨by rw [H.nm_eq]; exact hp', by rw [H.len _ hp', h1'], ?_, ?_, ?_, beq_iff_eq.1 hrl,
    beq_iff_eq.1 hril, fun i hi => ?_, ?_, ?_, fun j hj => ?_⟩
  · intro l hl
    have := lt_of_all hxw l hl
    rw [H.ns_eq]
    exact this
  · exact tab_eq_of_eqOn (good_word (good_three1 (g := id) (h := id) hx) (by simp))
      (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 hx3))
  · refine tab_ne_of_eqOn hx (good_idTabN n) ?_
    rw [Bool.not_eq_true'] at hx1 ⊢
    rw [Bool.eq_false_iff] at hx1 ⊢
    exact fun e => hx1 (idOn_iff.2 (eqOn_iff.1 e))
  · have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := e
    refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, ?_, ?_⟩
    · rw [H.ns_eq]
      exact lt_of_all e1 l (by rwa [getElem!_list_eq] at hl)
    · rw [H.ns_eq]
      exact lt_of_all e2 l (by rwa [getElem!_list_eq] at hl)
    · exact tab_eq_of_eqOn (good_word (good_three2 (h := id) (hrT i hi) (hriT i hi)) (by simp))
        (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 e3))
    · exact fixLab_spec hD' (good_word (good_three2 (h := id) hx (hrT i hi)) (by simp)) e4
    · exact fixLab_spec hD' (good_word (good_three2 (h := id) hx (hrT i hi)) (by simp)) e5
  · exact distinct5_spec (T := fun i => W.dcT n D i) (fun i hi =>
      good_word (good_three3 (hrT i hi) hx (hriT i hi)) (by simp [dcWord])) hdc
  · rw [beq_iff_eq.1 hczl, H.nm_eq]
  · rw [H.nm_eq] at hj
    have e := List.all_eq_true.1 hcz j (List.mem_range.2 hj)
    rw [beq_iff_eq] at e
    rw [getElem!_list_eq, ← czv_spec H hz hj, ← e]
    rfl

theorem idx9OkF_sound (H : Hyp n D nm ns mlen M Sl) {W : Idx9Wit}
    (h : idx9OkF W n Δ nm ns mlen M Sl = true) : W.Ok n ptAct Δ D := by
  unfold idx9OkF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hp1⟩, hp6⟩, h1⟩, h6⟩, hx1w⟩, hx6w⟩, hx13⟩, hx11⟩, hx63⟩, hx61⟩,
    hcm⟩, hrl⟩, hril⟩, hr⟩, hf⟩ := h
  have hD' := lt_of_all hD
  have hp1' : W.p₁ < nm := of_decide_eq_true hp1
  have hp6' : W.p₆ < nm := of_decide_eq_true hp6
  have h1' : mlen W.p₁ = 1 := beq_iff_eq.1 h1
  have h6' : mlen W.p₆ = 1 := beq_iff_eq.1 h6
  have hx1 : Good n (W.x1T n D) (x1F W M) := H.good_mword hp1' h1' hx1w
  have hx6 : Good n (W.x6T n D) (x6F W M) := H.good_mword hp6' h6' hx6w
  have hrT : ∀ i < 5, Good n (W.rT n D i) (wordF Sl (W.rw.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx9Wit.rT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.1
  have hriT : ∀ i < 5, Good n (W.riT n D i) (wordF Sl (W.ri.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx9Wit.riT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.2
  have hfT : ∀ k < 4, Good n (W.fT n D k) (fF W M k) := fun k hk => by
    unfold Idx9Wit.fT fF
    rcases k with _ | _ | _ | _ | k
    · exact hx1
    · exact hx6
    · exact good_word (good_three2 (h := id) hx1 hx6) (by simp)
    · exact good_word (good_three2 (h := id) hx1 hx6) (by simp)
    · omega
  have ne_id : ∀ {t : Array Nat} {f : Nat → Nat}, Good n t f → (!idOn n f) = true →
      t ≠ idTab n := fun ht hf => by
    refine tab_ne_of_eqOn ht (good_idTabN n) ?_
    rw [Bool.not_eq_true'] at hf ⊢
    rw [Bool.eq_false_iff] at hf ⊢
    exact fun e => hf (idOn_iff.2 (eqOn_iff.1 e))
  have cube : ∀ {t : Array Nat} {f : Nat → Nat}, Good n t f →
      idOn n (fun p => f (f (f p))) = true → wordTabA #[t] n [0, 0, 0] = idTab n := fun ht hf =>
    tab_eq_of_eqOn (good_word (good_three1 (g := id) (h := id) ht) (by simp))
      (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 hf))
  refine ⟨by rw [H.nm_eq]; exact hp1', by rw [H.nm_eq]; exact hp6', by rw [H.len _ hp1', h1'],
    by rw [H.len _ hp6', h6'], fun l hl => by rw [H.ns_eq]; exact lt_of_all hx1w l hl,
    fun l hl => by rw [H.ns_eq]; exact lt_of_all hx6w l hl, cube hx1 hx13, ne_id hx1 hx11,
    cube hx6 hx63, ne_id hx6 hx61, ?_, beq_iff_eq.1 hrl, beq_iff_eq.1 hril, fun i hi => ?_,
    fun k hk => ?_⟩
  · exact tab_eq_of_eqOn (good_word (good_three2 (h := id) hx1 hx6) (by simp))
      (good_word (good_three2 (h := id) hx1 hx6) (by simp)) hcm
  · have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := e
    refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, fun a ha b hb => ?_⟩
    · rw [H.ns_eq]
      exact lt_of_all e1 l (by rwa [getElem!_list_eq] at hl)
    · rw [H.ns_eq]
      exact lt_of_all e2 l (by rwa [getElem!_list_eq] at hl)
    · exact tab_eq_of_eqOn (good_word (good_three2 (h := id) (hrT i hi) (hriT i hi)) (by simp))
        (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 e3))
    · have e5 := List.all_eq_true.1 (List.all_eq_true.1 e4 a (List.mem_range.2 ha)) b
        (List.mem_range.2 hb)
      refine fixLab_spec hD' (good_word (good_three3 hx1 hx6 (hrT i hi)) fun l hl => ?_) e5
      unfold conj9Word at hl
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hl
      simp only [List.size_toArray, List.length_cons, List.length_nil]
      omega
  · have e := List.all_eq_true.1 hf k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at e
    refine ⟨cube (hfT k hk) e.1, ?_⟩
    exact distinct5_spec (T := fun i => W.dcT n D k i) (fun i hi =>
      good_word (good_three3 (hrT i hi) (hfT k hk) (hriT i hi)) (by simp [dcWord])) e.2

end Sound

end CFSG.KC.IdxF

end
