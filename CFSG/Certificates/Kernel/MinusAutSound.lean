module

public import Certificates.Data.Kernel.MinusAut
public import CFSG.Certificates.Kernel.MinusQuandleSound

public section

namespace CFSG.KC.MinusAut

open CFSG.OddTranspositions.PartThree CFSG.KD.MinusQuandle CFSG.KD.MinusAut CFSG.KC.MinusQuandle

theorem allF_of {n : ℕ} {g : ℕ → Bool} (h : ∀ k < n, g k = true) : allF n g = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec false (allF n g) (g n) = true
    rw [h n (by omega)]
    exact ih fun k hk => h k (by omega)

theorem ord_facts {R : ℕ → ℕ} {P X Y Q : ℕ} (h : ordOK R P X Y Q = true) :
    lane 7 P 0 = 0 ∧ lane 7 P 1 = 19 ∧ lane 7 P 5 = 1 ∧ lane 7 P 15 = 3 ∧
    (∀ t < 65, lane 7 P t < 65 ∧ lane 7 Q (lane 7 P t) = t ∧
      (isGen t = false → lane 7 X t < t ∧ lane 7 Y t < t ∧
        tq R (lane 7 P (lane 7 X t)) (lane 7 P (lane 7 Y t)) = lane 7 P t)) ∧
    (∀ q < 65, lane 7 Q q < 65 ∧ lane 7 P (lane 7 Q q) = q) := by
  simp only [ordOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h5⟩, h15⟩, hA⟩, hB⟩ := h
  refine ⟨h0, h1, h5, h15, fun t ht => ?_, fun q hq => ?_⟩
  · have h := allF_spec hA ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨hP, hQ⟩, hg⟩ := h
    refine ⟨hP, hQ, fun hng => ?_⟩
    rcases hg with hg | hg
    · rw [hng] at hg
      exact absurd hg Bool.false_ne_true
    · exact ⟨hg.1.1, hg.1.2, hg.2⟩
  · have h := allF_spec hB hq
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    exact h

theorem isGen_cases {t : ℕ} (h : isGen t = true) : t = 0 ∨ t = 1 ∨ t = 5 ∨ t = 15 := by
  simp only [isGen, Bool.or_eq_true, Nat.beq_eq] at h
  omega

theorem rec_agree {R : ℕ → ℕ} {P X Y Q : ℕ} (hO : ordOK R P X Y Q = true) {s : ℕ → ℕ}
    (hs : ∀ a b, a < 65 → b < 65 → s (tq R a b) = tq R (s a) (s b))
    {c1 c2 c3 n d : ℕ} (hn : n ≤ 65) (h0 : s 0 = 0) (h1 : s 19 = c1) (h2 : 5 < n → s 1 = c2)
    (h3 : 15 < n → s 3 = c3) (hrec : recOK R P X Y c1 c2 c3 n d = true) :
    ∀ t < n, lane 7 d (lane 7 P t) = s (lane 7 P t) := by
  obtain ⟨hP0, hP1, hP5, hP15, hA, -⟩ := ord_facts hO
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    have hr := allF_spec hrec ht
    simp only [Bool.and_eq_true, Nat.beq_eq] at hr
    rw [hr.2]
    cases hg : isGen t
    · obtain ⟨hx, hy, hxy⟩ := (hA t (by omega)).2.2 hg
      have hv : val R P X Y c1 c2 c3 t d =
          tq R (lane 7 d (lane 7 P (lane 7 X t))) (lane 7 d (lane 7 P (lane 7 Y t))) := by
        simp [val, hg]
      rw [hv, ih _ hx (by omega), ih _ hy (by omega), ← hxy,
        hs _ _ (hA _ (by omega)).1 (hA _ (by omega)).1]
    · have hv : val R P X Y c1 c2 c3 t d = gv c1 c2 c3 t := by simp [val, hg]
      rw [hv]
      rcases isGen_cases hg with rfl | rfl | rfl | rfl
      · rw [hP0, h0]
        rfl
      · rw [hP1, h1]
        rfl
      · rw [hP5, h2 ht]
        rfl
      · rw [hP15, h3 ht]
        rfl

theorem homOn_true {R : ℕ → ℕ} (hR : rowsOK R = true) {P X Y Q : ℕ}
    (hO : ordOK R P X Y Q = true) {s : ℕ → ℕ}
    (hs : ∀ a b, a < 65 → b < 65 → s (tq R a b) = tq R (s a) (s b)) {n d : ℕ} (hn : n ≤ 65)
    (hag : ∀ t < n, lane 7 d (lane 7 P t) = s (lane 7 P t)) : homOn R P Q n d = true := by
  obtain ⟨-, -, -, -, hA, hB⟩ := ord_facts hO
  apply allF_of
  intro a ha
  apply allF_of
  intro b hb
  have hPa := (hA a (by omega)).1
  have hPb := (hA b (by omega)).1
  have hq := (tq_spec hR hPa hPb).2
  rw [Bool.or_eq_true]
  by_cases hQ : lane 7 Q (tq R (lane 7 P a) (lane 7 P b)) < n
  · right
    rw [Nat.beq_eq]
    have hPQ := (hB _ hq).2
    calc lane 7 d (tq R (lane 7 P a) (lane 7 P b))
        = lane 7 d (lane 7 P (lane 7 Q (tq R (lane 7 P a) (lane 7 P b)))) := by rw [hPQ]
      _ = s (lane 7 P (lane 7 Q (tq R (lane 7 P a) (lane 7 P b)))) := hag _ hQ
      _ = s (tq R (lane 7 P a) (lane 7 P b)) := by rw [hPQ]
      _ = tq R (s (lane 7 P a)) (s (lane 7 P b)) := hs _ _ hPa hPb
      _ = tq R (lane 7 d (lane 7 P a)) (lane 7 d (lane 7 P b)) := by rw [hag a ha, hag b hb]
  · left
    cases hc : Nat.blt (lane 7 Q (tq R (lane 7 P a) (lane 7 P b))) n
    · rfl
    · exact absurd (by simpa [Nat.blt_eq] using hc) hQ

theorem failsD_false {R : ℕ → ℕ} (hR : rowsOK R = true) {P X Y Q : ℕ}
    (hO : ordOK R P X Y Q = true) {s : ℕ → ℕ}
    (hs : ∀ a b, a < 65 → b < 65 → s (tq R a b) = tq R (s a) (s b))
    {c1 c2 c3 n : ℕ} (d : ℕ) (hn : n ≤ 65) (h0 : s 0 = 0) (h1 : s 19 = c1) (h2 : 5 < n → s 1 = c2)
    (h3 : 15 < n → s 3 = c3) : failsD R P X Y Q c1 c2 c3 n d = false := by
  unfold failsD
  cases hr : recOK R P X Y c1 c2 c3 n d
  · rfl
  · rw [homOn_true hR hO hs hn (rec_agree hO hs hn h0 h1 h2 h3 hr)]
    rfl

theorem kmask_mem {H : List (ℕ × ℕ × ℕ × List ℕ)} {k : ℕ} (h : (kmask H).testBit k = true) :
    ∃ e ∈ H, key e.1 e.2.1 e.2.2.1 = k := by
  induction H with
  | nil => simp [kmask] at h
  | cons e H ih =>
    change (1 <<< key e.1 e.2.1 e.2.2.1 ||| kmask H).testBit k = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self .., of_decide_eq_true h⟩
    · obtain ⟨e', he', hk⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hk⟩

theorem homsOK_mem {R : ℕ → ℕ} {P X Y : ℕ} {H : List (ℕ × ℕ × ℕ × List ℕ)}
    (h : homsOK R P X Y H = true) : ∀ e ∈ H, entryOK R P X Y e = true := by
  induction H with
  | nil => simp
  | cons e H ih =>
    change (entryOK R P X Y e && homsOK R P X Y H) = true at h
    rw [Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact ih h.2 e' he'

theorem wordOK_cons {i : ℕ} {w : List ℕ} (h : wordOK (i :: w) = true) : i < 65 ∧ wordOK w = true := by
  change (Nat.blt i 65 && wordOK w) = true at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem wact_val {R : ℕ → ℕ} (hR : rowsOK R = true) :
    ∀ (w : List ℕ), wordOK w = true → ∀ q : Fin 65,
      wact R w q = ((w.map (Fin.ofNat 65)).foldr minusQuandleTf q).val := by
  intro w
  induction w with
  | nil => intro _ q; rfl
  | cons i w ih =>
    intro hw q
    obtain ⟨hi, hw⟩ := wordOK_cons hw
    change tq R i (wact R w q) = _
    rw [List.map_cons, List.foldr_cons, tf_val hR, ← ih hw q, Fin.val_ofNat, Nat.mod_eq_of_lt hi]

theorem hom_word {R : ℕ → ℕ} (hR : rowsOK R = true) {P X Y Q : ℕ}
    (hO : ordOK R P X Y Q = true) {H : List (ℕ × ℕ × ℕ × List ℕ)}
    (hH : homsOK R P X Y H = true) (hM : ∀ c1 < 65, mainA R P X Y Q (kmask H) c1 = true)
    (σ : Fin 65 → Fin 65) (hinj : Function.Injective σ)
    (hhom : ∀ i j : Fin 65, σ (minusQuandleTf i j) = minusQuandleTf (σ i) (σ j))
    (h0 : σ 0 = 0) : ∃ w : List (Fin 65), ∀ k : Fin 65, σ k = w.foldr minusQuandleTf k := by
  obtain ⟨-, -, -, -, hA, hB⟩ := ord_facts hO
  let s : ℕ → ℕ := fun q => if h : q < 65 then (σ ⟨q, h⟩ : ℕ) else 0
  have hsv : ∀ q : Fin 65, s q = σ q := fun q => by simp [s, q.isLt]
  have hs : ∀ a b, a < 65 → b < 65 → s (tq R a b) = tq R (s a) (s b) := by
    intro a b ha hb
    have hab : (⟨tq R a b, (tq_spec hR ha hb).2⟩ : Fin 65) = minusQuandleTf ⟨a, ha⟩ ⟨b, hb⟩ :=
      Fin.ext (tf_val hR ⟨a, ha⟩ ⟨b, hb⟩).symm
    have e1 := hsv ⟨tq R a b, (tq_spec hR ha hb).2⟩
    have e2 := hsv ⟨a, ha⟩
    have e3 := hsv ⟨b, hb⟩
    simp only at e1 e2 e3
    rw [e1, e2, e3, hab, hhom, tf_val hR]
  have hs0 : s 0 = 0 := by
    have := hsv 0
    simp only [Fin.val_zero] at this
    rw [this, h0]
    rfl
  have hne : ∀ a b : Fin 65, a ≠ b → s a ≠ s b := by
    intro a b hab h
    rw [hsv, hsv] at h
    exact hab (hinj (Fin.ext h))
  have hlt : ∀ q : Fin 65, s q < 65 := fun q => by rw [hsv]; exact (σ q).isLt
  have n1 : s 19 ≠ 0 := by
    have := hne (19 : Fin 65) 0 (by decide)
    simpa [hs0] using this
  have n2 : s 1 ≠ 0 := by
    have := hne (1 : Fin 65) 0 (by decide)
    simpa [hs0] using this
  have n3 : s 3 ≠ 0 := by
    have := hne (3 : Fin 65) 0 (by decide)
    simpa [hs0] using this
  have n21 : s 1 ≠ s 19 := by simpa using hne (1 : Fin 65) 19 (by decide)
  have n31 : s 3 ≠ s 19 := by simpa using hne (3 : Fin 65) 19 (by decide)
  have n32 : s 3 ≠ s 1 := by simpa using hne (3 : Fin 65) 1 (by decide)
  have l1 : s 19 < 65 := by simpa using hlt (19 : Fin 65)
  have l2 : s 1 < 65 := by simpa using hlt (1 : Fin 65)
  have l3 : s 3 < 65 := by simpa using hlt (3 : Fin 65)
  have hm := hM (s 19) l1
  have beqF : ∀ {a b : ℕ}, a ≠ b → Nat.beq a b = false := fun {a b} h => by
    cases hc : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) h
  have hb1 : Nat.beq (s 19) 0 = false := beqF n1
  have hf1 : failsD R P X Y Q (s 19) 0 0 5 (ext R P X Y (s 19) 0 0 5) = false :=
    failsD_false hR hO hs _ (by omega) hs0 rfl (by omega) (by omega)
  simp only [mainA, force_eq, hb1, hf1, Bool.false_or] at hm
  have hm2 := allF_spec hm l2
  have hb2 : Nat.beq (s 1) 0 = false := beqF n2
  have hb21 : Nat.beq (s 1) (s 19) = false := beqF n21
  have hf2 : failsD R P X Y Q (s 19) (s 1) 0 15 (ext R P X Y (s 19) (s 1) 0 15) = false :=
    failsD_false hR hO hs _ (by omega) hs0 rfl (fun _ => rfl) (by omega)
  simp only [hb2, hb21, hf2, force_eq, Bool.false_or] at hm2
  have hm3 := allF_spec hm2 l3
  have hb3 : Nat.beq (s 3) 0 = false := beqF n3
  have hb31 : Nat.beq (s 3) (s 19) = false := beqF n31
  have hb32 : Nat.beq (s 3) (s 1) = false := beqF n32
  have hf3 : failsD R P X Y Q (s 19) (s 1) (s 3) 18
      (extFrom R P X Y (s 19) (s 1) (s 3) (ext R P X Y (s 19) (s 1) 0 15) 15 3) = false :=
    failsD_false hR hO hs _ (by omega) hs0 rfl (fun _ => rfl) (fun _ => rfl)
  simp only [hb3, hb31, hb32, hf3, force_eq, Bool.false_or, Bool.or_false] at hm3
  obtain ⟨e, he, hk⟩ := kmask_mem hm3
  have hE := homsOK_mem hH e he
  simp only [entryOK, force_eq, Bool.and_eq_true, Nat.blt_eq] at hE
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, hw⟩, hrec, hall⟩ := hE
  have hk' : 4225 * e.1 + 65 * e.2.1 + e.2.2.1 = 4225 * s 19 + 65 * s 1 + s 3 := hk
  have q1 : e.1 = s 19 := by omega
  have q2 : e.2.1 = s 1 := by omega
  have q3 : e.2.2.1 = s 3 := by omega
  have hag := rec_agree hO hs le_rfl hs0 q1.symm (fun _ => q2.symm) (fun _ => q3.symm) hrec
  refine ⟨e.2.2.2.map (Fin.ofNat 65), fun k => Fin.ext ?_⟩
  rw [← wact_val hR _ hw k]
  have hwk := allF_spec hall k.isLt
  rw [Nat.beq_eq] at hwk
  rw [hwk]
  have hQk := hB k k.isLt
  have := hag _ hQk.1
  rw [hQk.2] at this
  rw [this, hsv]

theorem mainOK_spec {R : ℕ → ℕ} {P X Y Q K lo m : ℕ} (h : mainOK R P X Y Q K lo m = true)
    {c : ℕ} (h1 : lo ≤ c) (h2 : c < lo + m) : mainA R P X Y Q K c = true := by
  have h' := allF_spec h (k := c - lo) (by omega)
  have e : Nat.add lo (c - lo) = c := by
    change lo + (c - lo) = c
    omega
  rw [e] at h'
  exact h'

theorem transAux_spec {R : ℕ → ℕ} :
    ∀ (W : List (List ℕ)) (j : ℕ), transAux R W j = true →
      ∀ m (hm : m < W.length), wordOK W[m] = true ∧ wact R W[m] 0 = j + m := by
  intro W
  induction W with
  | nil => intro j _ m hm; simp at hm
  | cons w W ih =>
    intro j h m hm
    change (wordOK w && Nat.beq (wact R w 0) j && transAux R W (Nat.succ j)) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    rcases m with _ | m
    · exact ⟨h.1.1, by simpa using h.1.2⟩
    · have := ih (Nat.succ j) h.2 m (by simpa using hm)
      simp only [List.getElem_cons_succ]
      exact ⟨this.1, by rw [this.2]; omega⟩

theorem trans_word {R : ℕ → ℕ} (hR : rowsOK R = true) {W : List (List ℕ)}
    (hW : transOK R W = true) (i : Fin 65) : ∃ w : List (Fin 65), w.foldr minusQuandleTf 0 = i := by
  simp only [transOK, Bool.and_eq_true, Nat.beq_eq] at hW
  have hm : (i : ℕ) < W.length := by rw [hW.1]; exact i.isLt
  obtain ⟨hw, hact⟩ := transAux_spec W 0 hW.2 i hm
  refine ⟨W[(i : ℕ)].map (Fin.ofNat 65), Fin.ext ?_⟩
  rw [← wact_val hR _ hw 0]
  simpa using hact

end CFSG.KC.MinusAut
