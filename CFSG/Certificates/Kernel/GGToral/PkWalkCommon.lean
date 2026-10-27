module

public import CFSG.Certificates.Kernel.GGToral.PkRoots

public section

namespace CFSG.KC.GGToral

theorem rd_spec {k : ℕ → List ℕ → Bool} {s : List ℕ} (h : rd k s = true) :
    ∃ x t, k x t = true := by
  cases s with
  | nil => exact absurd h (by simp)
  | cons x t => exact ⟨x, t, h⟩

theorem memB_zero (r : ℕ) : memB 0 r = false := by
  cases h : memB 0 r with
  | false => rfl
  | true =>
    rw [memB_iff, Nat.zero_testBit] at h
    exact absurd h (by simp)

theorem memB_lor (a b r : ℕ) : memB (Nat.lor a b) r = true ↔ memB a r = true ∨ memB b r = true := by
  rw [memB_iff, memB_iff, memB_iff]
  change (a ||| b).testBit r = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true]

theorem memB_shiftLeft_one {x r : ℕ} (h : memB (Nat.shiftLeft 1 x) r = true) : x = r := by
  rw [memB_iff] at h
  change (1 <<< x).testBit r = true at h
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h
  exact of_decide_eq_true h

theorem memB_maskOf {r : ℕ} : ∀ {mem : List ℕ}, memB (maskOf mem) r = true → r ∈ mem
  | [], h => by
    rw [show maskOf [] = 0 from rfl, memB_zero] at h
    exact absurd h (by simp)
  | x :: mem, h => by
    rcases (memB_lor _ _ r).mp h with h1 | h1
    · exact List.mem_cons_of_mem _ (memB_maskOf h1)
    · rw [memB_shiftLeft_one h1]
      exact List.mem_cons_self

theorem memB_foldl {r : ℕ} : ∀ {cls : List (List ℕ × ℕ)} {acc : ℕ},
    memB (cls.foldl (fun a c => Nat.lor a (maskOf c.1)) acc) r = true →
      memB acc r = true ∨ ∃ c ∈ cls, r ∈ c.1
  | [], _, h => Or.inl h
  | c :: cls, acc, h => by
    rcases memB_foldl (cls := cls) h with h1 | ⟨c', hc', h1⟩
    · rcases (memB_lor _ _ r).mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨c, List.mem_cons_self, memB_maskOf h2⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h1⟩

@[expose] def ChainOK (H : Hd) (reps : List ℕ) : List ℕ → Prop
  | [] => True
  | v :: ents => (v ∈ reps ∨ ∃ g, inM H (maskL H ents) (letter H g v) = true) ∧ ChainOK H reps ents

theorem ChainOK.mono {H : Hd} {reps reps' : List ℕ} (h : ∀ r ∈ reps, r ∈ reps') :
    ∀ {ents : List ℕ}, ChainOK H reps ents → ChainOK H reps' ents
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨h1.imp (h _) id, ChainOK.mono h h2⟩

@[expose] def EntsInv (H : Hd) (mask : ℕ) (reps ents : List ℕ) : Prop :=
  mask = maskL H ents ∧ (∀ v ∈ ents, vecOK H v = true) ∧ (∀ r ∈ reps, r ∈ ents) ∧
    ChainOK H reps ents

theorem entsK_spec (H : Hd) (kont : ℕ → List ℕ → List ℕ → List ℕ → Bool) (m : ℕ) :
    ∀ mask reps ents s, entsK H kont m mask reps ents s = true → EntsInv H mask reps ents →
      ∃ mask' reps' ents' t, EntsInv H mask' reps' ents' ∧ kont mask' reps' ents' t = true := by
  induction m with
  | zero => exact fun mask reps ents s h hI => ⟨mask, reps, ents, s, hI, h⟩
  | succ m ih =>
    intro mask reps ents s h hI
    obtain ⟨v, s1, h⟩ := rd_spec h
    obtain ⟨l, s2, h⟩ := rd_spec h
    obtain ⟨hv, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨hl, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨hm, hents, hreps, hch⟩ := hI
    have hents' : ∀ w ∈ v :: ents, vecOK H w = true := fun w hw => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact hents w hw
    generalize hb : Nat.beq l 0 = b at h hl
    cases b with
    | true =>
      refine ih _ _ _ _ h ⟨by rw [hm]; rfl, hents', fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hreps r hr)
      · exact ⟨Or.inl List.mem_cons_self,
          ChainOK.mono (fun r hr => List.mem_cons_of_mem _ hr) hch⟩
    | false =>
      have hl' : inM H mask (letter H (Nat.sub l 1) v) = true := by
        rcases (orB_eq_true _ _).mp hl with h0 | h0
        · exact absurd h0 (by simp)
        · exact h0
      refine ih _ _ _ _ h ⟨by rw [hm]; rfl, hents',
        fun r hr => List.mem_cons_of_mem _ (hreps r hr), ?_⟩
      exact ⟨Or.inr ⟨_, hm ▸ hl'⟩, hch⟩

@[expose] def LMFacts (H : Hd) (mask : ℕ) : Prop :=
  ∃ reps ents, EntsInv H mask reps ents ∧ closedLM H mask ents = true ∧
    ∀ r ∈ reps, ∀ e ∈ ents, ∃ t, npItem H mask r e t = true

theorem npRow_spec (H : Hd) (mask r : ℕ) (K : List ℕ → Bool) : ∀ (ents s : List ℕ),
    List.rec (motive := fun _ => List ℕ → Bool) K
      (fun e _ ihe => fun s1 => rd (fun t s2 => andB (npItem H mask r e t) (ihe s2)) s1) ents s =
        true →
    (∀ e ∈ ents, ∃ t, npItem H mask r e t = true) ∧ ∃ t, K t = true
  | [], s, h => ⟨fun _ he => absurd he (by simp), s, h⟩
  | e :: ents, s, h => by
    obtain ⟨t, s2, h⟩ := rd_spec h
    obtain ⟨h1, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h2, h3⟩ := npRow_spec H mask r K ents s2 h
    refine ⟨fun e' he' => ?_, h3⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨t, h1⟩
    · exact h2 e' he'

theorem noPlaneK_spec (H : Hd) (mask : ℕ) (ents : List ℕ) (kont : List ℕ → Bool) :
    ∀ (reps s : List ℕ), noPlaneK H mask ents kont reps s = true →
      (∀ r ∈ reps, ∀ e ∈ ents, ∃ t, npItem H mask r e t = true) ∧ ∃ t, kont t = true
  | [], s, h => ⟨fun _ hr => absurd hr (by simp), s, h⟩
  | r :: reps, s, h => by
    obtain ⟨h1, t, h2⟩ := npRow_spec H mask r (noPlaneK H mask ents kont reps) ents s h
    obtain ⟨h3, h4⟩ := noPlaneK_spec H mask ents kont reps t h2
    refine ⟨fun r' hr' => ?_, h4⟩
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact h1
    · exact h3 r' hr'

theorem lmK_spec {H : Hd} {kont : ℕ → List ℕ → Bool} {s : List ℕ} (h : lmK H kont s = true) :
    ∃ mask t, LMFacts H mask ∧ kont mask t = true := by
  obtain ⟨m, s1, h⟩ := rd_spec h
  obtain ⟨mask, reps, ents, s2, hI, h⟩ := entsK_spec H _ m 0 [] [] s1 h
    ⟨rfl, by simp, by simp, trivial⟩
  obtain ⟨hcl, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨hnp, t, h⟩ := noPlaneK_spec H mask ents (kont mask) reps s2 h
  exact ⟨mask, t, ⟨reps, ents, hI, hcl, hnp⟩, h⟩

theorem lmsK_spec (H : Hd) (m : ℕ) : ∀ (k : List ℕ → List ℕ → Bool) (s : List ℕ),
    lmsK H m k s = true → ∃ ms t, (∀ mask ∈ ms, LMFacts H mask) ∧ k ms t = true := by
  induction m with
  | zero => exact fun k s h => ⟨[], s, by simp, h⟩
  | succ m ih =>
    intro k s h
    obtain ⟨mask, s1, hF, h⟩ := lmK_spec h
    obtain ⟨ms, t, hms, h⟩ := ih _ s1 h
    refine ⟨mask :: ms, t, fun x hx => ?_, h⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hF
    · exact hms x hx

theorem wordsK_spec (H : Hd) (tm : ℕ) (kont : List ℕ → Bool) : ∀ (pts s : List ℕ),
    wordsK H tm kont pts s = true →
      (∀ a ∈ pts, ∃ w, inM H tm (word H w a) = true) ∧ ∃ t, kont t = true
  | [], s, h => ⟨by simp, s, h⟩
  | a :: pts, s, h => by
    obtain ⟨wl, s1, h⟩ := rd_spec h
    obtain ⟨w, s2, h⟩ := rdN_spec h
    obtain ⟨h1, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h2, h3⟩ := wordsK_spec H tm kont pts s2 h
    refine ⟨fun b hb => ?_, h3⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨w, h1⟩
    · exact h2 b hb

@[expose] def WitOK (H : Hd) (mu : ℕ) (mem : List ℕ) (t : ℕ) : Prop :=
  ∃ ps w, pairsOK H mem ps = true ∧ combo H mu ps ≠ 0 ∧ word H w (combo H mu ps) = t

theorem oneWit_spec {H : Hd} {mu : ℕ} {mem : List ℕ} {t : ℕ} {kont : List ℕ → Bool}
    {s : List ℕ} (h : oneWit H mu mem t kont s = true) : WitOK H mu mem t ∧ ∃ r, kont r = true := by
  obtain ⟨nco, s1, h⟩ := rd_spec h
  obtain ⟨ps, s2, h⟩ := rdN_spec h
  obtain ⟨wl, s3, h⟩ := rd_spec h
  obtain ⟨w, s4, h⟩ := rdN_spec h
  obtain ⟨h1, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨h2, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨h3, h4⟩ := (andB_eq_true _ _).mp h
  exact ⟨⟨ps, w, h1, Nat.ne_of_beq_eq_false ((notB_eq_true _).mp h2), Nat.eq_of_beq_eq_true h3⟩,
    s4, h4⟩

theorem witK_spec (H : Hd) (mu : ℕ) (mem : List ℕ) (mask : ℕ) (kont : List ℕ → Bool) :
    ∀ (tg s : List ℕ), witK H mu mem mask kont tg s = true →
      (∀ t ∈ tg, inM H mask t = false → WitOK H mu mem t) ∧ ∃ r, kont r = true
  | [], s, h => ⟨by simp, s, h⟩
  | t :: tg, s, h => by
    change Bool.rec (motive := fun _ => Bool) (oneWit H mu mem t (witK H mu mem mask kont tg) s)
      (witK H mu mem mask kont tg s) (inM H mask t) = true at h
    cases hb : inM H mask t with
    | false =>
      rw [hb] at h
      obtain ⟨hw, r, hr⟩ := oneWit_spec h
      obtain ⟨h1, h2⟩ := witK_spec H mu mem mask kont tg r hr
      refine ⟨fun t' ht' hb' => ?_, h2⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact hw
      · exact h1 t' ht' hb'
    | true =>
      rw [hb] at h
      obtain ⟨h1, h2⟩ := witK_spec H mu mem mask kont tg s h
      refine ⟨fun t' ht' hb' => ?_, h2⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · rw [hb] at hb'
        exact absurd hb' (by simp)
      · exact h1 t' ht' hb'

@[expose] def RowsOK (H : Hd) (mu : ℕ) (mem : List ℕ) : List ℕ → List (ℕ × ℕ × List ℕ) → Prop
  | _, [] => True
  | P, (vec, piv, ps) :: rows => vec = combo H mu ps ∧ pairsOK H mem ps = true ∧ piv < H.n ∧
      zL H vec piv = false ∧ zeroAt H P vec = true ∧ RowsOK H mu mem (piv :: P) rows

theorem rowsK_spec (H : Hd) (mu : ℕ) (mem : List ℕ) (kont : List ℕ → Bool) (k : ℕ) :
    ∀ (P s : List ℕ), rowsK H mu mem kont k P s = true →
      ∃ rows, rows.length = k ∧ RowsOK H mu mem P rows ∧ ∃ r, kont r = true := by
  induction k with
  | zero => exact fun P s h => ⟨[], rfl, trivial, s, h⟩
  | succ k ih =>
    intro P s h
    obtain ⟨vec, s1, h⟩ := rd_spec h
    obtain ⟨piv, s2, h⟩ := rd_spec h
    obtain ⟨nco, s3, h⟩ := rd_spec h
    obtain ⟨ps, s4, h⟩ := rdN_spec h
    obtain ⟨h1, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h2, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h3, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h4, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨h5, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨rows, hlen, hrows, r, hr⟩ := ih (piv :: P) s4 h
    exact ⟨(vec, piv, ps) :: rows, by simp [hlen], ⟨Nat.eq_of_beq_eq_true h1, h2,
      Nat.blt_eq.mp h3, (notB_eq_true _).mp h4, h5, hrows⟩, r, hr⟩

@[expose] def KindFacts (H : Hd) (tg ms : List ℕ) (mu : ℕ) (mem : List ℕ) (kind : ℕ) : Prop :=
  (kind = 0 ∧ ∃ v1 q1 v2 q2 v3 q3, kerOK H mem v1 q1 v2 q2 v3 q3 = true) ∨
  (kind = 1 ∧ ∃ rows, dimV H ≤ rows.length + 1 ∧ RowsOK H mu mem [] rows) ∨
  ∃ mask, (kind = 2 ∧ mask = 0 ∨ kind = 3 ∧ ∃ k, mask = nthM ms k) ∧
    ∀ t ∈ tg, inM H mask t = false → WitOK H mu mem t

theorem kindK_spec {H : Hd} {tg ms : List ℕ} {mu : ℕ} {mem : List ℕ} {kont : List ℕ → Bool}
    {kind : ℕ} {s : List ℕ} (h : kindK H tg ms mu mem kont kind s = true) :
    KindFacts H tg ms mu mem kind ∧ ∃ r, kont r = true := by
  unfold kindK at h
  cases h0 : Nat.beq kind 0 with
  | true =>
    rw [h0] at h
    obtain ⟨v1, s1, h⟩ := rd_spec h
    obtain ⟨q1, s2, h⟩ := rd_spec h
    obtain ⟨v2, s3, h⟩ := rd_spec h
    obtain ⟨q2, s4, h⟩ := rd_spec h
    obtain ⟨v3, s5, h⟩ := rd_spec h
    obtain ⟨q3, s6, h⟩ := rd_spec h
    obtain ⟨hk, h⟩ := (andB_eq_true _ _).mp h
    exact ⟨Or.inl ⟨Nat.eq_of_beq_eq_true h0, v1, q1, v2, q2, v3, q3, hk⟩, s6, h⟩
  | false =>
    rw [h0] at h
    cases h1 : Nat.beq kind 1 with
    | true =>
      rw [h1] at h
      obtain ⟨nr, s1, h⟩ := rd_spec h
      obtain ⟨hd, h⟩ := (andB_eq_true _ _).mp h
      obtain ⟨rows, hlen, hrows, r, hr⟩ := rowsK_spec H mu mem kont nr [] s1 h
      exact ⟨Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h1, rows,
        by rw [hlen]; exact Nat.le_of_ble_eq_true hd, hrows⟩), r, hr⟩
    | false =>
      rw [h1] at h
      cases h2 : Nat.beq kind 2 with
      | true =>
        rw [h2] at h
        obtain ⟨hw, r, hr⟩ := witK_spec H mu mem 0 kont tg s h
        exact ⟨Or.inr (Or.inr ⟨0, Or.inl ⟨Nat.eq_of_beq_eq_true h2, rfl⟩, hw⟩), r, hr⟩
      | false =>
        rw [h2] at h
        obtain ⟨h3, h⟩ := (andB_eq_true _ _).mp h
        obtain ⟨k, s1, h⟩ := rd_spec h
        obtain ⟨hw, r, hr⟩ := witK_spec H mu mem (nthM ms k) kont tg s1 h
        exact ⟨Or.inr (Or.inr ⟨_, Or.inr ⟨Nat.eq_of_beq_eq_true h3, k, rfl⟩, hw⟩), r, hr⟩

@[expose] def ClassOK (H : Hd) (tg ms : List ℕ) (mu phi : ℕ) (mem : List ℕ) (kind : ℕ) : Prop :=
  Nat.land (maskOf mem) phi = maskOf mem ∧ closedOK H phi (maskOf mem) mem = true ∧
    linkedOK H mem = true ∧ KindFacts H tg ms mu mem kind

theorem classK_spec {H : Hd} {tg ms : List ℕ} {mu phi acc : ℕ} {kont : ℕ → List ℕ → Bool}
    {s : List ℕ} (h : classK H tg ms mu phi acc kont s = true) :
    ∃ mem kind r, ClassOK H tg ms mu phi mem kind ∧ kont (Nat.lor acc (maskOf mem)) r = true := by
  obtain ⟨nm, s1, h⟩ := rd_spec h
  obtain ⟨mem, s2, h⟩ := rdN_spec h
  obtain ⟨kind, s3, h⟩ := rd_spec h
  obtain ⟨-, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨hsub, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨-, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨hcl, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨hlk, h⟩ := (andB_eq_true _ _).mp h
  obtain ⟨hk, r, hr⟩ := kindK_spec h
  exact ⟨mem, kind, r, ⟨Nat.eq_of_beq_eq_true hsub, hcl, hlk, hk⟩, hr⟩

theorem classesK_spec (H : Hd) (tg ms : List ℕ) (mu phi : ℕ) (kont : ℕ → List ℕ → Bool)
    (k : ℕ) : ∀ acc s, classesK H tg ms mu phi kont k acc s = true →
      ∃ cls : List (List ℕ × ℕ), (∀ c ∈ cls, ClassOK H tg ms mu phi c.1 c.2) ∧
        ∃ r, kont (cls.foldl (fun a c => Nat.lor a (maskOf c.1)) acc) r = true := by
  induction k with
  | zero => exact fun acc s h => ⟨[], by simp, s, h⟩
  | succ k ih =>
    intro acc s h
    obtain ⟨mem, kind, r, hc, h⟩ := classK_spec h
    obtain ⟨cls, hcls, r', h⟩ := ih _ r h
    refine ⟨(mem, kind) :: cls, fun c hc' => ?_, r', h⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact hc
    · exact hcls c hc'

@[expose] def CaseOK (H : Hd) (tg ms : List ℕ) (a : ℕ) : Prop :=
  ∃ phi, phiOK H a phi = true ∧ ∃ cls : List (List ℕ × ℕ),
    (∀ c ∈ cls, ClassOK H tg ms a phi c.1 c.2) ∧ ∀ r, memB phi r = true → ∃ c ∈ cls, r ∈ c.1

theorem muK_spec (H : Hd) (tg ms : List ℕ) : ∀ (pts s : List ℕ), muK H tg ms pts s = true →
    ∀ a ∈ pts, CaseOK H tg ms a
  | [], _, _ => by simp
  | a :: pts, s, h => by
    obtain ⟨mu, s1, h⟩ := rd_spec h
    obtain ⟨phi, s2, h⟩ := rd_spec h
    obtain ⟨nc, s3, h⟩ := rd_spec h
    obtain ⟨hmu, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨hphi, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨cls, hcls, r, h⟩ := classesK_spec H tg ms mu phi _ nc 0 s3 h
    obtain ⟨hacc, hrest⟩ := (andB_eq_true _ _).mp h
    have hmu' : mu = a := Nat.eq_of_beq_eq_true hmu
    subst hmu'
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨phi, hphi, cls, hcls, fun r hr => ?_⟩
      rw [← Nat.eq_of_beq_eq_true hacc] at hr
      rcases memB_foldl hr with h0 | h0
      · rw [memB_zero] at h0
        exact absurd h0 (by simp)
      · exact h0
    · exact muK_spec H tg ms pts r hrest b hb

@[expose] def TabFacts (H : Hd) (pts tg : List ℕ) : Prop :=
  tg = pts ∨ (allVec H tg = true ∧ ∀ a ∈ pts, ∃ w, inM H (maskL H tg) (word H w a) = true)

theorem bodyK_spec {H : Hd} {pts ms s : List ℕ} (h : bodyK H pts ms s = true) :
    ∃ tg, TabFacts H pts tg ∧ ∀ a ∈ pts, CaseOK H tg ms a := by
  obtain ⟨nt, s1, h⟩ := rd_spec h
  obtain ⟨T, s2, h⟩ := rdN_spec h
  beta_reduce at h
  cases h0 : Nat.beq nt 0 with
  | true =>
    rw [h0] at h
    exact ⟨pts, Or.inl rfl, muK_spec H pts ms pts s2 h⟩
  | false =>
    rw [h0] at h
    obtain ⟨hall, h⟩ := (andB_eq_true _ _).mp h
    obtain ⟨hw, r, hr⟩ := wordsK_spec H (maskL H T) _ pts s2 h
    exact ⟨T, Or.inr ⟨hall, hw⟩, muK_spec H T ms pts r hr⟩

@[expose] noncomputable def pkPts (H : Hd) (theta : List ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ) (alcNZ H.p H.n theta) (twV H.p) (tw H)

@[expose] def WalkFacts (H : Hd) (theta : List ℕ) : Prop :=
  ∃ ms, (∀ m ∈ ms, LMFacts H m) ∧ ∃ tg, TabFacts H (pkPts H theta) tg ∧
    ∀ a ∈ pkPts H theta, CaseOK H tg ms a

theorem restK_spec {H : Hd} {theta s : List ℕ} (h : restK H theta s = true) :
    WalkFacts H theta := by
  obtain ⟨nr, s1, h⟩ := rd_spec h
  obtain ⟨-, s2, h⟩ := rdN_spec h
  obtain ⟨nl, s3, h⟩ := rd_spec h
  obtain ⟨ms, s4, hms, h⟩ := lmsK_spec H nl _ s3 h
  obtain ⟨tg, ht, hc⟩ := bodyK_spec h
  exact ⟨ms, hms, tg, ht, hc⟩

theorem pkCheck_walk {theta D : List ℕ} {H : Hd} {s : List ℕ}
    (hD : ∀ k' : Hd → List ℕ → Bool, hdK k' D = k' H s) (h : pkCheck theta D = true) :
    WalkFacts H theta :=
  restK_spec ((hD (fun H s => restK H theta s)).symm.trans h)

end CFSG.KC.GGToral
