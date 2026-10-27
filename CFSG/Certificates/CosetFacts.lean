module

public import CFSG.Certificates.CosetEnumeration
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

@[expose] def reduceStep (L : ℕ) (inv : ℕ → ℕ) (st : List ℕ) (c : ℕ) : List ℕ :=
  cond (Nat.beq c L) st <|
    match st with
    | [] => [c]
    | d :: st' => cond (Nat.beq d (inv c)) st' (c :: d :: st')

@[expose] def freelyTrivial (L : ℕ) (inv : ℕ → ℕ) (w : List ℕ) : Bool :=
  (w.foldl (reduceStep L inv) []).isEmpty

theorem evalWord_append (gen : ℕ → G) (u v : List ℕ) :
    evalWord gen (u ++ v) = evalWord gen u * evalWord gen v := by
  simp [evalWord, List.map_append, List.prod_append]

theorem evalWord_of_foldl_reduceStep {gen : ℕ → G} {L : ℕ} {inv : ℕ → ℕ} (hε : gen L = 1)
    (hinv : ∀ c < L, gen (inv c) = (gen c)⁻¹) :
    ∀ (w : List ℕ) (st : List ℕ), (∀ c ∈ w, c ≤ L) →
      evalWord gen (w.foldl (reduceStep L inv) st).reverse = evalWord gen st.reverse *
        evalWord gen w := by
  intro w
  induction w with
  | nil => intro st _; simp
  | cons c w ih =>
    intro st hw
    have hc : c ≤ L := hw c (by simp)
    rw [List.foldl_cons, ih _ (fun c' hc' => hw c' (by simp [hc'])), evalWord_cons, ← mul_assoc]
    congr 1
    unfold reduceStep
    rcases Nat.lt_or_eq_of_le hc with hlt | heq
    · have hb : Nat.beq c L = false := by
        cases h : Nat.beq c L with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true h) (Nat.ne_of_lt hlt)
      rw [hb, Bool.cond_false]
      cases st with
      | nil => simp [evalWord]
      | cons d st' =>
        simp only
        cases h : Nat.beq d (inv c) with
        | false => simp [evalWord, List.reverse_cons, mul_assoc]
        | true =>
          have hd : d = inv c := Nat.eq_of_beq_eq_true h
          simp [evalWord, List.reverse_cons, hd, hinv c hlt, mul_assoc]
    · subst heq
      rw [show Nat.beq c c = true from Nat.beq_refl c, Bool.cond_true, hε, mul_one]

theorem evalWord_eq_one_of_freelyTrivial {gen : ℕ → G} {L : ℕ} {inv : ℕ → ℕ} (hε : gen L = 1)
    (hinv : ∀ c < L, gen (inv c) = (gen c)⁻¹) {w : List ℕ} (hw : ∀ c ∈ w, c ≤ L)
    (h : freelyTrivial L inv w = true) : evalWord gen w = 1 := by
  have key := evalWord_of_foldl_reduceStep hε hinv w [] hw
  unfold freelyTrivial at h
  rw [List.isEmpty_iff] at h
  rw [h] at key
  simpa using key.symm

@[expose] def refOK (fx fc fy inv : ℕ → ℕ) (f r cur c : ℕ) : Bool :=
  and (Nat.blt (Nat.div r 2) f) <|
    cond (Nat.beq (Nat.mod r 2) 0)
      (and (Nat.beq (fx (Nat.div r 2)) cur) (Nat.beq (fc (Nat.div r 2)) c))
      (and (Nat.beq (fy (Nat.div r 2)) cur) (Nat.beq (fc (Nat.div r 2)) (inv c)))

@[expose] def refNext (fx fy : ℕ → ℕ) (r : ℕ) : ℕ :=
  cond (Nat.beq (Nat.mod r 2) 0) (fy (Nat.div r 2)) (fx (Nat.div r 2))

@[expose] def walkOK (fx fc fy inv refs : ℕ → ℕ) (f t o s : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, cur, [] => Nat.beq cur s
  | q, cur, c :: w =>
    cond (Nat.beq q t)
      (and (and (Nat.beq (fx f) cur) (Nat.beq (fc f) c))
        (walkOK fx fc fy inv refs f t o s (Nat.succ q) (fy f) w))
      (and (refOK fx fc fy inv f (refs (Nat.add o q)) cur c)
        (walkOK fx fc fy inv refs f t o s (Nat.succ q) (refNext fx fy (refs (Nat.add o q))) w))

@[expose] def factOK (N L' : ℕ) (fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ)
    (rels subs : List (List ℕ)) (f : ℕ) : Bool :=
  and (Nat.blt (fx f) N) <| and (Nat.blt (fy f) N) <|
  match kind f with
  | 0 => and (Nat.beq (pl (fy f)) (Nat.add (Nat.mul (fx f) L') (fc f)))
      (and (Nat.blt (fc f) L') (Nat.blt (fx f) (fy f)))
  | 2 => and (Nat.blt (wi f) rels.length) <| and (Nat.blt (ft f) (wordAt rels (wi f)).length)
      (walkOK fx fc fy inv refs f (ft f) (fo f) (fs f) 0 (fs f) (wordAt rels (wi f)))
  | 3 => and (Nat.blt (wi f) subs.length) <| and (Nat.blt (ft f) (wordAt subs (wi f)).length)
      (walkOK fx fc fy inv refs f (ft f) (fo f) 0 0 0 (wordAt subs (wi f)))
  | _ => false

@[expose] def factsOK (N L' : ℕ) (fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ)
    (rels subs : List (List ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => and (factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo)
      (factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs (Nat.succ lo) n)

theorem factsOK_add (N L' : ℕ) (fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ)
    (rels subs : List (List ℕ)) (lo n m : ℕ) :
    factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo (n + m) =
      (factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo n &&
        factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs (lo + n) m) := by
  induction n generalizing lo with
  | zero => simp [factsOK]
  | succ n ih =>
    rw [Nat.succ_add, factsOK, factsOK, ih, Nat.succ_eq_add_one, Nat.add_right_comm,
      Bool.and_assoc]
    rfl

theorem factOK_of_factsOK {N L' : ℕ} {fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ}
    {rels subs : List (List ℕ)} {lo n : ℕ}
    (h : factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo n = true) :
    ∀ f, lo ≤ f → f < lo + n → factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs f = true := by
  induction n generalizing lo with
  | zero => intro f h1 h2; omega
  | succ n ih =>
    rw [factsOK, Bool.and_eq_true] at h
    intro f h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih h.2 f (Nat.succ_le_of_lt hlt) (by rw [Nat.succ_add]; exact h2)

section Walk

variable {gen : ℕ → G} {L' : ℕ} {pl fx fc fy inv refs : ℕ → ℕ}

noncomputable def factElt (gen : ℕ → G) (L' : ℕ) (pl fx fc fy : ℕ → ℕ) (f : ℕ) : G :=
  rep gen L' pl (fx f) * gen (fc f) * (rep gen L' pl (fy f))⁻¹

private theorem walk_cons_eq (gen : ℕ → G) (L' : ℕ) (pl : ℕ → ℕ) (cur c y s : ℕ) (w : List ℕ) :
    rep gen L' pl cur * evalWord gen (c :: w) * (rep gen L' pl s)⁻¹ =
      (rep gen L' pl cur * gen c * (rep gen L' pl y)⁻¹) *
        (rep gen L' pl y * evalWord gen w * (rep gen L' pl s)⁻¹) := by
  rw [evalWord_cons]; group

theorem ref_mem {H : Subgroup G} {f r cur c : ℕ}
    (htrue : ∀ g < f, factElt gen L' pl fx fc fy g ∈ H) (hc : gen (inv c) = (gen c)⁻¹)
    (h : refOK fx fc fy inv f r cur c = true) :
    rep gen L' pl cur * gen c * (rep gen L' pl (refNext fx fy r))⁻¹ ∈ H := by
  unfold refOK at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hlt, h⟩ := h
  have hg := htrue _ hlt
  unfold refNext
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · have hb : Nat.beq (Nat.mod r 2) 0 = true := by rw [Nat.beq_eq]; exact hr
    rw [hb, Bool.cond_true, Bool.and_eq_true] at h
    rw [hb, Bool.cond_true]
    rw [factElt, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2] at hg
    exact hg
  · have hb : Nat.beq (Nat.mod r 2) 0 = false := by
      cases hh : Nat.beq (Nat.mod r 2) 0 with
      | false => rfl
      | true =>
        have : r % 2 = 0 := Nat.eq_of_beq_eq_true hh
        omega
    rw [hb, Bool.cond_false, Bool.and_eq_true] at h
    rw [hb, Bool.cond_false]
    have := H.inv_mem hg
    rw [factElt, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2, hc] at this
    simpa [mul_assoc] using this

theorem walk_mem_of_lt {H : Subgroup G} {f t o s : ℕ}
    (htrue : ∀ g < f, factElt gen L' pl fx fc fy g ∈ H) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → t < q →
      rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ ∈ H := by
  intro w
  induction w with
  | nil =>
    intro q cur _ h _
    have hcur : cur = s := Nat.eq_of_beq_eq_true h
    subst hcur
    simp
  | cons c w ih =>
    intro q cur hw h htq
    simp only [walkOK] at h
    have hb : Nat.beq q t = false := by
      cases hh : Nat.beq q t with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
    rw [hb, Bool.cond_false, Bool.and_eq_true] at h
    obtain ⟨href, hrest⟩ := h
    rw [walk_cons_eq gen L' pl cur c (refNext fx fy (refs (Nat.add o q))) s w]
    exact H.mul_mem (ref_mem htrue (hw c (by simp)) href)
      (ih (Nat.succ q) _ (fun c' hc' => hw c' (by simp [hc'])) (by simpa using hrest) (by omega))

theorem walk_mem_iff {H : Subgroup G} {f t o s : ℕ}
    (htrue : ∀ g < f, factElt gen L' pl fx fc fy g ∈ H) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → q ≤ t → t < q + w.length →
      (rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ ∈ H ↔
        factElt gen L' pl fx fc fy f ∈ H) := by
  intro w
  induction w with
  | nil => intro q cur _ _ h1 h2; simp at h2; omega
  | cons c w ih =>
    intro q cur hw h hqt htl
    have hw' : ∀ c' ∈ w, gen (inv c') = (gen c')⁻¹ := fun c' hc' => hw c' (by simp [hc'])
    simp only [walkOK] at h
    rcases Nat.eq_or_lt_of_le hqt with rfl | hlt'
    · rw [show Nat.beq q q = true from Nat.beq_refl q, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hx, hc⟩, hrest⟩ := h
      have hx' := Nat.eq_of_beq_eq_true hx
      have hc' := Nat.eq_of_beq_eq_true hc
      have hr := walk_mem_of_lt (H := H) htrue w (Nat.succ q) (fy f) hw' (by simpa using hrest)
        (Nat.lt_succ_self q)
      rw [walk_cons_eq gen L' pl cur c (fy f) s w]
      have hfe : rep gen L' pl cur * gen c * (rep gen L' pl (fy f))⁻¹ =
          factElt gen L' pl fx fc fy f := by rw [factElt, hx', hc']
      rw [hfe]
      exact ⟨fun hm => by
        have h2 := H.mul_mem hm (H.inv_mem hr)
        rwa [mul_inv_cancel_right] at h2, fun hm => H.mul_mem hm hr⟩
    · have hb : Nat.beq q t = false := by
        cases hh : Nat.beq q t with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      rw [hb, Bool.cond_false, Bool.and_eq_true] at h
      obtain ⟨href, hrest⟩ := h
      have hg := ref_mem htrue (hw c (by simp)) href
      rw [walk_cons_eq gen L' pl cur c (refNext fx fy (refs (Nat.add o q))) s w,
        ← ih (Nat.succ q) _ hw' (by simpa using hrest) hlt' (by simp at htl; omega)]
      exact ⟨fun hm => by
        have h2 := H.mul_mem (H.inv_mem hg) hm
        rwa [inv_mul_cancel_left] at h2, fun hm => H.mul_mem hg hm⟩

end Walk

@[expose] def allTrivial (L : ℕ) (inv : ℕ → ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all fun w => and (freelyTrivial L inv w) (w.all fun c => Nat.blt c (Nat.succ L))

theorem evalWord_eq_one_of_allTrivial {gen : ℕ → G} {L : ℕ} {inv : ℕ → ℕ} (hε : gen L = 1)
    (hinv : ∀ c < L, gen (inv c) = (gen c)⁻¹) {ws : List (List ℕ)}
    (h : allTrivial L inv ws = true) : ∀ w ∈ ws, evalWord gen w = 1 := by
  intro w hw
  simp only [allTrivial, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h w hw
  exact evalWord_eq_one_of_freelyTrivial hε hinv (fun c hc => Nat.lt_succ_iff.mp (h2 c hc)) h1

@[expose] def stripEps (L : ℕ) (w : List ℕ) : List ℕ := w.filter fun c => !(Nat.beq c L)

theorem evalWord_stripEps {gen : ℕ → G} {L : ℕ} (hε : gen L = 1) (w : List ℕ) :
    evalWord gen (stripEps L w) = evalWord gen w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    by_cases hc : c = L
    · subst hc
      simp [stripEps, Nat.beq_refl, evalWord_cons, hε] at ih ⊢
      exact ih
    · have hb : Nat.beq c L = false := by
        cases h : Nat.beq c L with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true h) hc
      simp only [stripEps, List.filter_cons, hb, Bool.not_false, ite_true] at ih ⊢
      rw [evalWord_cons, evalWord_cons, ← ih]

@[expose] def isRotOf (w r : List ℕ) : Bool := (List.range r.length).any fun i => r.rotate i == w

@[expose] def derivedOK (L : ℕ) (inv : ℕ → ℕ) (base ws : List (List ℕ)) : Bool :=
  ws.all fun w => and (w.all fun c => Nat.blt c (Nat.succ L))
    (or (freelyTrivial L inv w) (base.any fun r => isRotOf (stripEps L w) r))

theorem evalWord_of_derivedOK {gen : ℕ → G} {L : ℕ} {inv : ℕ → ℕ} (hε : gen L = 1)
    (hinv : ∀ c < L, gen (inv c) = (gen c)⁻¹) {base ws : List (List ℕ)}
    (hbase : ∀ r ∈ base, evalWord gen r = 1) (h : derivedOK L inv base ws = true) :
    ∀ w ∈ ws, evalWord gen w = 1 := by
  intro w hw
  simp only [derivedOK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    Nat.blt_eq] at h
  obtain ⟨hlet, htriv | ⟨r, hr, hrot⟩⟩ := h w hw
  · exact evalWord_eq_one_of_freelyTrivial hε hinv (fun c hc => Nat.lt_succ_iff.mp (hlet c hc))
      htriv
  · rw [← evalWord_stripEps hε]
    simp only [isRotOf, List.any_eq_true, List.mem_range, beq_iff_eq] at hrot
    obtain ⟨i, _, hi⟩ := hrot
    rw [← hi, evalWord, List.map_rotate]
    exact List.prod_rotate_eq_one_of_prod_eq_one (hbase r hr) i

@[expose] def liveCount (live : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (liveCount live n) (cond (live n) 1 0)

theorem liveCount_eq (live : ℕ → Bool) (n : ℕ) :
    liveCount live n = ((Finset.range n).filter (fun i => live i = true)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [liveCount, Finset.range_add_one, Finset.filter_insert, Nat.add_eq, ih]
    cases h : live n
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

@[expose] def coverOK (N L F : ℕ) (fx fc fy inv ffi : ℕ → ℕ) (live : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 =>
    and (cond (live (Nat.div lo L))
        (and (refOK fx fc fy inv F (ffi lo) (Nat.div lo L) (Nat.mod lo L))
          (and (live (refNext fx fy (ffi lo))) (Nat.blt (refNext fx fy (ffi lo)) N)))
        true)
      (coverOK N L F fx fc fy inv ffi live (Nat.succ lo) n)

theorem coverOK_add (N L F : ℕ) (fx fc fy inv ffi : ℕ → ℕ) (live : ℕ → Bool) (lo n m : ℕ) :
    coverOK N L F fx fc fy inv ffi live lo (n + m) =
      (coverOK N L F fx fc fy inv ffi live lo n &&
        coverOK N L F fx fc fy inv ffi live (lo + n) m) := by
  induction n generalizing lo with
  | zero => simp [coverOK]
  | succ n ih =>
    rw [Nat.succ_add, coverOK, coverOK, ih, show Nat.succ lo + n = lo + (n + 1) by omega]
    exact (Bool.and_assoc _ _ _).symm

theorem cover_of_coverOK {N L F : ℕ} {fx fc fy inv ffi : ℕ → ℕ} {live : ℕ → Bool} {lo n : ℕ}
    (h : coverOK N L F fx fc fy inv ffi live lo n = true) :
    ∀ e, lo ≤ e → e < lo + n → live (e / L) = true →
      refOK fx fc fy inv F (ffi e) (e / L) (e % L) = true ∧
        live (refNext fx fy (ffi e)) = true ∧ refNext fx fy (ffi e) < N := by
  induction n generalizing lo with
  | zero => intro e h1 h2; omega
  | succ n ih =>
    rw [coverOK, Bool.and_eq_true] at h
    intro e h1 h2 hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have h0 := h.1
      rw [show live (Nat.div lo L) = true from hl, Bool.cond_true] at h0
      simp only [Bool.and_eq_true, Nat.blt_eq] at h0
      exact ⟨h0.1, h0.2.1, h0.2.2⟩
    · exact ih h.2 e (Nat.succ_le_of_lt hlt) (by rw [Nat.succ_add]; exact h2) hl

theorem index_le_of_facts {H : Subgroup G} {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi inv : ℕ → ℕ} {live : ℕ → Bool}
    {rels subs : List (List ℕ)}
    (hgen : Subgroup.closure (gen '' Set.Iio L) = ⊤)
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹) (hinvL : ∀ c < L, inv c < L)
    (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1) (hsubs : ∀ w ∈ subs, evalWord gen w ∈ H)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true)
    (hcover : coverOK N L F fx fc fy inv ffi live 0 (N * L) = true) :
    H.FiniteIndex ∧ H.index ≤ liveCount live N := by
  set L' := L + 1
  have hok : ∀ f < F, factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs f = true :=
    fun f hf => factOK_of_factsOK hfacts f (Nat.zero_le f) (by simpa using hf)
  have hwinv : ∀ w ∈ rels ++ subs, ∀ c ∈ w, gen (inv c) = (gen c)⁻¹ :=
    fun w hw c hc => hinv c (hlet w hw c hc)
  have htrue : ∀ f < F, factElt gen L' pl fx fc fy f ∈ H := by
    intro f
    induction f using Nat.strong_induction_on with
    | _ f ih =>
      intro hf
      have h := hok f hf
      unfold factOK at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨_, _, h⟩ := h
      have ih' : ∀ g < f, factElt gen L' pl fx fc fy g ∈ H :=
        fun g hg => ih g hg (lt_trans hg hf)
      split at h
      ·
        simp only [Bool.and_eq_true, Nat.blt_eq] at h
        obtain ⟨hpl, hcL, hxy⟩ := h
        have hpl' : pl (fy f) = fx f * L' + fc f := by simpa using Nat.eq_of_beq_eq_true hpl
        have hL0 : 0 < L' := by omega
        have hdiv : pl (fy f) / L' = fx f := by
          rw [hpl', Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt hcL,
            Nat.zero_add]
        have hmod : pl (fy f) % L' = fc f := by
          rw [hpl', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcL]
        have hy0 : 0 < fy f := lt_of_le_of_lt (Nat.zero_le _) hxy
        rw [factElt, rep_eq gen L' pl hy0 (by rw [hdiv]; exact hxy), hdiv, hmod]
        simp
      ·
        simp only [Bool.and_eq_true, Nat.blt_eq] at h
        obtain ⟨h1, h2, h3⟩ := h
        have hwm := wordAt_mem h1
        rw [← walk_mem_iff (H := H) ih' _ 0 (fs f) (hwinv _ (List.mem_append_left _ hwm)) h3
          (Nat.zero_le _) (by simpa using h2), hrels _ hwm]
        simp
      ·
        simp only [Bool.and_eq_true, Nat.blt_eq] at h
        obtain ⟨h1, h2, h3⟩ := h
        have hwm := wordAt_mem h1
        rw [← walk_mem_iff (H := H) ih' _ 0 0 (hwinv _ (List.mem_append_right _ hwm)) h3
          (Nat.zero_le _) (by simpa using h2), rep_zero]
        simpa using hsubs _ hwm
      · exact absurd h (by simp)
  have hstep : ∀ i < N, live i = true → ∀ c < L, ∀ x : G, x * (rep gen L' pl i)⁻¹ ∈ H →
      ∃ j < N, live j = true ∧ x * gen c * (rep gen L' pl j)⁻¹ ∈ H := by
    intro i hi hl c hc x hx
    have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le c) hc
    have he : i * L + c < N * L := by
      calc i * L + c < i * L + L := by omega
        _ = (i + 1) * L := by ring
        _ ≤ N * L := Nat.mul_le_mul_right _ hi
    have hdiv : (i * L + c) / L = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hc, Nat.zero_add]
    have hmod : (i * L + c) % L = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    obtain ⟨h1, h2, h3⟩ := cover_of_coverOK hcover (i * L + c) (Nat.zero_le _)
      (by simpa using he) (by rw [hdiv]; exact hl)
    rw [hdiv, hmod] at h1
    refine ⟨refNext fx fy (ffi (i * L + c)), h3, h2, ?_⟩
    have hfe := ref_mem htrue (hinv c (Nat.le_of_lt hc)) h1
    have := H.mul_mem hx hfe
    simpa [mul_assoc] using this
  have key : ∀ x : G, ∃ i < N, live i = true ∧ x * (rep gen L' pl i)⁻¹ ∈ H := by
    intro x
    have hx : x ∈ Subgroup.closure (gen '' Set.Iio L) := hgen ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨0, hN, hlive0, by simp [rep_zero]⟩
    | mul_right x _ y hy ih =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨i, hi, hl, hmem⟩ := ih
      exact hstep i hi hl c hc x hmem
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨i, hi, hl, hmem⟩ := ih
      rw [← hinv c (Nat.le_of_lt hc)]
      exact hstep i hi hl (inv c) (hinvL c hc) x hmem
  set S := (Finset.range N).filter (fun i => live i = true)
  have hsurj : Function.Surjective
      (fun i : S => (QuotientGroup.mk (rep gen L' pl i)⁻¹ : G ⧸ H)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨i, hi, hl, hmem⟩ := key y⁻¹
      refine ⟨⟨i, by simp [S, hi, hl]⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      have := H.inv_mem hmem
      simpa [mul_inv_rev] using this
  have hfin : Finite (G ⧸ H) := Finite.of_surjective _ hsurj
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  rw [Subgroup.index_eq_card, liveCount_eq]
  have := Nat.card_le_card_of_surjective _ hsurj
  simpa [Nat.card_eq_fintype_card] using this

end CFSG.Certificates.CosetEnumeration
