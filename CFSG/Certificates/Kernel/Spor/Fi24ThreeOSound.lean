module

public import Certificates.Data.Kernel.Spor.Fi24ThreeO
public import CFSG.Certificates.Kernel.Spor.Fi24KitSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound

public section

namespace CFSG.KS.Fi24ThreeO

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24Kit Finset

@[expose] def VN (NW : Nat → Nat → Nat) (NT : Nat → Nat) : Prop := NV NT ∧ ∀ j, NV (NW j)

@[expose] noncomputable def CF (NW : Nat → Nat → Nat) (NT : Nat → Nat) (c : Nat) : Nat → Nat :=
  if c = 26 then pF NT else LN NW c

@[expose] noncomputable def cP (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (x : Nat) :
    Nat :=
  cs.foldr (CF NW NT) x

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

theorem beq26 {c : Nat} (h : c = 26) : Nat.beq c 26 = true := by
  subst h
  rfl

theorem beq26' {c : Nat} (h : c ≠ 26) : Nat.beq c 26 = false := by
  cases e : Nat.beq c 26
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem apC_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) (c x : Nat) :
    apC NW NT c x = CF NW NT c x := by
  unfold apC CF
  by_cases h : c = 26
  · rw [beq26 h, if_pos h]
    exact ptF_eq _ x
  · rw [beq26' h, if_neg h]
    exact letN_eq _ _ _

theorem ptC_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) : ∀ (cs : List Nat) (x : Nat),
    ptC NW NT cs x = cP NW NT cs x
  | [], _ => rfl
  | c :: cs, x => by
    have e : ptC NW NT (c :: cs) x = apC NW NT c (ptC NW NT cs x) := Fi24NetPt.strictN_eq _ _
    rw [e, ptC_eq NW NT cs x, apC_eq]
    rfl

theorem cP_append (cs ds : List Nat) (x : Nat) :
    cP NW NT (cs ++ ds) x = cP NW NT cs (cP NW NT ds x) := by
  unfold cP
  rw [List.foldr_append]

theorem cP_cons (c : Nat) (cs : List Nat) (x : Nat) :
    cP NW NT (c :: cs) x = CF NW NT c (cP NW NT cs x) := rfl

theorem CF_lt (hV : VN NW NT) (c : Nat) {q : Nat} (hq : q < 524288) : CF NW NT c q < 524288 := by
  unfold CF
  split_ifs
  · exact pF_lt hV.1 hq
  · exact LN_lt (hV.2 _) hq

theorem cP_lt (hV : VN NW NT) : ∀ (cs : List Nat) {q : Nat}, q < 524288 → cP NW NT cs q < 524288
  | [], _, hq => hq
  | c :: cs, _, hq => CF_lt hV c (cP_lt hV cs hq)

theorem testBit_plC (hV : VN NW NT) (c v q : Nat) :
    (plC NW NT c v).testBit q = v.testBit (CF NW NT c q) := by
  unfold plC CF
  by_cases h : c = 26
  · rw [beq26 h, if_pos h]
    exact testBit_netF hV.1 v q
  · rw [beq26' h, if_neg h]
    exact testBit_planeL (hV.2 _) v q

theorem testBit_wkC (hV : VN NW NT) (cs : List Nat) (v : Nat) {q : Nat} (hq : q < 524288) :
    (wkC NW NT cs v).testBit q = v.testBit (cP NW NT cs q) :=
  CFSG.KS.Fi24FixP.testBit_walkP (A := plC NW NT) (σ := CF NW NT) cs
    (fun c _ q hq => CF_lt hV c hq) (fun c _ v q _ => testBit_plC hV c v q) v q hq

theorem testBit_fixC (hV : VN NW NT) (cs : List Nat) (x : Nat) :
    (fixC NW NT cs).testBit x = true ↔ x < 306936 ∧ cP NW NT cs x = x :=
  CFSG.KS.Fi24FixP.testBit_fixS (F := wkC NW NT cs) (g := cP NW NT cs)
    (fun v _ hq => testBit_wkC hV cs v hq) (fun _ hq => cP_lt hV cs hq) x

theorem testBit_plOf : ∀ (l : List Nat) (x : Nat), (plOf l).testBit x = true ↔ x ∈ l
  | [], x => by
    change (0 : Nat).testBit x = true ↔ _
    simp
  | y :: l, x => by
    change ((1 <<< y) ||| plOf l).testBit x = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_plOf l x, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.mem_cons, decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem ptsM_bit {x : Nat} (hx : x < 306936) : ptsM.testBit x = true := ptsM_testBit hx

theorem ptsM_bit' {x : Nat} (hx : ¬ x < 306936) : ptsM.testBit x = false := by
  unfold ptsM
  rw [CFSG.KS.Fi24FixP.testBit_ones]
  exact decide_eq_false hx

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL f l = true → ∀ a ∈ l, f a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 ha with e | e
    · rw [e]
      exact h1
    · exact allL_spec h2 a e

theorem allI_spec {α : Type} {f : Nat → α → Bool} : ∀ {l : List α} {i : Nat}, allI f l i = true →
    ∀ j (hj : j < l.length), f (i + j) l[j] = true
  | [], _, _, j, hj => absurd hj (by simp)
  | b :: l, i, h, j, hj => by
    obtain ⟨h1, h2⟩ := andB_true h
    cases j with
    | zero => exact h1
    | succ j =>
      have := allI_spec h2 j (by simpa using hj)
      rw [show i + (j + 1) = Nat.succ i + j by omega]
      exact this

theorem cubeOK_spec (hV : VN NW NT) {w : List Nat} (h : cubeOK NW NT w = true) :
    ∀ x < 306936, cP NW NT (w ++ (w ++ w)) x = x := by
  intro x hx
  have e : fixC NW NT (w ++ (w ++ w)) = ptsM := Nat.eq_of_beq_eq_true h
  have hb : (fixC NW NT (w ++ (w ++ w))).testBit x = true := by
    rw [e]
    exact ptsM_bit hx
  exact ((testBit_fixC hV _ x).1 hb).2

@[expose] def InW (ws : List (List Nat)) (v : List Nat) : Prop :=
  ∃ l : List (List Nat), (∀ w ∈ l, w ∈ ws) ∧ v = l.flatten

theorem InW.nil (ws : List (List Nat)) : InW ws [] := ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩

theorem InW.append {ws : List (List Nat)} {u v : List Nat} (hu : InW ws u) (hv : InW ws v) :
    InW ws (u ++ v) := by
  obtain ⟨l, hl, rfl⟩ := hu
  obtain ⟨m, hm, rfl⟩ := hv
  refine ⟨l ++ m, fun w h => ?_, by rw [List.flatten_append]⟩
  rcases List.mem_append.1 h with h | h
  · exact hl w h
  · exact hm w h

theorem InW.single {ws : List (List Nat)} {w : List Nat} (h : w ∈ ws) : InW ws w :=
  ⟨[w], fun w' h' => by rw [List.mem_singleton.1 h']; exact h, by simp⟩

theorem testBit_stepW (hV : VN NW NT) (S x : Nat) (hx : x < 524288) :
    ∀ {ws : List (List Nat)}, (stepW NW NT ws S).testBit x = true →
      S.testBit x = true ∨ ∃ w ∈ ws, S.testBit (cP NW NT w x) = true
  | [], h => Or.inl h
  | w :: ws, h => by
    have e : stepW NW NT (w :: ws) S = Nat.lor (wkC NW NT w S) (stepW NW NT ws S) :=
      Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, Bool.or_eq_true, testBit_wkC hV w S hx] at h
    rcases h with h | h
    · exact Or.inr ⟨w, List.mem_cons_self, h⟩
    · rcases testBit_stepW hV S x hx h with h' | ⟨w', hw', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨w', List.mem_cons_of_mem w hw', h'⟩

theorem stepW_of (S x : Nat) : ∀ {ws : List (List Nat)}, S.testBit x = true →
    (stepW NW NT ws S).testBit x = true
  | [], h => h
  | w :: ws, h => by
    have e : stepW NW NT (w :: ws) S = Nat.lor (wkC NW NT w S) (stepW NW NT ws S) :=
      Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, stepW_of S x h, Bool.or_true]

theorem iterW_spec (hV : VN NW NT) (ws : List (List Nat)) (S : Nat) :
    ∀ d x, x < 524288 → (iterW NW NT ws d S).testBit x = true →
      ∃ v, InW ws v ∧ S.testBit (cP NW NT v x) = true
  | 0, _, _, h => ⟨[], InW.nil ws, h⟩
  | d + 1, x, hx, h => by
    have e : iterW NW NT ws (d + 1) S = stepW NW NT ws (iterW NW NT ws d S) :=
      Fi24NetPt.strictN_eq _ _
    rw [e] at h
    rcases testBit_stepW hV _ x hx h with h1 | ⟨w, hw, h1⟩
    · exact iterW_spec hV ws S d x hx h1
    · obtain ⟨v, hv, hS⟩ := iterW_spec hV ws S d _ (cP_lt hV w hx) h1
      refine ⟨v ++ w, hv.append (InW.single hw), ?_⟩
      rw [cP_append]
      exact hS

theorem covW_spec (hV : VN NW NT) {ws : List (List Nat)} {d S F : Nat}
    (h : covW NW NT ws d S F = true) {x : Nat} (hx : x < 306936) :
    F.testBit x = true ∨ ∃ v, InW ws v ∧ S.testBit (cP NW NT v x) = true := by
  unfold covW at h
  have e : ((iterW NW NT ws d S ||| F) &&& ptsM).testBit x = ptsM.testBit x := by
    have e0 := Nat.eq_of_beq_eq_true h
    change (iterW NW NT ws d S ||| F) &&& ptsM = ptsM at e0
    rw [e0]
  rw [Nat.testBit_and, Nat.testBit_or, ptsM_bit hx, Bool.and_true, Bool.or_eq_true] at e
  rcases e with e | e
  · exact Or.inr (iterW_spec hV ws S d x (by omega) e)
  · exact Or.inl e

theorem stepW_mem (hV : VN NW NT) {P x : Nat} (hx : x < 524288) {w : List Nat}
    (hP : P.testBit (cP NW NT w x) = true) : ∀ {ws : List (List Nat)}, w ∈ ws →
      (stepW NW NT ws P).testBit x = true
  | [], hw' => absurd hw' List.not_mem_nil
  | w' :: ws', hw' => by
    have e' : stepW NW NT (w' :: ws') P = Nat.lor (wkC NW NT w' P) (stepW NW NT ws' P) :=
      Fi24NetPt.strictN_eq _ _
    rw [e', nlor, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 hw' with h' | h'
    · subst h'
      exact Or.inl (by rw [testBit_wkC hV _ P hx]; exact hP)
    · exact Or.inr (stepW_mem hV hx hP h')

theorem stepS_keep {y : Nat} : ∀ (ls : List Nat) (S : Nat), S.testBit y = true →
    (stepS NW ls S).testBit y = true
  | [], _, hS => hS
  | l :: ls', S, hS => by
    change (Nat.lor (planeL NW l S) (stepS NW ls' S)).testBit y = true
    rw [nlor, Nat.testBit_or, stepS_keep ls' S hS, Bool.or_true]

theorem iterS_keep {y : Nat} (ls : List Nat) (S : Nat) (hS : S.testBit y = true) :
    ∀ d, (iterS NW ls d S).testBit y = true
  | 0 => hS
  | d + 1 => by
    have e : iterS NW ls (d + 1) S = stepS NW ls (iterS NW ls d S) := Fi24NetPt.strictN_eq _ _
    rw [e]
    exact stepS_keep ls _ (iterS_keep ls S hS d)

theorem stepS_mem (hV : VN NW NT) {P x l : Nat} (hP : P.testBit (LN NW l x) = true) :
    ∀ {ls : List Nat}, l ∈ ls → (stepS NW ls P).testBit x = true
  | [], h' => absurd h' List.not_mem_nil
  | l' :: ls', h' => by
    change (Nat.lor (planeL NW l' P) (stepS NW ls' P)).testBit x = true
    rw [nlor, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h' with h'' | h''
    · subst h''
      exact Or.inl (by rw [testBit_planeL (hV.2 _)]; exact hP)
    · exact Or.inr (stepS_mem hV hP h'')

theorem closW_spec (hV : VN NW NT) {ws : List (List Nat)} {P : Nat} (h : closW NW NT ws P = true)
    {x : Nat} (hx : x < 524288) {w : List Nat} (hw : w ∈ ws) (hP : P.testBit (cP NW NT w x) = true) :
    P.testBit x = true := by
  have e : stepW NW NT ws P = P := Nat.eq_of_beq_eq_true h
  rw [← e]
  exact stepW_mem hV hx hP hw

theorem itN_eq (f : Nat → Nat) : ∀ n p, itN f n p = f^[n] p
  | 0, _ => rfl
  | n + 1, p => by
    have e : itN f (n + 1) p = f (itN f n p) := Fi24NetPt.strictN_eq _ _
    rw [e, itN_eq f n p, Function.iterate_succ_apply']

theorem cycK_spec {f : Nat → Nat} {p L : Nat} (h : cycK f p L = true) :
    L % 3 = 0 ∧ L ≠ 0 ∧ f^[L] p = p ∧ f^[L / 3] p ≠ p := by
  unfold cycK at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  refine ⟨Nat.eq_of_beq_eq_true h1, fun e => ?_, ?_, fun e => ?_⟩
  · rw [e] at h3
    exact absurd h3 (by decide)
  · rw [← itN_eq]
    exact Nat.eq_of_beq_eq_true h5
  · have e' : itN f (L / 3) p = p := by rw [itN_eq]; exact e
    change notB (Nat.beq (itN f (L / 3) p) p) = true at h6
    rw [e', Nat.beq_refl] at h6
    exact absurd h6 (by decide)

theorem uP_eq (k p : Nat) {OL : Nat → Nat} :
    uP NW OL NT k p = clsK OL NT k (clsK OL NT (LN NW 2 k) (clsK OL NT (LN NW 2 (LN NW 2 k)) p)) := by
  unfold uP
  simp only [Fi24NetPt.strictN_eq, letN_eq]

theorem orbOK_spec (hV : VN NW NT) {ls : List Nat} {d y c : Nat} (h : orbOK NW ls d y c = true) :
    ∃ P : Nat, P.testBit y = true ∧
      (∀ x, P.testBit x = true → ∃ v : List Nat, (∀ l ∈ v, l ∈ ls) ∧ wN NW v x = y) ∧
      (∀ x < 524288, ∀ l ∈ ls, P.testBit (LN NW l x) = true → P.testBit x = true) ∧
      #((range 524288).filter (fun x => P.testBit x = true)) = c := by
  unfold orbOK at h
  rw [letB_eq'] at h
  obtain ⟨h1, h2⟩ := andB_true h
  set P := iterS NW ls d (Nat.shiftLeft 1 y) with hP
  have hWV : WV NW ls := fun l _ => hV.2 _
  have h1y : (Nat.shiftLeft 1 y).testBit y = true := by
    rw [nshl, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
  refine ⟨P, iterS_keep ls _ h1y d, fun x hx => ?_, fun x _ l hl hPl => ?_, ?_⟩
  · obtain ⟨v, hv, hS⟩ := iterS_spec hWV _ d x hx
    refine ⟨v, hv, ?_⟩
    change (Nat.shiftLeft 1 y).testBit _ = true at hS
    rw [nshl, Nat.one_shiftLeft, Nat.testBit_two_pow] at hS
    exact (of_decide_eq_true hS).symm
  · have e : stepS NW ls P = P := Nat.eq_of_beq_eq_true h1
    rw [← e]
    exact stepS_mem hV hPl hl
  · have e := Nat.eq_of_beq_eq_true h2
    rw [CFSG.KS.Fi24FixP.popcount_19, CFSG.KS.Fi24FixP.sum_bits] at e
    exact e

private theorem swp_fix_hi {S d m : Nat} (h : ValidIn S d m) {q : Nat} (hq : S ≤ q) :
    swp d m q = q := by
  have h1 : ¬ m.testBit q = true := fun e => by
    have := (h q e).1
    omega
  have h2 : ¬ (d ≤ q ∧ m.testBit (q - d) = true) := fun ⟨hd, e⟩ => by
    have := (h (q - d) e).1
    omega
  unfold swp
  rw [if_neg h1, if_neg h2]

private theorem pF_fix_hi {M : Nat → Nat} (h : NV M) {q : Nat} (hq : 524288 ≤ q) : pF M q = q :=
  compF_fix (τ := fun l => swp (ldist l) (M l)) (c := 37) (fun i hi => swp_fix_hi (h i hi) hq)
    0 37 (Nat.le_refl _)

private theorem pR_fix_hi {M : Nat → Nat} (h : NV M) {q : Nat} (hq : 524288 ≤ q) : pR M q = q :=
  compF_fix (τ := fun l => swp (ldist (36 - l)) (M (36 - l))) (c := 37)
    (fun i hi => swp_fix_hi (h (36 - i) (by omega)) hq) 0 37 (Nat.le_refl _)

private theorem CF_fix_hi (hV : VN NW NT) (c : Nat) {q : Nat} (hq : 524288 ≤ q) :
    CF NW NT c q = q := by
  unfold CF
  split_ifs
  · exact pF_fix_hi hV.1 hq
  · unfold LN
    split_ifs
    · exact pF_fix_hi (hV.2 _) hq
    · exact pR_fix_hi (hV.2 _) hq

private theorem testBit_wkC_ge (hV : VN NW NT) : ∀ (cs : List Nat) (v : Nat) {q : Nat},
    524288 ≤ q → (wkC NW NT cs v).testBit q = v.testBit q
  | [], _, _, _ => rfl
  | c :: cs, v, q, hq => by
    have e : wkC NW NT (c :: cs) v = wkC NW NT cs (plC NW NT c v) :=
      CFSG.KS.Fi24NetPt.strictN_eq _ _
    rw [e, testBit_wkC_ge hV cs _ hq, testBit_plC hV, CF_fix_hi hV c hq]

private theorem wkC_hi (hV : VN NW NT) (cs : List Nat) {v : Nat}
    (hv : ∀ i, 524288 ≤ i → v.testBit i = false) :
    ∀ i, 524288 ≤ i → (wkC NW NT cs v).testBit i = false := fun i hi => by
  rw [testBit_wkC_ge hV cs v hi]
  exact hv i hi

private theorem idPl19_hi {k : Nat} (hk : k < 19) :
    ∀ i, 524288 ≤ i → (CFSG.KC.Fi24FixP.idPl19 k).testBit i = false := fun i hi => by
  rw [CFSG.KS.Fi24FixP.testBit_idPl19 hk, decide_eq_false (by omega : ¬ i < 524288),
    Bool.false_and]

private theorem xor_hi {a b : Nat} (ha : ∀ i, 524288 ≤ i → a.testBit i = false)
    (hb : ∀ i, 524288 ≤ i → b.testBit i = false) :
    ∀ i, 524288 ≤ i → (Nat.xor a b).testBit i = false := fun i hi => by
  rw [nxor, Nat.testBit_xor, ha i hi, hb i hi, Bool.xor_false]

private theorem testBit_stack {P0 : Nat} {Q : Nat → Nat} {x : Nat} (hx : x < 524288) (j : Nat) :
    ∀ n, (∀ b, 524288 ≤ b → P0.testBit b = false) →
    (∀ i < n, ∀ b, 524288 ≤ b → (Q i).testBit b = false) →
    (Nat.rec (motive := fun _ => Nat) P0 (fun k acc => strictN acc (fun a => Nat.lor a
      (Nat.shiftLeft (Q k) (Nat.mul (Nat.succ k) 524288)))) n).testBit (j * 524288 + x) =
      (decide (j ≤ n) && (if j = 0 then P0 else Q (j - 1)).testBit x)
  | 0, hP0, _ => by
    change P0.testBit (j * 524288 + x) = _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [Nat.zero_mul, Nat.zero_add, decide_eq_true (Nat.le_refl 0), Bool.true_and,
        if_pos (rfl : (0 : Nat) = 0)]
    · rw [hP0 _ (by omega : 524288 ≤ j * 524288 + x), decide_eq_false (by omega : ¬ j ≤ 0),
        Bool.false_and]
  | n + 1, hP0, hQ => by
    have e : (Nat.rec (motive := fun _ => Nat) P0 (fun k acc => strictN acc (fun a => Nat.lor a
        (Nat.shiftLeft (Q k) (Nat.mul (Nat.succ k) 524288)))) (n + 1)) =
        Nat.lor (Nat.rec (motive := fun _ => Nat) P0 (fun k acc => strictN acc (fun a => Nat.lor a
          (Nat.shiftLeft (Q k) (Nat.mul (Nat.succ k) 524288)))) n)
          (Nat.shiftLeft (Q n) (Nat.mul (n + 1) 524288)) :=
      CFSG.KS.Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, testBit_stack hx j n hP0 (fun i hi => hQ i (by omega)), nshl,
      Nat.testBit_shiftLeft, nmul]
    rcases Nat.lt_trichotomy j (n + 1) with hj | rfl | hj
    · rw [decide_eq_true (by omega : j ≤ n), decide_eq_true (by omega : j ≤ n + 1),
        decide_eq_false (by omega : ¬ j * 524288 + x ≥ (n + 1) * 524288), Bool.false_and,
        Bool.or_false]
    · rw [decide_eq_false (by omega : ¬ n + 1 ≤ n), decide_eq_true (Nat.le_refl (n + 1)),
        decide_eq_true (by omega : (n + 1) * 524288 + x ≥ (n + 1) * 524288),
        if_neg (by omega : n + 1 ≠ 0), Nat.add_sub_cancel, Nat.add_sub_cancel_left,
        Bool.false_and, Bool.false_or]
    · rw [hQ n (by omega) _ (by omega : 524288 ≤ j * 524288 + x - (n + 1) * 524288),
        decide_eq_false (by omega : ¬ j ≤ n), decide_eq_false (by omega : ¬ j ≤ n + 1),
        Bool.false_and, Bool.and_false, Bool.false_or]

private theorem testBit_pk19 (hV : VN NW NT) (cs : List Nat) {x : Nat} (hx : x < 524288) {j : Nat}
    (hj : j < 19) : (pk19 NW NT cs).testBit (j * 524288 + x) = (cP NW NT cs x).testBit j := by
  have hP0 := wkC_hi hV cs (idPl19_hi (k := 0) (by decide))
  have hQ : ∀ i < 18, ∀ b, 524288 ≤ b → (Nat.xor (wkC NW NT cs (Nat.xor
      (CFSG.KC.Fi24FixP.idPl19 (Nat.succ i)) (CFSG.KC.Fi24FixP.idPl19 0)))
      (wkC NW NT cs (CFSG.KC.Fi24FixP.idPl19 0))).testBit b = false := fun i hi =>
    xor_hi (wkC_hi hV cs (xor_hi (idPl19_hi (by omega)) (idPl19_hi (by decide)))) hP0
  unfold pk19
  rw [CFSG.KS.Fi24NetPt.strictN_eq]
  refine (testBit_stack (P0 := wkC NW NT cs (CFSG.KC.Fi24FixP.idPl19 0))
    (Q := fun i => Nat.xor (wkC NW NT cs (Nat.xor (CFSG.KC.Fi24FixP.idPl19 (Nat.succ i))
      (CFSG.KC.Fi24FixP.idPl19 0))) (wkC NW NT cs (CFSG.KC.Fi24FixP.idPl19 0)))
    hx j 18 hP0 hQ).trans ?_
  rw [decide_eq_true (by omega : j ≤ 18), Bool.true_and]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos (rfl : (0 : Nat) = 0), testBit_wkC hV cs _ hx,
      CFSG.KS.Fi24FixP.testBit_idPl19 (k := 0) (by decide), decide_eq_true (cP_lt hV cs hx),
      Bool.true_and]
  · have hj' : Nat.succ (j - 1) = j := by omega
    rw [if_neg (by omega : j ≠ 0)]
    show (Nat.xor (wkC NW NT cs (Nat.xor (CFSG.KC.Fi24FixP.idPl19 (Nat.succ (j - 1)))
      (CFSG.KC.Fi24FixP.idPl19 0))) (wkC NW NT cs (CFSG.KC.Fi24FixP.idPl19 0))).testBit x = _
    rw [nxor, Nat.testBit_xor, testBit_wkC hV cs _ hx, testBit_wkC hV cs _ hx, nxor,
      Nat.testBit_xor, hj', CFSG.KS.Fi24FixP.testBit_idPl19 hj,
      CFSG.KS.Fi24FixP.testBit_idPl19 (k := 0) (by decide), decide_eq_true (cP_lt hV cs hx),
      Bool.true_and, Bool.true_and, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

private theorem diffP_loop {D x : Nat} : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => strictN acc (fun a => Nat.lor a
      (Nat.land (Nat.shiftRight D (Nat.mul k 524288)) (ones 524288)))) n).testBit x = true →
    ∃ k < n, D.testBit (k * 524288 + x) = true
  | 0, h => by
    change (0 : Nat).testBit x = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h (by decide)
  | n + 1, h => by
    have e : (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => strictN acc (fun a => Nat.lor a
        (Nat.land (Nat.shiftRight D (Nat.mul k 524288)) (ones 524288)))) (n + 1)) =
        Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => strictN acc (fun a => Nat.lor a
          (Nat.land (Nat.shiftRight D (Nat.mul k 524288)) (ones 524288)))) n)
          (Nat.land (Nat.shiftRight D (Nat.mul n 524288)) (ones 524288)) :=
      CFSG.KS.Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, hD⟩ := diffP_loop n h
      exact ⟨k, by omega, hD⟩
    · rw [nland, Nat.testBit_and, nshr, Nat.testBit_shiftRight, nmul, Bool.and_eq_true] at h
      exact ⟨n, by omega, h.1⟩

private theorem diffP_spec {P Q x : Nat} (h : (diffP P Q).testBit x = true) :
    ∃ k < 19, P.testBit (k * 524288 + x) ≠ Q.testBit (k * 524288 + x) := by
  unfold diffP at h
  rw [CFSG.KS.Fi24NetPt.strictN_eq] at h
  obtain ⟨k, hk, hD⟩ := diffP_loop 19 h
  refine ⟨k, hk, fun e => ?_⟩
  rw [nxor, Nat.testBit_xor, e, Bool.xor_self] at hD
  exact absurd hD (by decide)

private theorem ne_of_diffP_pk19 (hV : VN NW NT) {cs ds : List Nat} {x : Nat} (hx : x < 524288)
    (h : (diffP (pk19 NW NT cs) (pk19 NW NT ds)).testBit x = true) :
    cP NW NT cs x ≠ cP NW NT ds x := by
  obtain ⟨k, hk, hne⟩ := diffP_spec h
  rw [testBit_pk19 hV cs hx hk, testBit_pk19 hV ds hx hk] at hne
  exact fun e => hne (by rw [e])

private theorem offS_spec (hV : VN NW NT) {cg cs : List Nat} {x : Nat}
    (h : (offS NW NT cg cs).testBit x = true) :
    x < 306936 ∧ cP NW NT cg x ≠ x ∧ cP NW NT cg x ≠ cP NW NT cs x ∧
      cP NW NT cg x ≠ cP NW NT (cs ++ cs) x := by
  unfold offS at h
  rw [CFSG.KS.Fi24NetPt.strictN_eq, nland, nland, nland, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2, h3⟩ := h
  have hx : x < 306936 := by
    rcases Nat.lt_or_ge x 306936 with hx | hx
    · exact hx
    · rw [ptsM_bit' (by omega : ¬ x < 306936)] at h0
      exact absurd h0 (by decide)
  have hx' : x < 524288 := by omega
  exact ⟨hx, ne_of_diffP_pk19 hV hx' h1, ne_of_diffP_pk19 hV hx' h2, ne_of_diffP_pk19 hV hx' h3⟩

private theorem ne_of_notB_beq {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

private theorem testBit_of_bitN {m i : Nat} (h : Nat.beq (bitN m i) 1 = true) :
    m.testBit i = true := by
  rw [← CFSG.KS.Fi24NetPt.bit_eq m i]
  exact h

private theorem testBit_eq_of_bitN {m n i j : Nat} (h : Nat.beq (bitN m i) (bitN n j) = true) :
    m.testBit i = n.testBit j := by
  rw [← CFSG.KS.Fi24NetPt.bit_eq m i, ← CFSG.KS.Fi24NetPt.bit_eq n j]
  exact congrArg (fun t => Nat.beq t 1) (Nat.eq_of_beq_eq_true h)

private theorem testBit_pl3 {x : Nat} : ∀ {ep : List (Nat × Nat × Nat)},
    (pl3 ep).testBit x = true → ∃ e ∈ ep, e.1 = x
  | [], h => by
    change (0 : Nat).testBit x = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h (by decide)
  | e :: ep, h => by
    change ((1 <<< e.1) ||| pl3 ep).testBit x = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, of_decide_eq_true h⟩
    · obtain ⟨e', he', h'⟩ := testBit_pl3 h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

private theorem testBit_recLor {β : Type} (B : Nat) (F : β → Nat) {k : Nat} : ∀ (l : List β),
    (List.rec (motive := fun _ => Nat) B (fun p _ ih => strictN ih (fun a => Nat.lor a (F p)))
      l).testBit k = true → B.testBit k = true ∨ ∃ p ∈ l, (F p).testBit k = true
  | [], h => Or.inl h
  | p :: l, h => by
    have e : (List.rec (motive := fun _ => Nat) B
        (fun p _ ih => strictN ih (fun a => Nat.lor a (F p))) (p :: l)) =
        Nat.lor (List.rec (motive := fun _ => Nat) B
          (fun p _ ih => strictN ih (fun a => Nat.lor a (F p))) l) (F p) :=
      CFSG.KS.Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases testBit_recLor B F l h with h | ⟨q, hq, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h⟩
    · exact Or.inr ⟨p, List.mem_cons_self, h⟩

private theorem testBit_of_land_ptsM {A k : Nat} (h : Nat.land A ptsM = ptsM) (hk : k < 306936) :
    A.testBit k = true := by
  have e : (Nat.land A ptsM).testBit k = ptsM.testBit k := by rw [h]
  rw [nland, Nat.testBit_and, ptsM_bit hk, Bool.and_true] at e
  exact e

private theorem testBit_plG {k : Nat} : ∀ {gq : List (Nat × List Nat)},
    (plG gq).testBit k = true → ∃ g ∈ gq, k ∈ g.2
  | [], h => by
    change (0 : Nat).testBit k = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h (by decide)
  | g :: gq, h => by
    have e : plG (g :: gq) = Nat.lor (plOf g.2) (plG gq) := CFSG.KS.Fi24NetPt.strictN_eq _ _
    rw [e, nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨g, List.mem_cons_self, (testBit_plOf g.2 k).1 h⟩
    · obtain ⟨g', hg', hk⟩ := testBit_plG h
      exact ⟨g', List.mem_cons_of_mem _ hg', hk⟩

private theorem lenL_length {α : Type} : ∀ (l : List α), lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_length l)

private theorem keyList_eq : ∀ (gq : List (Nat × List Nat)),
    List.rec (motive := fun _ => List Nat) List.nil (fun g _ ih => g.1 :: ih) gq = gq.map Prod.fst
  | [] => rfl
  | g :: gq => congrArg (List.cons g.1) (keyList_eq gq)

private theorem incLoop_ge : ∀ (l : List Nat) {p : Nat}, List.rec (motive := fun _ => Nat → Bool)
    (fun _ => true) (fun a _ ih p => andB (Nat.ble p a) (ih (Nat.succ a))) l p = true →
    ∀ x ∈ l, p ≤ x
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, p, h, x, hx => by
    obtain ⟨h1, h2⟩ := andB_true h
    have hpa := Nat.le_of_ble_eq_true h1
    rcases List.mem_cons.1 hx with e | e
    · rw [e]
      exact hpa
    · have := incLoop_ge l h2 x e
      omega

private theorem incLoop_key_inj : ∀ (gq : List (Nat × List Nat)) {p : Nat},
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun a _ ih p => andB (Nat.ble p a) (ih (Nat.succ a))) (gq.map Prod.fst) p = true →
    ∀ g ∈ gq, ∀ g' ∈ gq, g.1 = g'.1 → g = g'
  | [], _, _, g, hg, _, _, _ => absurd hg List.not_mem_nil
  | a :: gq, p, h, g, hg, g', hg', e => by
    obtain ⟨_, h2⟩ := andB_true h
    have hge : ∀ x ∈ gq, a.1 < x.1 := fun x hx => by
      have := incLoop_ge (gq.map Prod.fst) h2 x.1 (List.mem_map_of_mem hx)
      omega
    rcases List.mem_cons.1 hg with hg | hg <;> rcases List.mem_cons.1 hg' with hg' | hg'
    · rw [hg, hg']
    · rw [hg] at e
      exact absurd e (Nat.ne_of_lt (hge g' hg'))
    · rw [hg'] at e
      exact absurd e.symm (Nat.ne_of_lt (hge g hg))
    · exact incLoop_key_inj gq h2 g hg g' hg' e

private theorem ncL_spec {OL : Nat → Nat} : ∀ {l : List Nat}, ncL OL NT l = true →
    ∀ {a b : Nat}, a ∈ l → b ∈ l → a ≠ b → clsK OL NT a b ≠ b ∨ clsK OL NT b a ≠ a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hab => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha]
      exact Or.inl (ne_of_notB_beq (CFSG.KS.Fi24ThreeO.allL_spec h1 b hb))
    · rw [hb]
      exact Or.inr (ne_of_notB_beq (CFSG.KS.Fi24ThreeO.allL_spec h1 a ha))
    · exact ncL_spec h2 ha hb hab

private theorem exists_testBit_ne_of_ne {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (hne : x ≠ y) : ∃ j < n, x.testBit j ≠ y.testBit j := by
  refine Classical.byContradiction fun hc => hne (Nat.eq_of_testBit_eq fun i => ?_)
  rcases Nat.lt_or_ge i n with hi | hi
  · exact Classical.byContradiction fun hi' => hc ⟨i, hi, hi'⟩
  · have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy h2)]

private theorem exists_testBit_false_of_ne {x n : Nat} (hx : x < 2 ^ n) (hne : x ≠ 2 ^ n - 1) :
    ∃ j < n, x.testBit j = false := by
  refine Classical.byContradiction fun hc => hne (Nat.eq_of_testBit_eq fun i => ?_)
  rw [Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [decide_eq_true hi]
    cases e : x.testBit i
    · exact absurd ⟨i, hi, e⟩ hc
    · rfl
  · have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [decide_eq_false (by omega : ¬ i < n), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2)]

private theorem shl_one_eq (n : Nat) : Nat.shiftLeft (nat_lit 1) n = 2 ^ n := Nat.one_shiftLeft n

theorem sepOK_spec (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {tw : List (List Nat)}
    {gq : List (Nat × List Nat)} (h : sepOK NW NT OL w tw gq = true) :
    (∀ W ∈ tw, (fixC NW NT w).testBit (cP NW NT W 0) = true) ∧
    (∀ k k', (fixC NW NT w).testBit k = true → (fixC NW NT w).testBit k' = true → k ≠ k' →
      (∃ W ∈ tw, (fixC NW NT [26]).testBit (cP NW NT (invC W) k) ≠
          (fixC NW NT [26]).testBit (cP NW NT (invC W) k')) ∨
        clsK OL NT k k' ≠ k' ∨ clsK OL NT k' k ≠ k) ∧
    (∀ k, (fixC NW NT w).testBit k = true →
      ∃ W ∈ tw, (fixC NW NT [26]).testBit (cP NW NT (invC W) k) = false) := by
  unfold sepOK at h
  rw [letB_eq', letB_eq', letB_eq'] at h
  obtain ⟨hT, h⟩ := andB_true h
  obtain ⟨hK, h⟩ := andB_true h
  obtain ⟨hM, h⟩ := andB_true h
  obtain ⟨hG, h⟩ := andB_true h
  obtain ⟨hP, hW⟩ := andB_true h
  have hFS : ∀ k, (fixC NW NT w).testBit k = true → k < 524288 ∧ ∃ g ∈ gq, k ∈ g.2 := by
    intro k hk
    have hk3 := ((testBit_fixC hV w k).1 hk).1
    refine ⟨by omega, testBit_plG ?_⟩
    rw [Nat.eq_of_beq_eq_true hP]
    exact hk
  have hkey : ∀ g ∈ gq, g.1 < 2 ^ tw.length ∧ g.1 ≠ 2 ^ tw.length - 1 := by
    intro g hg
    obtain ⟨m1, m2⟩ := andB_true (CFSG.KS.Fi24ThreeO.allL_spec hM g hg)
    have m1' := Nat.blt_eq.mp m1
    have m2' := ne_of_notB_beq m2
    rw [shl_one_eq, lenL_length] at m1'
    rw [shl_one_eq, lenL_length] at m2'
    exact ⟨m1', m2'⟩
  have hbit : ∀ g ∈ gq, ∀ k ∈ g.2, k < 524288 → ∀ j (hj : j < tw.length),
      (fixC NW NT [26]).testBit (cP NW NT (invC tw[j]) k) = g.1.testBit j := by
    intro g hg k hk hk5 j hj
    have h1 := CFSG.KS.Fi24ThreeO.allI_spec hT j hj
    rw [letB_eq'] at h1
    have h2 := CFSG.KS.Fi24ThreeO.allL_spec h1 g hg
    rw [letB_eq'] at h2
    have h3 : (ctP NW NT (fixC NW NT [26]) tw[j]).testBit k = g.1.testBit (0 + j) :=
      testBit_eq_of_bitN (CFSG.KS.Fi24ThreeO.allL_spec h2 k hk)
    rw [Nat.zero_add] at h3
    exact (testBit_wkC hV (invC tw[j]) (fixC NW NT [26]) hk5).symm.trans h3
  refine ⟨fun W hW' => ?_, fun k k' hk hk' hne => ?_, fun k hk => ?_⟩
  · have b := testBit_of_bitN (CFSG.KS.Fi24ThreeO.allL_spec hW W hW')
    rw [ptC_eq] at b
    exact b
  · obtain ⟨hk5, g, hg, hkg⟩ := hFS k hk
    obtain ⟨hk5', g', hg', hkg'⟩ := hFS k' hk'
    by_cases he : g.1 = g'.1
    · rw [keyList_eq gq] at hK
      have hgg := incLoop_key_inj gq hK g hg g' hg' he
      rw [← hgg] at hkg'
      obtain ⟨-, hnc⟩ := andB_true (CFSG.KS.Fi24ThreeO.allL_spec hG g hg)
      exact Or.inr (ncL_spec hnc hkg hkg' hne)
    · obtain ⟨j, hj, hb⟩ := exists_testBit_ne_of_ne (hkey g hg).1 (hkey g' hg').1 he
      refine Or.inl ⟨tw[j], List.getElem_mem hj, ?_⟩
      rw [hbit g hg k hkg hk5 j hj, hbit g' hg' k' hkg' hk5' j hj]
      exact hb
  · obtain ⟨hk5, g, hg, hkg⟩ := hFS k hk
    obtain ⟨j, hj, hb⟩ := exists_testBit_false_of_ne (hkey g hg).1 (hkey g hg).2
    refine ⟨tw[j], List.getElem_mem hj, ?_⟩
    rw [hbit g hg k hkg hk5 j hj]
    exact hb

theorem offOK_spec (hV : VN NW NT) {cg cs : List Nat} {S : Nat} (h : offOK NW NT cg cs S = true) :
    ∀ x < 306936, S.testBit x = true →
      cP NW NT cg x ≠ x ∧ cP NW NT cg x ≠ cP NW NT cs x ∧ cP NW NT cg x ≠ cP NW NT (cs ++ cs) x := by
  intro x hx hS
  unfold offOK at h
  have e0 := Nat.eq_of_beq_eq_true h
  have e : (Nat.land (Nat.land S ptsM) (offS NW NT cg cs)).testBit x =
      (Nat.land S ptsM).testBit x := by rw [e0]
  rw [nland, nland, Nat.testBit_and, Nat.testBit_and, hS, ptsM_bit hx, Bool.true_and,
    Bool.true_and] at e
  exact (offS_spec hV e).2

theorem gensOK_spec (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {gp : List (List Nat × List Nat)}
    {en : List Nat} {ep : List (Nat × Nat × Nat)} (h : gensOK NW NT OL w gp en ep = true) :
    (∀ p ∈ gp, (fixC NW NT w).testBit (cP NW NT p.1 0) = true ∧
      (fixC NW NT w).testBit (cP NW NT p.2 0) = true) ∧
    ∀ k < 306936, cP NW NT w k ≠ k →
      (∃ p ∈ gp, cP NW NT (dW p.1 ++ dW p.2) k ≠ k ∧ cP NW NT (dW p.1 ++ dW p.2) k ≠ cP NW NT w k ∧
          cP NW NT (dW p.1 ++ dW p.2) k ≠ cP NW NT (w ++ w) k) ∨
        clsK OL NT k (cP NW NT w k) ≠ cP NW NT w k ∨
        ∃ d e, (fixC NW NT w).testBit d = true ∧ (fixC NW NT w).testBit e = true ∧
          clsK OL NT d (clsK OL NT e k) ≠ k ∧ clsK OL NT d (clsK OL NT e k) ≠ cP NW NT w k ∧
          clsK OL NT d (clsK OL NT e k) ≠ cP NW NT (w ++ w) k := by
  unfold gensOK at h
  rw [letB_eq'] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  rw [letB_eq'] at h6
  have hcov := Nat.eq_of_beq_eq_true h6
  refine ⟨fun p hp => ?_, fun k hk hw => ?_⟩
  · obtain ⟨a1, a2⟩ := andB_true (CFSG.KS.Fi24ThreeO.allL_spec h1 p hp)
    have b1 := testBit_of_bitN a1
    have b2 := testBit_of_bitN a2
    rw [ptC_eq] at b1
    rw [ptC_eq] at b2
    exact ⟨b1, b2⟩
  · rcases testBit_recLor _ (fun p : List Nat × List Nat => offS NW NT (dW p.1 ++ dW p.2) w) gp
      (testBit_of_land_ptsM hcov hk) with hB | ⟨p, hp, hoff⟩
    · rw [nlor, nlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hB
      rcases hB with hB | hB | hB
      · exact absurd ((testBit_fixC hV w k).1 hB).2 hw
      · have n1 := ne_of_notB_beq
          (CFSG.KS.Fi24ThreeO.allL_spec h3 k ((testBit_plOf en k).1 hB))
        rw [ptC_eq] at n1
        exact Or.inr (Or.inl n1)
      · obtain ⟨t, ht, rfl⟩ := testBit_pl3 hB
        obtain ⟨b1, b2⟩ := andB_true (CFSG.KS.Fi24ThreeO.allL_spec h5 t ht)
        obtain ⟨b11, b12⟩ := andB_true b1
        rw [letB_eq'] at b2
        obtain ⟨c1, c2⟩ := andB_true b2
        obtain ⟨c2, c3⟩ := andB_true c2
        have n1 := ne_of_notB_beq c1
        have n2 := ne_of_notB_beq c2
        have n3 := ne_of_notB_beq c3
        rw [ptC_eq] at n2
        rw [ptC_eq] at n3
        exact Or.inr (Or.inr ⟨t.2.1, t.2.2, testBit_of_bitN b11, testBit_of_bitN b12, n1, n2, n3⟩)
    · obtain ⟨-, o1, o2, o3⟩ := offS_spec hV hoff
      exact Or.inl ⟨p, hp, o1, o2, o3⟩

end CFSG.KS.Fi24ThreeO

end
