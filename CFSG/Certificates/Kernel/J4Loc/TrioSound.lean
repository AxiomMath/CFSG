module

public import Certificates.Data.Kernel.J4Loc.Trio
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Sporadic.J4.QTElem
public import CFSG.Sporadic.J4.QTRankNative

public section

namespace CFSG.KS.J4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.Loop CFSG.Sporadic.J4.QT

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  rw [andB_eq, Bool.and_eq_true] at h
  exact h

theorem fld_eq (w P i : ℕ) : fld w P i = (P >>> (w * i)) % 2 ^ w := by
  change (P >>> (w * i)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_lt (w P i : ℕ) : fld w P i < 2 ^ w := by
  rw [fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem mem_keyK (c : ℕ) : ∀ l : List ℕ, (keyK l).testBit c = true ↔ c ∈ l
  | [] => by
    change (0 : ℕ).testBit c = true ↔ c ∈ []
    simp
  | x :: l => by
    change ((keyK l) ||| (1 <<< x)).testBit c = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
    simp only [Bool.or_eq_true, decide_eq_true_eq, mem_keyK c l]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

theorem mem_of_keyK_eq {l l' : List ℕ} (h : Nat.beq (keyK l) (keyK l') = true) (c : ℕ) :
    c ∈ l ↔ c ∈ l' := by
  rw [← mem_keyK, ← mem_keyK, Nat.eq_of_beq_eq_true h]

theorem allL_spec {f : ℕ → Bool} : ∀ {l : List ℕ}, allL l f = true → ∀ x ∈ l, f x = true
  | [], _ => by simp
  | x :: l, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact allL_spec h2 y hy

theorem eqLK_spec : ∀ {l l' : List ℕ}, eqLK l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: l, y :: l', h => by
    obtain ⟨h1, h2⟩ := andB_true h
    rw [Nat.eq_of_beq_eq_true h1, eqLK_spec h2]

theorem mapK_eq (r : List ℕ) : ∀ l : List ℕ, mapK r l = l.map (actK r)
  | [] => rfl
  | x :: l => by
    change actK r x :: mapK r l = _
    rw [mapK_eq r l, List.map_cons]

theorem rowL_eq : ∀ (l : List (List ℕ)) (i : ℕ), rowL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => rowL_eq l i

theorem rowsXor_cons (x : ℕ) (r : List ℕ) (c : ℕ) : ∀ n,
    rowsXor (fun j => (x :: r).getD j 0) (n + 1) c =
      (if c.testBit 0 then x else 0) ^^^ rowsXor (fun j => r.getD j 0) n (c >>> 1)
  | 0 => by
    rw [rowsXor_succ, rowsXor_zero, rowsXor_zero]
    simp
  | n + 1 => by
    rw [rowsXor_succ, rowsXor_cons x r c n, rowsXor_succ, Nat.testBit_shiftRight, Nat.xor_assoc,
      Nat.add_comm 1 n, List.getD_cons_succ]

theorem actK_eq : ∀ (r : List ℕ) (c : ℕ), actK r c = rowsXor (fun j => r.getD j 0) r.length c
  | [], _ => rfl
  | x :: r, c => by
    change Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 x (Nat.beq (Nat.land c 1) 1))
      (actK r (Nat.shiftRight c 1)) = _
    rw [actK_eq r, List.length_cons, rowsXor_cons]
    have hb : Nat.beq (Nat.land c 1) 1 = c.testBit 0 := by
      rw [Nat.testBit_zero]
      change Nat.beq (c &&& 1) 1 = _
      rw [Nat.and_one_is_mod]
      cases h : Nat.beq (c % 2) 1
      · simp [Nat.ne_of_beq_eq_false h]
      · simp [Nat.eq_of_beq_eq_true h]
    rw [hb]
    cases c.testBit 0 <;> rfl

theorem actK_eq_actT {r : List ℕ} (hr : r.length = 11) (c : ℕ) : actK r c = actT r c := by
  rw [actK_eq, hr]
  rfl

@[expose] noncomputable def octF (TK i : ℕ) : Finset ℕ := (octL (fld 80 TK i)).toFinset

@[expose] noncomputable def wordF (LR : List (List ℕ)) : List ℕ → Finset ℕ → Finset ℕ
  | [], W => W
  | l :: w, W => wordF LR w (W.image (actK (rowL LR l)))

theorem wordF_append (LR : List (List ℕ)) (w : List ℕ) (l : ℕ) : ∀ W : Finset ℕ,
    wordF LR (w ++ [l]) W = (wordF LR w W).image (actK (rowL LR l)) := by
  induction w with
  | nil => intro W; rfl
  | cons a w ih => intro W; exact ih _

theorem sortedC_spec {c : ℕ} (h : sortedC c = true) : c < 2 ^ 77 ∧ 0 < fld 11 c 0 ∧
    ∀ k < 6, fld 11 c k < fld 11 c (k + 1) := by
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h2
  refine ⟨?_, lt_of_blt h2, fun k hk => lt_of_blt (allR_spec h3 k hk)⟩
  have := lt_of_blt h1
  change c < 1 <<< 77 at this
  rwa [Nat.one_shiftLeft] at this

theorem octL_eq (c : ℕ) : octL c = [0, fld 11 c 0, fld 11 c 1, fld 11 c 2, fld 11 c 3,
    fld 11 c 4, fld 11 c 5, fld 11 c 6] := rfl

theorem octL_sorted {c : ℕ} (h : sortedC c = true) : (octL c).Pairwise (· < ·) := by
  obtain ⟨-, h0, hs⟩ := sortedC_spec h
  have h1 : fld 11 c 0 < fld 11 c 1 := hs 0 (by decide)
  have h2 : fld 11 c 1 < fld 11 c 2 := hs 1 (by decide)
  have h3 : fld 11 c 2 < fld 11 c 3 := hs 2 (by decide)
  have h4 : fld 11 c 3 < fld 11 c 4 := hs 3 (by decide)
  have h5 : fld 11 c 4 < fld 11 c 5 := hs 4 (by decide)
  have h6 : fld 11 c 5 < fld 11 c 6 := hs 5 (by decide)
  rw [octL_eq]
  repeat' refine List.Pairwise.cons ?_ ?_
  all_goals first
    | exact List.Pairwise.nil
    | (intro a ha
       simp only [List.mem_cons, List.not_mem_nil, or_false] at ha)
  all_goals omega

theorem octF_card {TK i : ℕ} (h : sortedC (fld 80 TK i) = true) : (octF TK i).card = 8 := by
  unfold octF
  rw [List.toFinset_card_of_nodup ((octL_sorted h).imp ne_of_lt)]
  rfl

theorem testBit_fld (c k r : ℕ) (hr : r < 11) :
    (fld 11 c k).testBit r = c.testBit (11 * k + r) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hr, Nat.add_comm]

theorem eq_of_pairwise_lt : ∀ {l l' : List ℕ}, l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l, b :: l', h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      · rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
        · exact e.symm
        · exact absurd (lt_trans (h2.1 a ha) (h1.1 b hb)) (lt_irrefl b)
    subst hab
    refine congrArg _ (eq_of_pairwise_lt h1.2 h2.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (e ▸ h1.1 x hx) (lt_irrefl x)
      · exact e
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (e ▸ h2.1 x hx) (lt_irrefl x)
      · exact e

theorem code_inj {c c' : ℕ} (h : sortedC c = true) (h' : sortedC c' = true)
    (he : (octL c).toFinset = (octL c').toFinset) : c = c' := by
  have hl : octL c = octL c' := eq_of_pairwise_lt (octL_sorted h) (octL_sorted h')
    fun x => by rw [← List.mem_toFinset, he, List.mem_toFinset]
  rw [octL_eq, octL_eq] at hl
  simp only [List.cons.injEq, true_and, and_true] at hl
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hl
  have hk : ∀ k < 7, fld 11 c k = fld 11 c' k := by
    intro k hk
    interval_cases k
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
  have hc := (sortedC_spec h).1
  have hc' := (sortedC_spec h').1
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 77
  · have hb' : b = 11 * (b / 11) + b % 11 := (Nat.div_add_mod b 11).symm
    rw [hb', ← testBit_fld c _ _ (Nat.mod_lt _ (by decide)),
      ← testBit_fld c' _ _ (Nat.mod_lt _ (by decide)), hk _ (by omega)]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc' (Nat.pow_le_pow_right (by decide) (by omega)))]

@[expose] def OctAll (LR : List (List ℕ)) (TK TR N I0 : ℕ) : Prop :=
  ∀ i < N, octOK LR TK TR N I0 i = true

theorem octBlk_all {LR : List (List ℕ)} {TK TR N I0 B : ℕ}
    (h : ∀ k < B, octBlk LR TK TR N I0 k = true) (hN : N ≤ 32 * B) : OctAll LR TK TR N I0 := by
  intro i hi
  have hk : orB (notB (Nat.blt (Nat.add (Nat.mul 32 (i / 32)) (i % 32)) N))
      (octOK LR TK TR N I0 (Nat.add (Nat.mul 32 (i / 32)) (i % 32))) = true :=
    allR_spec (h (i / 32) (by omega)) (i % 32) (Nat.mod_lt _ (by decide))
  rw [show Nat.add (Nat.mul 32 (i / 32)) (i % 32) = i from Nat.div_add_mod i 32] at hk
  rcases orB_true hk with hk | hk
  · have hb : Nat.blt i N = true := by
      change Nat.ble (i + 1) N = true
      rw [Nat.ble_eq]
      exact hi
    rw [notB_eq, hb] at hk
    exact absurd hk (by decide)
  · exact hk

theorem octOK_spec {LR : List (List ℕ)} {TK TR N I0 i : ℕ} (h : octOK LR TK TR N I0 i = true) :
    sortedC (fld 80 TK i) = true ∧
      (i + 1 < N → fld 80 TK i < fld 80 TK (i + 1)) ∧
      (∀ a ∈ octL (fld 80 TK i), ∀ b ∈ octL (fld 80 TK i), a ^^^ b ∈ octL (fld 80 TK i)) ∧
      (∀ l < 6, fld 12 (fld 96 TR i) l < N ∧
        (octF TK i).image (actK (rowL LR l)) = octF TK (fld 12 (fld 96 TR i) l)) ∧
      treeOK TR N I0 i (fld 96 TR i) = true := by
  unfold octOK at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨hs, h⟩ := andB_true h
  obtain ⟨hn, h⟩ := andB_true h
  obtain ⟨hx, h⟩ := andB_true h
  obtain ⟨hl, ht⟩ := andB_true h
  refine ⟨hs, fun hi => ?_, fun a ha b hb => ?_, fun l hl' => ?_, ht⟩
  · rcases orB_true hn with hn | hn
    · rw [notB_eq] at hn
      have hb : Nat.blt (Nat.succ i) N = true := by
        change Nat.ble (i + 1 + 1) N = true
        rw [Nat.ble_eq]
        exact hi
      rw [hb] at hn
      exact absurd hn (by decide)
    · exact lt_of_blt hn
  · exact (mem_keyK _ _).1 (by rw [← bitB_eq]; exact allL_spec (allL_spec hx a ha) b hb)
  · have h1 := allR_spec hl l hl'
    rw [strictB_eq] at h1
    obtain ⟨h1, h2⟩ := andB_true h1
    refine ⟨lt_of_blt h1, ?_⟩
    ext x
    have e := mem_of_keyK_eq h2 x
    rw [mapK_eq, List.mem_map] at e
    unfold octF
    rw [Finset.mem_image, List.mem_toFinset]
    simp only [List.mem_toFinset]
    exact e

theorem treeOK_spec {TR N I0 i r : ℕ} (h : treeOK TR N I0 i r = true) :
    (fld 8 r 11 = 0 → i = I0) ∧
      (fld 8 r 11 ≠ 0 → fld 12 r 6 < N ∧ fld 4 r 21 < 6 ∧
        fld 12 (fld 96 TR (fld 12 r 6)) (fld 4 r 21) = i ∧
        fld 8 (fld 96 TR (fld 12 r 6)) 11 + 1 = fld 8 r 11) := by
  unfold treeOK at h
  rw [strictB_eq] at h
  cases hd : Nat.beq (fld 8 r 11) 0
  · rw [hd] at h
    change (strictB (fld 12 r 6) fun p => strictB (fld 4 r 21) fun l => andB (Nat.blt p N)
      (andB (Nat.blt l 6) (strictB (fld 96 TR p) fun rp => andB (Nat.beq (fld 12 rp l) i)
        (Nat.beq (Nat.succ (fld 8 rp 11)) (fld 8 r 11))))) = true at h
    rw [strictB_eq, strictB_eq] at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h⟩ := andB_true h
    rw [strictB_eq] at h
    obtain ⟨h3, h4⟩ := andB_true h
    refine ⟨fun h0 => by rw [h0] at hd; exact absurd hd (by decide), fun _ =>
      ⟨lt_of_blt h1, lt_of_blt h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩⟩
  · rw [hd] at h
    exact ⟨fun _ => Nat.eq_of_beq_eq_true h, fun h0 => absurd (Nat.eq_of_beq_eq_true hd) h0⟩

section Tree

variable {LR : List (List ℕ)} {TK TR N I0 : ℕ}

theorem octF_step (h : OctAll LR TK TR N I0) {i : ℕ} (hi : i < N) {l : ℕ} (hl : l < 6) :
    ∃ j < N, (octF TK i).image (actK (rowL LR l)) = octF TK j :=
  ⟨_, ((octOK_spec (h i hi)).2.2.2.1 l hl).1, ((octOK_spec (h i hi)).2.2.2.1 l hl).2⟩

theorem wordF_octF (h : OctAll LR TK TR N I0) : ∀ (w : List ℕ), (∀ l ∈ w, l < 6) →
    ∀ i < N, ∃ j < N, wordF LR w (octF TK i) = octF TK j := by
  intro w
  induction w with
  | nil => intro _ i hi; exact ⟨i, hi, rfl⟩
  | cons l w ih =>
    intro hw i hi
    obtain ⟨j, hj, he⟩ := octF_step h hi (hw l List.mem_cons_self)
    change ∃ k < N, wordF LR w ((octF TK i).image (actK (rowL LR l))) = octF TK k
    rw [he]
    exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) j hj

theorem octF_word (h : OctAll LR TK TR N I0) {i : ℕ} (hi : i < N) :
    ∃ w : List ℕ, (∀ l ∈ w, l < 6) ∧ octF TK i = wordF LR w (octF TK I0) := by
  suffices H : ∀ d, ∀ i < N, fld 8 (fld 96 TR i) 11 = d →
      ∃ w : List ℕ, (∀ l ∈ w, l < 6) ∧ octF TK i = wordF LR w (octF TK I0) from
    H _ i hi rfl
  intro d
  induction d with
  | zero =>
    intro i hi hd
    rw [(treeOK_spec (octOK_spec (h i hi)).2.2.2.2).1 hd]
    exact ⟨[], by simp, rfl⟩
  | succ d ih =>
    intro i hi hd
    obtain ⟨hp, hl, hc, hdp⟩ := (treeOK_spec (octOK_spec (h i hi)).2.2.2.2).2 (by omega)
    obtain ⟨w, hw, he⟩ := ih _ hp (by omega)
    refine ⟨w ++ [fld 4 (fld 96 TR i) 21], fun a ha => ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact hw a ha
      · rw [List.mem_singleton.1 ha]
        exact hl
    · rw [wordF_append, ← he, ((octOK_spec (h _ hp)).2.2.2.1 _ hl).2, hc]

theorem code_lt (h : OctAll LR TK TR N I0) {i j : ℕ} (hij : i < j) (hj : j < N) :
    fld 80 TK i < fld 80 TK j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := (octOK_spec (h j (by omega))).2.1 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact lt_trans (ih hij (by omega)) hs
    · exact hs

theorem octF_inj (h : OctAll LR TK TR N I0) {i j : ℕ} (hi : i < N) (hj : j < N)
    (he : octF TK i = octF TK j) : i = j := by
  have hc := code_inj (octOK_spec (h i hi)).1 (octOK_spec (h j hj)).1 he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd hc (ne_of_lt (code_lt h hij hj))
  · exact hij
  · exact absurd hc.symm (ne_of_lt (code_lt h hij hi))

theorem octF_props (h : OctAll LR TK TR N I0) {i : ℕ} (hi : i < N) :
    (octF TK i).card = 8 ∧ 0 ∈ octF TK i ∧ (∀ x ∈ octF TK i, x < 2048) ∧
      ∀ x ∈ octF TK i, ∀ y ∈ octF TK i, x ^^^ y ∈ octF TK i := by
  have hs := octOK_spec (h i hi)
  refine ⟨octF_card hs.1, by simp [octF, octL_eq], fun x hx => ?_, fun x hx y hy => ?_⟩
  · simp only [octF, octL_eq, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | decide
      | exact fld_lt 11 _ _
  · unfold octF at hx hy ⊢
    rw [List.mem_toFinset] at hx hy ⊢
    exact hs.2.2.1 x hx y hy

end Tree

end CFSG.KS.J4Loc

end
