module

public import Certificates.Data.Kernel.OmegaPacked
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

public section

namespace CFSG.Certificates.Kernel

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree Certificates.OmegaPacked

namespace OmegaPackedS

open CFSG.LieType.Chevalley.RootOps

theorem keyLe_trans {a b c : Entry} (h1 : keyLe a b = true) (h2 : keyLe b c = true) :
    keyLe a c = true := by
  simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.ble_eq] at *
  omega

theorem keyLe_total {a b : Entry} (h : ¬keyLe a b = true) : keyLe b a = true := by
  simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.ble_eq] at *
  omega

theorem mergeF_perm' : ∀ (f : ℕ) (l l' : List Entry), (mergeF f l l').Perm (l ++ l')
  | 0, l, l' => by simp [mergeF]
  | _ + 1, [], l' => by simp [mergeF]
  | _ + 1, e :: l, [] => by simp [mergeF]
  | f + 1, e :: l, e' :: l' => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm' f l (e' :: l')).cons e
    · refine ((mergeF_perm' f (e :: l) l').cons e').trans ?_
      simpa using (List.perm_middle (a := e') (l₁ := e :: l) (l₂ := l')).symm

theorem splitAlt_perm' : ∀ l : List Entry, ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => by simp [splitAlt]
  | e :: l => by
    simp only [splitAlt, List.cons_append]
    exact List.Perm.cons e (List.perm_append_comm.trans (splitAlt_perm' l))

theorem msortF_perm' : ∀ (f : ℕ) (l : List Entry), (msortF f l).Perm l
  | 0, l => by simp [msortF]
  | _ + 1, [] => by simp [msortF]
  | _ + 1, [e] => by simp [msortF]
  | f + 1, e :: e' :: l => by
    unfold msortF
    exact (mergeF_perm' _ _ _).trans
      (((msortF_perm' f _).append (msortF_perm' f _)).trans (splitAlt_perm' _))

abbrev KSorted (l : List Entry) : Prop := l.Pairwise fun a b => keyLe a b = true

theorem mergeF_sorted : ∀ (f : ℕ) (l l' : List Entry), KSorted l → KSorted l' →
    l.length + l'.length ≤ f → KSorted (mergeF f l l')
  | 0, l, l', _, _, hf => by
    have : l = [] ∧ l' = [] := by
      constructor <;> apply List.eq_nil_of_length_eq_zero <;> omega
    obtain ⟨rfl, rfl⟩ := this
    simp [mergeF]
  | _ + 1, [], l', _, h', _ => by simpa [mergeF] using h'
  | _ + 1, e :: l, [], h, _, _ => by simpa [mergeF] using h
  | f + 1, e :: l, e' :: l', h, h', hf => by
    unfold mergeF
    unfold KSorted at *
    rw [List.pairwise_cons] at h h'
    split_ifs with hk
    · refine List.pairwise_cons.2 ⟨fun x hx => ?_, mergeF_sorted f l (e' :: l') h.2
        (List.pairwise_cons.2 h') (by simp at hf ⊢; omega)⟩
      rcases List.mem_append.1 ((mergeF_perm' f l (e' :: l')).mem_iff.1 hx) with hx | hx
      · exact h.1 x hx
      · rcases List.mem_cons.1 hx with hx | hx
        · rw [hx]
          exact hk
        · exact keyLe_trans hk (h'.1 x hx)
    · have hk' := keyLe_total hk
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, mergeF_sorted f (e :: l) l'
        (List.pairwise_cons.2 h) h'.2 (by simp at hf ⊢; omega)⟩
      rcases List.mem_append.1 ((mergeF_perm' f (e :: l) l').mem_iff.1 hx) with hx | hx
      · rcases List.mem_cons.1 hx with hx | hx
        · rw [hx]
          exact hk'
        · exact keyLe_trans hk' (h.1 x hx)
      · exact h'.1 x hx

theorem splitAlt_length : ∀ l : List Entry,
    (splitAlt l).1.length = (l.length + 1) / 2 ∧ (splitAlt l).2.length = l.length / 2
  | [] => by simp [splitAlt]
  | e :: l => by
    have := splitAlt_length l
    simp only [splitAlt, List.length_cons]
    omega

theorem msortF_sorted : ∀ (f : ℕ) (l : List Entry), l.length ≤ 2 ^ f → KSorted (msortF f l)
  | 0, l, hl => by
    match l, hl with
    | [], _ => simp [msortF]
    | [e], _ => simp [msortF]
  | _ + 1, [], _ => by simp [msortF]
  | _ + 1, [e], _ => by simp [msortF]
  | f + 1, e :: e' :: l, hl => by
    unfold msortF
    have hs := splitAlt_length (e :: e' :: l)
    simp only [List.length_cons, pow_succ] at hs hl
    refine mergeF_sorted _ _ _ (msortF_sorted f _ (by omega)) (msortF_sorted f _ (by omega)) ?_
    rw [(msortF_perm' f (splitAlt (e :: e' :: l)).1).length_eq,
      (msortF_perm' f (splitAlt (e :: e' :: l)).2).length_eq]
    omega

def KLt (a b : Entry) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1)

theorem kLt_trans {a b c : Entry} (h1 : KLt a b) (h2 : KLt b c) : KLt a c := by
  unfold KLt at *
  omega

theorem combineE_spec : ∀ l : List Entry, KSorted l →
    (combineE l).Pairwise KLt ∧ ∀ x ∈ combineE l, ∃ y ∈ l, x.1 = y.1 ∧ x.2.1 = y.2.1
  | [], _ => by simp [combineE]
  | e :: l, h => by
    unfold KSorted at h
    rw [List.pairwise_cons] at h
    obtain ⟨ih1, ih2⟩ := combineE_spec l h.2
    simp only [combineE]
    cases hM : combineE l with
    | nil => simp
    | cons e' l' =>
      rw [hM] at ih1 ih2
      obtain ⟨y, hy, hy1, hy2⟩ := ih2 e' List.mem_cons_self
      have hey := h.1 y hy
      simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
        Nat.ble_eq] at hey
      rw [List.pairwise_cons] at ih1
      simp only
      split_ifs with hk
      · simp only [Bool.and_eq_true, Nat.beq_eq] at hk
        refine ⟨List.pairwise_cons.2 ⟨fun x hx => ?_, ih1.2⟩, ?_⟩
        · have := ih1.1 x hx
          unfold KLt at this ⊢
          simp only
          omega
        · intro x hx
          rcases List.mem_cons.1 hx with hx | hx
          · exact ⟨e, List.mem_cons_self, by rw [hx], by rw [hx]⟩
          · obtain ⟨z, hz, h1, h2⟩ := ih2 x (List.mem_cons_of_mem _ hx)
            exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩
      · simp only [Bool.and_eq_true, Nat.beq_eq, not_and] at hk
        have hee : KLt e e' := by
          unfold KLt
          by_cases h1 : e.1 = e'.1
          · have := hk h1
            omega
          · omega
        refine ⟨List.pairwise_cons.2 ⟨fun x hx => ?_, List.pairwise_cons.2 ih1⟩, ?_⟩
        · rcases List.mem_cons.1 hx with hx | hx
          · rw [hx]
            exact hee
          · exact kLt_trans hee (ih1.1 x hx)
        · intro x hx
          rcases List.mem_cons.1 hx with hx | hx
          · exact ⟨x, by rw [hx]; exact List.mem_cons_self, rfl, rfl⟩
          · obtain ⟨z, hz, h1, h2⟩ := ih2 x hx
            exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩

def Good (w : ℕ) (A : List Entry) : Prop :=
  A.Pairwise KLt ∧ ∀ e ∈ A, e.2.2 = 1 ∧ e.1 < w ∧ e.2.1 < w

theorem good_modE_canonE {w : ℕ} {Y : List Entry} (hY : Y.length ≤ 2 ^ 16)
    (hp : ∀ e ∈ Y, e.1 < w ∧ e.2.1 < w) : Good w (modE 2 (canonE Y)) := by
  obtain ⟨h1, h2⟩ := combineE_spec _ (msortF_sorted 16 Y hY)
  have h1' := h1.sublist (List.filter_sublist (p := fun e => e.2.2 != 0))
  unfold Good modE canonE
  constructor
  · rw [List.pairwise_filterMap]
    refine h1'.imp fun {a b} hab => ?_
    intro a' ha' b' hb'
    split_ifs at ha' hb' <;> simp at ha' hb'
    rw [← ha', ← hb']
    exact hab
  · intro e he
    rw [List.mem_filterMap] at he
    obtain ⟨x, hx, hxe⟩ := he
    split_ifs at hxe with hz
    simp only [Option.some.injEq] at hxe
    rw [← hxe]
    obtain ⟨y, hy, hy1, hy2⟩ := h2 x (List.mem_filter.1 hx).1
    have hyY := hp y ((msortF_perm' 16 Y).mem_iff.1 hy)
    refine ⟨?_, by simp only; omega, by simp only; omega⟩
    simp only
    omega

theorem length_le_of_nodup {w : ℕ} {l : List ℕ} (hl : l.Nodup) (hw : ∀ x ∈ l, x < w) :
    l.length ≤ w := by
  classical
  rw [← List.toFinset_card_of_nodup hl]
  calc l.toFinset.card ≤ (Finset.range w).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.2 (hw x (List.mem_toFinset.1 hx))
    _ = w := Finset.card_range w

theorem length_le_of_nodup2 {w : ℕ} {l : List (ℕ × ℕ)} (hl : l.Nodup)
    (hw : ∀ x ∈ l, x.1 < w ∧ x.2 < w) : l.length ≤ w * w := by
  classical
  rw [← List.toFinset_card_of_nodup hl]
  calc l.toFinset.card ≤ (Finset.range w ×ˢ Finset.range w).card :=
        Finset.card_le_card fun x hx => by
          have := hw x (List.mem_toFinset.1 hx)
          simp [Finset.mem_product, this.1, this.2]
    _ = w * w := by simp

theorem good_length {w : ℕ} {A : List Entry} (h : Good w A) : A.length ≤ w * w := by
  have := length_le_of_nodup2 (w := w) (l := A.map fun e => (e.1, e.2.1)) ?_ ?_
  · simpa using this
  · unfold List.Nodup
    rw [List.pairwise_map]
    exact h.1.imp fun {a b} hab heq => by
      unfold KLt at hab
      simp only [Prod.mk.injEq] at heq
      omega
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact ⟨(h.2 e he).2.1, (h.2 e he).2.2⟩

theorem good_filter_length {w : ℕ} {A : List Entry} (h : Good w A) (m : ℕ) :
    (A.filter fun e => Nat.beq e.1 m).length ≤ w := by
  have := length_le_of_nodup (w := w) (l := (A.filter fun e => Nat.beq e.1 m).map (·.2.1)) ?_ ?_
  · simpa using this
  · unfold List.Nodup
    rw [List.pairwise_map, List.pairwise_filter]
    exact h.1.imp fun {a b} hab ha hb heq => by
      simp only [Nat.beq_eq] at ha hb
      unfold KLt at hab
      omega
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact (h.2 e (List.mem_filter.1 he).1).2.2

def Canon (w : ℕ) (X : List PEntry) : Prop :=
  ∃ A0 A1, Good w A0 ∧ Good w A1 ∧
    X = A0.map (fun e => ((0, 0), e)) ++ A1.map (fun e => ((1, 0), e))

theorem length_flatMap_redW (d : ℕ) (X : List PEntry) :
    (X.flatMap (redW d)).length ≤ X.length := by
  induction X with
  | nil => simp
  | cons x X ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : (redW d x).length ≤ 1 := by
      unfold redW
      split_ifs <;> simp
    omega

theorem pos_flatMap_redW {w d : ℕ} {X : List PEntry} (hX : ∀ x ∈ X, x.2.1 < w ∧ x.2.2.1 < w) :
    ∀ e ∈ X.flatMap (redW d), e.1 < w ∧ e.2.1 < w := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.1 he
  have := hX x hx
  unfold redW at he
  split_ifs at he <;> simp at he
  · rw [he]
    exact this
  · rw [he]
    exact this

theorem canon_normW {w : ℕ} {X : List PEntry} (hl : X.length ≤ 2 ^ 16)
    (hX : ∀ x ∈ X, x.2.1 < w ∧ x.2.2.1 < w) : Canon w (normW X) :=
  ⟨_, _, good_modE_canonE ((length_flatMap_redW 0 X).trans hl) (pos_flatMap_redW hX),
    good_modE_canonE ((length_flatMap_redW 1 X).trans hl) (pos_flatMap_redW hX), rfl⟩

theorem pmul_length_le {A B : List PEntry} {k : ℕ}
    (h : ∀ y ∈ B, (A.filter fun x => Nat.beq x.2.1 y.2.2.1).length ≤ k) :
    (pmul A B).length ≤ B.length * k := by
  induction B with
  | nil => simp [pmul]
  | cons y B ih =>
    rw [pmul, List.flatMap_cons, List.length_append, List.length_map, ← pmul]
    have h1 := ih fun y' hy' => h y' (List.mem_cons_of_mem _ hy')
    have h2 := h y List.mem_cons_self
    rw [List.length_cons, Nat.add_one_mul]
    omega

theorem canon_filter_length {w : ℕ} {X : List PEntry} (h : Canon w X) (m : ℕ) :
    (X.filter fun x => Nat.beq x.2.1 m).length ≤ 2 * w := by
  obtain ⟨A0, A1, h0, h1, rfl⟩ := h
  simp only [List.filter_append, List.filter_map, List.length_append, List.length_map]
  have := good_filter_length h0 m
  have := good_filter_length h1 m
  simp only [Function.comp_def] at *
  omega

theorem canon_length {w : ℕ} {X : List PEntry} (h : Canon w X) : X.length ≤ 2 * (w * w) := by
  obtain ⟨A0, A1, h0, h1, rfl⟩ := h
  have := good_length h0
  have := good_length h1
  simp only [List.length_append, List.length_map]
  omega

theorem canon_pos {w : ℕ} {X : List PEntry} (h : Canon w X) :
    ∀ x ∈ X, x.2.1 < w ∧ x.2.2.1 < w := by
  obtain ⟨A0, A1, h0, h1, rfl⟩ := h
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact (h0.2 e he).2
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact (h1.2 e he).2

theorem entriesOk_spec {τ : Tag} {w g : ℕ} (h : entriesOk τ w g = true) :
    (∀ k ∈ [1, 2, 3], ∀ e ∈ entries τ g k, e.1 < w ∧ e.2.1 < w) ∧
      2 * w * w + ((entries τ g 1).length + (entries τ g 2).length + (entries τ g 3).length) *
        (2 * w + 1) ≤ 65536 := by
  simp only [entriesOk, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Nat.ble_eq,
    List.foldl_cons, List.foldl_nil, Nat.zero_add] at h
  exact ⟨h.1, h.2⟩

theorem nilpE_mem {τ : Tag} {g : ℕ} {C : ℤ} {ea eb : ℕ} {y : PEntry}
    (hy : y ∈ nilpE τ g C ea eb) : ∃ k ∈ [1, 2, 3], ∃ e ∈ entries τ g k,
      y.2.1 = e.1 ∧ y.2.2.1 = e.2.1 := by
  simp only [nilpE, List.mem_flatMap, List.mem_map] at hy
  obtain ⟨k, hk, e, he, rfl⟩ := hy
  exact ⟨k, hk, e, he, rfl, rfl⟩

theorem nilpE_length (τ : Tag) (g : ℕ) (C : ℤ) (ea eb : ℕ) :
    (nilpE τ g C ea eb).length =
      (entries τ g 1).length + (entries τ g 2).length + (entries τ g 3).length := by
  simp only [nilpE, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_map]
  omega

theorem omegaProd_canon {τ : Tag} {w : ℕ} : ∀ (fs : List (ℕ × ℤ × ℕ)) (acc : List PEntry),
    Canon w acc → (∀ f ∈ fs, entriesOk τ w f.1 = true) → Canon w (omegaProd τ acc fs)
  | [], acc, hacc, _ => hacc
  | f :: fs, acc, hacc, hfs => by
    rw [omegaProd]
    refine omegaProd_canon fs _ ?_ fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    obtain ⟨hpos, hlen⟩ := entriesOk_spec (hfs f List.mem_cons_self)
    set N := nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0
    have hN : ∀ y ∈ N, y.2.1 < w ∧ y.2.2.1 < w := by
      intro y hy
      obtain ⟨k, hk, e, he, h1, h2⟩ := nilpE_mem hy
      rw [h1, h2]
      exact hpos k hk e he
    have hA := canon_pos hacc
    refine canon_normW ?_ ?_
    · have h1 := canon_length hacc
      have h2 := pmul_length_le (A := acc) (B := N) (k := 2 * w)
        fun y _ => canon_filter_length hacc _
      have h3 := nilpE_length τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0
      rw [mul1, List.length_append, List.length_append]
      have h4 : N.length * (2 * w + 1) = N.length * (2 * w) + N.length := by ring
      have h5 : 2 * w * w = 2 * (w * w) := by ring
      rw [← h3] at hlen
      rw [h4, h5] at hlen
      omega
    · intro x hx
      simp only [mul1, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hA x hx
      · exact hN x hx
      · simp only [pmul, List.mem_flatMap, List.mem_map, List.mem_filter] at hx
        obtain ⟨y, hy, z, ⟨hz, -⟩, rfl⟩ := hx
        exact ⟨(hN y hy).1, (hA z hz).2⟩

theorem eq_of_mem_iff : ∀ {A B : List Entry}, A.Pairwise KLt → B.Pairwise KLt →
    (∀ x, x ∈ A ↔ x ∈ B) → A = B
  | [], [], _, _, _ => rfl
  | [], b :: B, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: A, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: A, b :: B, hA, hB, h => by
    rw [List.pairwise_cons] at hA hB
    have irr : ∀ x : Entry, ¬KLt x x := fun x hx => by
      unfold KLt at hx
      omega
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with h1 | h1
      · exact h1
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with h2 | h2
      · exact h2.symm
      exact absurd (kLt_trans (hA.1 b h2) (hB.1 a h1)) (irr a)
    subst hab
    rw [eq_of_mem_iff hA.2 hB.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩]
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with h1 | h1
      · subst h1
        exact absurd (hA.1 _ hx) (irr _)
      · exact h1
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with h1 | h1
      · subst h1
        exact absurd (hB.1 _ hx) (irr _)
      · exact h1

section Coeff

variable (R : Type*) [CommRing R]

noncomputable def cf (A : List Entry) (c r : ℕ) : R :=
  (A.map fun e => if e.1 = c ∧ e.2.1 = r then (e.2.2 : R) else 0).sum

noncomputable def cp (L : List PEntry) (s : R) (c r : ℕ) : R :=
  (L.map fun x => if x.2.1 = c ∧ x.2.2.1 = r then s ^ x.1.1 * (x.2.2.2 : R) else 0).sum

variable {R}

theorem cf_cons (e : Entry) (A : List Entry) (c r : ℕ) :
    cf R (e :: A) c r = (if e.1 = c ∧ e.2.1 = r then (e.2.2 : R) else 0) + cf R A c r := by
  simp [cf]

theorem cf_nil (c r : ℕ) : cf R [] c r = 0 := by simp [cf]

theorem cf_append (A B : List Entry) (c r : ℕ) :
    cf R (A ++ B) c r = cf R A c r + cf R B c r := by
  simp [cf]

theorem cp_cons (x : PEntry) (L : List PEntry) (s : R) (c r : ℕ) :
    cp R (x :: L) s c r =
      (if x.2.1 = c ∧ x.2.2.1 = r then s ^ x.1.1 * (x.2.2.2 : R) else 0) + cp R L s c r := by
  simp [cp]

theorem cp_nil (s : R) (c r : ℕ) : cp R [] s c r = 0 := by simp [cp]

theorem cp_append (A B : List PEntry) (s : R) (c r : ℕ) :
    cp R (A ++ B) s c r = cp R A s c r + cp R B s c r := by
  simp [cp]

theorem cp_map_deg (d : ℕ) (A : List Entry) (s : R) (c r : ℕ) :
    cp R (A.map fun e => ((d, 0), e)) s c r = s ^ d * cf R A c r := by
  induction A with
  | nil => simp [cp_nil, cf_nil]
  | cons e A ih =>
    rw [List.map_cons, cp_cons, ih, cf_cons]
    simp only
    split_ifs <;> ring

theorem cf_combineE (A : List Entry) (c r : ℕ) : cf R (combineE A) c r = cf R A c r := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    simp only [combineE]
    revert ih
    generalize combineE A = M
    intro ih
    rw [cf_cons e A, ← ih]
    rcases M with _ | ⟨e', l'⟩
    · rw [cf_cons]
    · simp only
      by_cases hk : (Nat.beq e.1 e'.1 && Nat.beq e.2.1 e'.2.1) = true
      · rw [if_pos hk]
        simp only [Bool.and_eq_true, Nat.beq_eq] at hk
        obtain ⟨h1, h2⟩ := hk
        rw [cf_cons, cf_cons]
        simp only [← h1, ← h2]
        split_ifs <;> push_cast <;> ring
      · rw [if_neg hk, cf_cons]

theorem cf_filter (A : List Entry) (c r : ℕ) :
    cf R (A.filter fun e => e.2.2 != 0) c r = cf R A c r := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [cf_cons, ih, cf_cons]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [ih, cf_cons, h]
      simp

theorem intCast_emod_two (h2 : (2 : R) = 0) (z : ℤ) : ((z % 2 : ℤ) : R) = (z : R) := by
  conv_rhs => rw [← Int.emod_add_mul_ediv z 2]
  push_cast
  rw [h2]
  ring

theorem cf_modE (h2 : (2 : R) = 0) (A : List Entry) (c r : ℕ) :
    cf R (modE 2 A) c r = cf R A c r := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    rw [modE, List.filterMap_cons, ← modE, cf_cons, ← ih]
    by_cases h : e.2.2 % ((2 : ℕ) : ℤ) = 0
    · have h0 : (e.2.2 : R) = 0 := by
        rw [← intCast_emod_two h2]
        push_cast at h ⊢
        rw [h, Int.cast_zero]
      simp only [h, if_true]
      simp [h0]
    · simp only [h, if_false]
      rw [cf_cons]
      push_cast
      rw [intCast_emod_two h2]

theorem cf_canonE (A : List Entry) (c r : ℕ) : cf R (canonE A) c r = cf R A c r := by
  rw [canonE, cf_filter, cf_combineE]
  exact ((msortF_perm' 16 A).map _).sum_eq

theorem redW_coeff {s : R} (hs : s ^ 2 + s + 1 = 0) (x : PEntry) (c r : ℕ) :
    cf R (redW 0 x) c r + s * cf R (redW 1 x) c r =
      if x.2.1 = c ∧ x.2.2.1 = r then s ^ x.1.1 * (x.2.2.2 : R) else 0 := by
  have h3 : s ^ 3 = 1 := by linear_combination (s - 1) * hs
  have hpow : s ^ x.1.1 = s ^ (x.1.1 % 3) := by
    conv_lhs => rw [← Nat.div_add_mod x.1.1 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hpow]
  rcases (by omega : x.1.1 % 3 = 0 ∨ x.1.1 % 3 = 1 ∨ x.1.1 % 3 = 2) with h | h | h
  · simp only [redW, h, if_true, show (0 : ℕ) ≠ 2 by omega, show (0 : ℕ) ≠ 1 by omega,
      if_false, cf_cons, cf_nil]
    split_ifs <;> ring
  · simp only [redW, h, if_true, show (1 : ℕ) ≠ 2 by omega, show (1 : ℕ) ≠ 0 by omega,
      if_false, cf_cons, cf_nil]
    split_ifs <;> ring
  · simp only [redW, h, if_true, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
      if_false, cf_cons, cf_nil]
    split_ifs
    · push_cast
      linear_combination (-(x.2.2.2 : R)) * hs
    · ring

theorem cp_normW (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) (X : List PEntry)
    (c r : ℕ) : cp R (normW X) s c r = cp R X s c r := by
  rw [normW, cp_append, cp_map_deg, cp_map_deg, cf_modE h2, cf_modE h2, cf_canonE, cf_canonE,
    pow_zero, one_mul, pow_one]
  induction X with
  | nil => simp [cf_nil, cp_nil]
  | cons x X ih =>
    rw [List.flatMap_cons, List.flatMap_cons, cf_append, cf_append, cp_cons, ← ih,
      ← redW_coeff hs x c r]
    ring

theorem cp_filter_map (A : List PEntry) (y : PEntry) (s : R) (c r : ℕ) :
    cp R ((A.filter fun x => Nat.beq x.2.1 y.2.2.1).map fun x =>
        ((x.1.1 + y.1.1, x.1.2 + y.1.2), (y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2))) s c r =
      if y.2.1 = c then cp R A s y.2.2.1 r * (s ^ y.1.1 * (y.2.2.2 : R)) else 0 := by
  induction A with
  | nil => simp [cp_nil]
  | cons x A ih =>
    rw [List.filter_cons]
    cases hb : Nat.beq x.2.1 y.2.2.1
    · have h : x.2.1 ≠ y.2.2.1 := fun h => by rw [h, Nat.beq_refl] at hb; cases hb
      simp only [Bool.false_eq_true, if_false, ih, cp_cons, h, false_and, zero_add]
    · have h : x.2.1 = y.2.2.1 := Nat.eq_of_beq_eq_true hb
      simp only [if_true, List.map_cons, cp_cons, ih, h, true_and]
      by_cases hc : y.2.1 = c <;> by_cases hr : x.2.2.1 = r <;> simp [hc, hr, pow_add] <;> ring

theorem cp_pmul {w : ℕ} (A : List PEntry) {B : List PEntry} (hB : ∀ y ∈ B, y.2.2.1 < w)
    (s : R) (c r : ℕ) :
    cp R (pmul A B) s c r = ∑ m ∈ Finset.range w, cp R A s m r * cp R B s c m := by
  induction B with
  | nil => simp [pmul, cp_nil]
  | cons y B ih =>
    rw [pmul, List.flatMap_cons, cp_append, ← pmul, ih fun y' hy' => hB y' (List.mem_cons_of_mem _ hy'),
      cp_filter_map]
    have hy : y.2.2.1 ∈ Finset.range w := Finset.mem_range.2 (hB y List.mem_cons_self)
    simp only [cp_cons, mul_add, Finset.sum_add_distrib]
    congr 1
    by_cases hc : y.2.1 = c
    · simp [hc, mul_ite, Finset.sum_ite_eq, hy]
    · simp [hc]

theorem cp_map_k (D : List Entry) (k ea eb : ℕ) (C : ℤ) (s : R) (c r : ℕ) :
    cp R (D.map fun e => ((k * ea, k * eb), (e.1, e.2.1, C ^ k * e.2.2))) s c r =
      ((C : R) * s ^ ea) ^ k * cf R D c r := by
  induction D with
  | nil => simp [cp_nil, cf_nil]
  | cons e D ih =>
    rw [List.map_cons, cp_cons, ih, cf_cons]
    simp only
    split_ifs
    · push_cast
      ring
    · ring

theorem cp_nilpE (τ : Tag) (g : ℕ) (C : ℤ) (ea : ℕ) (s : R) (c r : ℕ) :
    cp R (nilpE τ g C ea 0) s c r =
      ((C : R) * s ^ ea) ^ 1 * cf R (entries τ g 1) c r +
        ((C : R) * s ^ ea) ^ 2 * cf R (entries τ g 2) c r +
        ((C : R) * s ^ ea) ^ 3 * cf R (entries τ g 3) c r := by
  simp only [nilpE, List.flatMap_cons, List.flatMap_nil, List.append_nil, cp_append, cp_map_k]
  ring

theorem sum_mul_cf {w : ℕ} (F : ℕ → R) (A : List Entry) (hA : ∀ e ∈ A, e.2.1 < w) (c : ℕ) :
    ∑ m ∈ Finset.range w, F m * cf R A c m =
      (A.map fun e => if e.1 = c then (e.2.2 : R) * F e.2.1 else 0).sum := by
  induction A with
  | nil => simp [cf_nil]
  | cons e A ih =>
    rw [List.map_cons, List.sum_cons, ← ih fun e' he' => hA e' (List.mem_cons_of_mem _ he')]
    simp only [cf_cons, mul_add, Finset.sum_add_distrib]
    congr 1
    have he : e.2.1 ∈ Finset.range w := Finset.mem_range.2 (hA e List.mem_cons_self)
    by_cases hc : e.1 = c
    · simp [hc, mul_ite, Finset.sum_ite_eq, he]
      ring
    · simp [hc]

def bR (b : Bool) : R := if b then 1 else 0

variable (R) in
noncomputable def pv (w : ℕ) (s : R) (M : ℕ × ℕ) (c r : ℕ) : R :=
  bR (M.1.testBit (w * c + r)) + s * bR (M.2.testBit (w * c + r))

theorem bR_xor (h2 : (2 : R) = 0) (a b : Bool) : (bR (a ^^ b) : R) = bR a + bR b := by
  have h11 : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  cases a <;> cases b <;> simp [bR, h11]

theorem testBit_xor' (a b i : ℕ) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

theorem pv_xor (h2 : (2 : R) = 0) (w : ℕ) (s : R) (M D : ℕ × ℕ) (c r : ℕ) :
    pv R w s (Nat.xor M.1 D.1, Nat.xor M.2 D.2) c r = pv R w s M c r + pv R w s D c r := by
  unfold pv
  simp only [testBit_xor', bR_xor h2]
  ring

local notation "OPcol" => _root_.Certificates.OmegaPacked.colOf

theorem testBit_colOf (w U k i : ℕ) :
    (OPcol w (2 ^ w - 1) U k).testBit i = (decide (i < w) && U.testBit (w * k + i)) := by
  unfold _root_.Certificates.OmegaPacked.colOf
  change ((U >>> (w * k)) &&& (2 ^ w - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem testBit_shift_col {w X c c' r : ℕ} (hr : r < w)
    (hX : ∀ i, w ≤ i → X.testBit i = false) :
    (Nat.shiftLeft X (Nat.mul w c')).testBit (w * c + r) = (decide (c = c') && X.testBit r) := by
  change (X <<< (w * c')).testBit (w * c + r) = _
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy c c' with h | rfl | h
  · have h1 := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at h1
    have h' : ¬(w * c + r ≥ w * c') := by omega
    simp [h', h.ne]
  · simp
  · have h1 := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at h1
    have := hX (w * c + r - w * c') (by omega)
    simp [this, h.ne']

theorem intCast_parity (h2 : (2 : R) = 0) (z : ℤ) :
    (z : R) = if z.natAbs % 2 = 0 then 0 else 1 := by
  rw [← intCast_emod_two h2]
  have key : z.natAbs % 2 = 0 ↔ z % 2 = 0 := by
    rcases Int.natAbs_eq z with h | h <;> omega
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · rw [h, if_pos (key.2 h)]
    simp
  · rw [h, if_neg (by rw [key, h]; omega)]
    simp

theorem pv_stepE (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {w U V d c r : ℕ}
    {D : ℕ × ℕ} {e : Entry} (hd : d < 3) (hr : r < w) :
    pv R w s (stepE w (2 ^ w - 1) U V d D e) c r =
      pv R w s D c r + if e.1 = c then (e.2.2 : R) * s ^ d * pv R w s (U, V) e.2.1 r else 0 := by
  have hz := intCast_parity h2 e.2.2
  unfold stepE
  by_cases hp : e.2.2.natAbs % 2 = 0
  · simp [Nat.beq_eq, hp, hz]
  rw [if_neg (by simpa [Nat.beq_eq] using hp)]
  rw [if_neg hp] at hz
  rw [hz]
  have hcol : ∀ X, (X = U ∨ X = V) → ∀ i, w ≤ i → (OPcol w (2 ^ w - 1) X e.2.1).testBit i = false :=
    fun X _ i hi => by rw [testBit_colOf]; simp; omega
  have hU := testBit_shift_col (c := c) (c' := e.1) hr (hcol U (.inl rfl))
  have hV := testBit_shift_col (c := c) (c' := e.1) hr (hcol V (.inr rfl))
  have hUV := testBit_shift_col (c := c) (c' := e.1)
    (X := Nat.xor (OPcol w (2 ^ w - 1) U e.2.1) (OPcol w (2 ^ w - 1) V e.2.1)) hr
    (fun i hi => by rw [testBit_xor', hcol U (.inl rfl) i hi, hcol V (.inr rfl) i hi]; rfl)
  rw [testBit_xor', testBit_colOf, testBit_colOf] at hUV
  rw [testBit_colOf] at hU hV
  unfold pv
  simp only
  interval_cases d
  · simp only [Nat.beq_refl, if_true, testBit_xor', hU, hV, bR_xor h2]
    by_cases hc : c = e.1
    · simp [hc, hr]
      ring
    · simp [hc, Ne.symm hc, bR]
  · simp only [Nat.beq_refl, if_true, testBit_xor', hU, hV, hUV, bR_xor h2,
      show Nat.beq 1 0 = false from rfl, Bool.false_eq_true, if_false]
    by_cases hc : c = e.1
    · simp only [hc, decide_true, Bool.true_and, hr, decide_true, if_true, bR_xor h2]
      linear_combination (bR (V.testBit (w * e.2.1 + r)) : R) * hs -
        ((bR (V.testBit (w * e.2.1 + r)) : R) * s ^ 2) * h2
    · simp [hc, Ne.symm hc, bR]
  · simp only [testBit_xor', hU, hV, hUV, bR_xor h2,
      show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
      Bool.false_eq_true, if_false]
    by_cases hc : c = e.1
    · simp only [hc, decide_true, Bool.true_and, hr, decide_true, if_true, bR_xor h2]
      linear_combination (bR (U.testBit (w * e.2.1 + r)) : R) * hs -
        ((bR (U.testBit (w * e.2.1 + r)) : R) * s ^ 2) * h2 +
        ((bR (V.testBit (w * e.2.1 + r)) : R) * (1 - s)) * hs
    · simp [hc, Ne.symm hc, bR]

theorem pv_foldl_stepE (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {w U V d c r : ℕ}
    (hd : d < 3) (hr : r < w) : ∀ (l : List Entry) (D : ℕ × ℕ),
    pv R w s (l.foldl (stepE w (2 ^ w - 1) U V d) D) c r = pv R w s D c r +
      (l.map fun e => if e.1 = c then (e.2.2 : R) * s ^ d * pv R w s (U, V) e.2.1 r else 0).sum
  | [], D => by simp
  | e :: l, D => by
    rw [List.foldl_cons, pv_foldl_stepE h2 hs hd hr l, pv_stepE h2 hs hd hr, List.map_cons,
      List.sum_cons, add_assoc]

theorem pv_zero (w : ℕ) (s : R) (c r : ℕ) : pv R w s (0, 0) c r = 0 := by
  simp [pv, bR]

theorem stepE_sum (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {w : ℕ} (M : ℕ × ℕ)
    (D : List Entry) (hD : ∀ e ∈ D, e.2.1 < w) (k p c r : ℕ) :
    (D.map fun e => if e.1 = c then (e.2.2 : R) * s ^ ((k * p) % 3) * pv R w s M e.2.1 r
      else 0).sum =
      (s ^ p) ^ k * ∑ m ∈ Finset.range w, pv R w s M m r * cf R D c m := by
  have h3 : s ^ 3 = 1 := by linear_combination (s - 1) * hs
  have hpow : s ^ ((k * p) % 3) = (s ^ p) ^ k := by
    rw [← pow_mul, mul_comm p k]
    conv_rhs => rw [← Nat.div_add_mod (k * p) 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [sum_mul_cf _ D hD, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  split_ifs
  · rw [hpow]
    ring
  · ring

theorem pv_stepF (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {τ : Tag} {w c r : ℕ}
    {M : ℕ × ℕ} {f : ℕ × ℤ × ℕ} (hr : r < w)
    (hf : ∀ k ∈ [1, 2, 3], ∀ e ∈ entries τ f.1 k, e.1 < w ∧ e.2.1 < w) :
    pv R w s (stepF τ w (2 ^ w - 1) M f) c r = pv R w s M c r +
      ∑ m ∈ Finset.range w,
        pv R w s M m r * cp R (nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0) s c m := by
  have hC := intCast_parity h2 (famSign τ f.1 * f.2.1)
  simp only [cp_nilpE, mul_add, Finset.sum_add_distrib, mul_left_comm _ (((_ : ℤ) : R) * _ ^ _) _,
    ← Finset.mul_sum]
  unfold stepF
  by_cases hp : (famSign τ f.1 * f.2.1).natAbs % 2 = 0
  · rw [if_pos hp] at hC
    simp [Nat.beq_eq, hp, hC]
  rw [if_neg (by simpa [Nat.beq_eq] using hp)]
  rw [if_neg hp] at hC
  rw [hC]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [pv_xor h2]
  have hd : ∀ k, (k * f.2.2) % 3 < 3 := fun k => Nat.mod_lt _ (by omega)
  have hD : ∀ k ∈ [1, 2, 3], ∀ e ∈ entries τ f.1 k, e.2.1 < w := fun k hk e he => (hf k hk e he).2
  rw [pv_foldl_stepE h2 hs (hd 3) hr, pv_foldl_stepE h2 hs (hd 2) hr,
    pv_foldl_stepE h2 hs (hd 1) hr, pv_zero, stepE_sum h2 hs M _ (hD 1 (by simp)),
    stepE_sum h2 hs M _ (hD 2 (by simp)), stepE_sum h2 hs M _ (hD 3 (by simp))]
  simp only [Prod.mk.eta, one_mul, Finset.mul_sum, mul_assoc]
  ring_nf

theorem testBit_foldl_lor (w j : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    (l.foldl (fun a i => Nat.lor a (Nat.shiftLeft 1 (Nat.mul (w + 1) i))) a).testBit j =
      (a.testBit j || l.any fun i => decide (j = (w + 1) * i))
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, testBit_foldl_lor w j l, List.any_cons]
    change ((a ||| 1 <<< ((w + 1) * i)).testBit j || _) = _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [Bool.or_assoc, eq_comm]

theorem testBit_idU {w c r : ℕ} (hc : c < w) (hr : r < w) :
    (idU w).testBit (w * c + r) = decide (c = r) := by
  unfold idU
  rw [testBit_foldl_lor, Nat.zero_testBit, Bool.false_or, Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    have hci : c = i := by
      rcases Nat.lt_trichotomy c i with h1 | h1 | h1
      · have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h1)
        rw [Nat.mul_succ] at this
        nlinarith
      · exact h1
      · have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h1)
        rw [Nat.mul_succ] at this
        nlinarith
    subst hci
    nlinarith
  · rintro rfl
    exact ⟨c, hc, by ring⟩

theorem pv_idU (w : ℕ) (s : R) {c r : ℕ} (hc : c < w) (hr : r < w) :
    pv R w s (idU w, 0) c r = if c = r then 1 else 0 := by
  unfold pv
  rw [testBit_idU hc hr]
  simp [bR]

theorem pv_foldl_stepF (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {τ : Tag} {w : ℕ} :
    ∀ (fs : List (ℕ × ℤ × ℕ)) (acc : List PEntry) (M : ℕ × ℕ),
      (∀ f ∈ fs, ∀ k ∈ [1, 2, 3], ∀ e ∈ entries τ f.1 k, e.1 < w ∧ e.2.1 < w) →
      (∀ c r, c < w → r < w → pv R w s M c r = (if c = r then 1 else 0) + cp R acc s c r) →
      ∀ c r, c < w → r < w → pv R w s (fs.foldl (stepF τ w (2 ^ w - 1)) M) c r =
        (if c = r then 1 else 0) + cp R (omegaProd τ acc fs) s c r
  | [], acc, M, _, hM => by simpa [omegaProd] using hM
  | f :: fs, acc, M, hfs, hM => by
    rw [List.foldl_cons, omegaProd]
    refine pv_foldl_stepF h2 hs fs _ _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) ?_
    intro c r hc hr
    have hf := hfs f List.mem_cons_self
    have hN : ∀ y ∈ nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0, y.2.2.1 < w := by
      intro y hy
      obtain ⟨k, hk, e, he, -, h2⟩ := nilpE_mem hy
      rw [h2]
      exact (hf k hk e he).2
    rw [pv_stepF h2 hs hr hf, cp_normW h2 hs, mul1, cp_append, cp_append, cp_pmul _ hN,
      hM c r hc hr]
    have : ∀ m ∈ Finset.range w,
        pv R w s M m r * cp R (nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0) s c m =
          (if r = m then cp R (nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0) s c m else 0) +
            cp R acc s m r * cp R (nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0) s c m := by
      intro m hm
      rw [hM m r (Finset.mem_range.1 hm) hr]
      by_cases h : m = r
      · subst h
        simp
        ring
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_range, hr, if_true]
    ring

theorem cf_good {w : ℕ} {A : List Entry} (hA : Good w A) (c r : ℕ) :
    cf R A c r = if (c, r, (1 : ℤ)) ∈ A then 1 else 0 := by
  induction A with
  | nil => simp [cf_nil]
  | cons e A ih =>
    obtain ⟨hp, hv⟩ := hA
    rw [List.pairwise_cons] at hp
    rw [cf_cons, ih ⟨hp.2, fun x hx => hv x (List.mem_cons_of_mem _ hx)⟩]
    have he1 := (hv e List.mem_cons_self).1
    by_cases hk : e.1 = c ∧ e.2.1 = r
    · have he : e = (c, r, 1) := Prod.ext hk.1 (Prod.ext hk.2 he1)
      have hn : (c, r, (1 : ℤ)) ∉ A := fun h => by
        have := hp.1 _ h
        rw [he] at this
        unfold KLt at this
        simp at this
      simp [hk, he1, hn, he]
    · have hne : (c, r, (1 : ℤ)) ≠ e := fun h => hk ⟨by rw [← h], by rw [← h]⟩
      simp [hk, List.mem_cons, hne]

theorem ind_inj [Nontrivial R] (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0)
    {p0 p1 q0 q1 : Prop} [Decidable p0] [Decidable p1] [Decidable q0] [Decidable q1]
    (h : ((if p0 then 1 else 0) + s * (if p1 then 1 else 0) : R) =
      (if q0 then 1 else 0) + s * (if q1 then 1 else 0)) : (p0 ↔ q0) ∧ (p1 ↔ q1) := by
  have h10 : (1 : R) ≠ 0 := one_ne_zero
  have hs0 : s ≠ 0 := fun h0 => h10 (by rw [h0] at hs; simpa using hs)
  have hs1 : s + 1 ≠ 0 := fun h1 => h10 (by linear_combination hs - s * h1)
  by_cases a : p0 <;> by_cases b : p1 <;> by_cases c : q0 <;> by_cases d : q1 <;>
    simp only [a, b, c, d, if_true, if_false, mul_one, mul_zero, add_zero, zero_add,
      iff_true, iff_false, true_iff, false_iff, not_true, not_false_eq_true, and_true,
      and_false, true_and, false_and] at h ⊢
  all_goals first
    | exact h10 h | exact h10 h.symm | exact hs0 h | exact hs0 h.symm
    | exact hs1 (by linear_combination h) | exact hs1 (by linear_combination -h)
    | exact hs1 (by linear_combination -h + h2) | exact hs1 (by linear_combination h + h2)
    | exact hs0 (by linear_combination -h) | exact hs0 (by linear_combination h)
    | exact h10 (by linear_combination -h) | exact h10 (by linear_combination h)

theorem cp_canon {w : ℕ} {X : List PEntry} {A0 A1 : List Entry} (h0 : Good w A0)
    (h1 : Good w A1) (hX : X = A0.map (fun e => ((0, 0), e)) ++ A1.map (fun e => ((1, 0), e)))
    (s : R) (c r : ℕ) :
    cp R X s c r = (if (c, r, (1 : ℤ)) ∈ A0 then 1 else 0) +
      s * (if (c, r, (1 : ℤ)) ∈ A1 then 1 else 0) := by
  rw [hX, cp_append, cp_map_deg, cp_map_deg, cf_good h0, cf_good h1, pow_zero, one_mul, pow_one]

theorem good_mem_iff {w : ℕ} {A B : List Entry} (hA : Good w A) (hB : Good w B)
    (h : ∀ c r, c < w → r < w → ((c, r, (1 : ℤ)) ∈ A ↔ (c, r, (1 : ℤ)) ∈ B)) : A = B := by
  refine eq_of_mem_iff hA.1 hB.1 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hA.2 x hx
    have : x = (x.1, x.2.1, 1) := Prod.ext rfl (Prod.ext rfl h1)
    rw [this] at hx ⊢
    exact (h _ _ h2 h3).1 hx
  · obtain ⟨h1, h2, h3⟩ := hB.2 x hx
    have : x = (x.1, x.2.1, 1) := Prod.ext rfl (Prod.ext rfl h1)
    rw [this] at hx ⊢
    exact (h _ _ h2 h3).2 hx

theorem canon_inj [Nontrivial R] (h2 : (2 : R) = 0) {s : R} (hs : s ^ 2 + s + 1 = 0) {w : ℕ}
    {X Y : List PEntry} (hX : Canon w X) (hY : Canon w Y)
    (h : ∀ c r, c < w → r < w → cp R X s c r = cp R Y s c r) : X = Y := by
  obtain ⟨A0, A1, ha0, ha1, hXe⟩ := hX
  obtain ⟨B0, B1, hb0, hb1, hYe⟩ := hY
  have key : ∀ c r, c < w → r < w → (((c, r, (1 : ℤ)) ∈ A0 ↔ (c, r, (1 : ℤ)) ∈ B0) ∧
      ((c, r, (1 : ℤ)) ∈ A1 ↔ (c, r, (1 : ℤ)) ∈ B1)) := fun c r hc hr => ind_inj h2 hs (by
    rw [← cp_canon ha0 ha1 hXe s c r, ← cp_canon hb0 hb1 hYe s c r]
    exact h c r hc hr)
  rw [hXe, hYe, good_mem_iff ha0 hb0 fun c r hc hr => (key c r hc hr).1,
    good_mem_iff ha1 hb1 fun c r hc hr => (key c r hc hr).2]

end Coeff

end OmegaPackedS

open OmegaPackedS Polynomial CFSG.LieType.Chevalley.RootOps in
theorem omegaCheck_of_omegaCheckP {τ : Tag} {L L' : List (ℕ × ℤ × ℕ)}
    (h : omegaCheckP τ L L' = true) : omegaCheck τ L L' = true := by
  simp only [omegaCheckP, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hall, hU⟩, hV⟩ := h
  have hm : Nat.shiftLeft 1 (dim τ) - 1 = 2 ^ dim τ - 1 := by
    change 1 <<< dim τ - 1 = _
    rw [Nat.shiftLeft_eq, one_mul]
  rw [hm] at hU hV
  have hok : ∀ f ∈ L ++ L', entriesOk τ (dim τ) f.1 = true := fun f hf => (hall f hf).2
  have hpos : ∀ f ∈ L ++ L', f.1 < τ.rootCertificate.roots.length := fun f hf =>
    Nat.blt_eq.mp (hall f hf).1
  let R := AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 2 := by compute_degree!
  have hR : Nontrivial R := AdjoinRoot.nontrivial _ (by rw [hdeg]; decide)
  have h2 : (2 : R) = 0 := by
    have : ((2 : ZMod 2) : ZMod 2) = 0 := rfl
    rw [← map_ofNat (AdjoinRoot.of (X ^ 2 + X + 1 : (ZMod 2)[X])) 2, this, map_zero]
  have hs : (AdjoinRoot.root (X ^ 2 + X + 1 : (ZMod 2)[X])) ^ 2 +
      AdjoinRoot.root (X ^ 2 + X + 1 : (ZMod 2)[X]) + 1 = 0 := by
    have := AdjoinRoot.eval₂_root (X ^ 2 + X + 1 : (ZMod 2)[X])
    simpa using this
  have hnil : Canon (dim τ) ([] : List PEntry) :=
    ⟨[], [], ⟨List.Pairwise.nil, by simp⟩, ⟨List.Pairwise.nil, by simp⟩, rfl⟩
  have key : ∀ L₀ : List (ℕ × ℤ × ℕ), (∀ f ∈ L₀, entriesOk τ (dim τ) f.1 = true) →
      ∀ c r, c < dim τ → r < dim τ →
        pv R (dim τ) (AdjoinRoot.root _) (prodP τ (dim τ) (2 ^ dim τ - 1) L₀) c r =
          (if c = r then 1 else 0) + cp R (omegaProd τ [] L₀) (AdjoinRoot.root _) c r := by
    intro L₀ hL₀
    refine pv_foldl_stepF h2 hs L₀ [] _ (fun f hf => (entriesOk_spec (hL₀ f hf)).1) ?_
    intro c r hc hr
    rw [pv_idU _ _ hc hr, cp_nil, add_zero]
  have heq : omegaProd τ [] L = omegaProd τ [] L' := by
    refine canon_inj h2 hs (omegaProd_canon L [] hnil fun f hf => hok f (List.mem_append_left _ hf))
      (omegaProd_canon L' [] hnil fun f hf => hok f (List.mem_append_right _ hf)) ?_
    intro c r hc hr
    have e1 := key L (fun f hf => hok f (List.mem_append_left _ hf)) c r hc hr
    have e2 := key L' (fun f hf => hok f (List.mem_append_right _ hf)) c r hc hr
    have hP : prodP τ (dim τ) (2 ^ dim τ - 1) L = prodP τ (dim τ) (2 ^ dim τ - 1) L' :=
      Prod.ext hU hV
    rw [hP] at e1
    exact add_left_cancel (e1.symm.trans e2)
  simp only [omegaCheck, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq]
  exact ⟨hpos, heq⟩

end CFSG.Certificates.Kernel
