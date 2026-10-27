module

public import Certificates.Data.Kernel.AS91I43

public section

namespace Certificates.Kernel.AS91I43

open CFSG.GF2Type.Smith1979.GammaU CFSG.Quasithin.H13.AS91.Two

theorem s7xx3 (y a b : ℕ) : (y ^^^ a) ^^^ b = (y ^^^ b) ^^^ a := by ac_rfl

theorem s7xx4 (y b : ℕ) : (y ^^^ b) ^^^ b = y := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem s7xx1 (y z b : ℕ) : (y ^^^ b) ^^^ (z ^^^ b) = y ^^^ z := by
  rw [← Nat.xor_assoc, s7xx3 y b z, s7xx4]

@[expose] def s7spn : List ℕ → ℕ → Prop
  | [], y => y = 0
  | b :: B, y => s7spn B y ∨ s7spn B (y ^^^ b)

theorem s7spn_zero : ∀ B : List ℕ, s7spn B 0
  | [] => rfl
  | _ :: B => Or.inl (s7spn_zero B)

theorem s7spn_xor : ∀ (B : List ℕ) (y z : ℕ), s7spn B y → s7spn B z → s7spn B (y ^^^ z)
  | [], y, z, hy, hz => by
    change y = 0 at hy
    change z = 0 at hz
    subst hy hz
    rfl
  | b :: B, y, z, hy, hz => by
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact Or.inl (s7spn_xor B _ _ hy hz)
    · right
      have := s7spn_xor B _ _ hy hz
      rwa [← Nat.xor_assoc] at this
    · right
      have := s7spn_xor B _ _ hy hz
      rwa [s7xx3] at this
    · left
      have := s7spn_xor B _ _ hy hz
      rwa [s7xx1] at this

theorem s7spn_perm {B C : List ℕ} (h : B.Perm C) : ∀ y, s7spn B y ↔ s7spn C y := by
  induction h with
  | nil => intro y; exact Iff.rfl
  | cons x _ ih => intro y; simp only [s7spn, ih]
  | swap x z l =>
    intro y
    simp only [s7spn, s7xx3 y x z]
    tauto
  | trans _ _ ih1 ih2 => intro y; rw [ih1, ih2]

theorem s7spn_self (x : ℕ) (B : List ℕ) : s7spn (x :: B) x :=
  Or.inr (by rw [Nat.xor_self]; exact s7spn_zero B)

theorem s7spn_append {P : List ℕ} {y : ℕ} (h : s7spn P y) (Q : List ℕ) : s7spn (P ++ Q) y := by
  rw [s7spn_perm List.perm_append_comm]
  induction Q with
  | nil => exact h
  | cons q Q ih => exact Or.inl ih

theorem s7spn_sub {P : List ℕ} : ∀ (Q : List ℕ), (∀ q ∈ Q, s7spn P q) → ∀ y, s7spn Q y → s7spn P y
  | [], _, y, hy => by
    change y = 0 at hy
    subst hy
    exact s7spn_zero P
  | q :: Q, hQ, y, hy => by
    have hQ' : ∀ q' ∈ Q, s7spn P q' := fun q' h' => hQ q' (List.mem_cons_of_mem _ h')
    rcases hy with hy | hy
    · exact s7spn_sub Q hQ' y hy
    · have := s7spn_xor P _ _ (s7spn_sub Q hQ' _ hy) (hQ q List.mem_cons_self)
      rwa [s7xx4] at this

theorem s7spn_lt : ∀ (B : List ℕ) (k : ℕ), (∀ c ∈ B, c < 2 ^ k) → ∀ y, s7spn B y → y < 2 ^ k
  | [], k, _, y, hy => by
    change y = 0 at hy
    subst hy
    exact Nat.two_pow_pos k
  | c :: B, k, hB, y, hy => by
    have hB' : ∀ c' ∈ B, c' < 2 ^ k := fun c' h' => hB c' (List.mem_cons_of_mem _ h')
    rcases hy with hy | hy
    · exact s7spn_lt B k hB' y hy
    · rw [← s7xx4 y c]
      exact Nat.xor_lt_two_pow (s7spn_lt B k hB' _ hy) (hB c List.mem_cons_self)

@[expose] def s7E : List ℕ → List ℕ
  | [] => [0]
  | b :: B => s7E B ++ (s7E B).map (· ^^^ b)

theorem s7E_mem : ∀ (B : List ℕ) (y : ℕ), y ∈ s7E B ↔ s7spn B y
  | [], y => by simp [s7E, s7spn, eq_comm]
  | b :: B, y => by
    simp only [s7E, s7spn, List.mem_append, List.mem_map, s7E_mem B]
    refine or_congr Iff.rfl ⟨?_, fun h => ⟨_, h, s7xx4 y b⟩⟩
    rintro ⟨a, ha, rfl⟩
    rwa [s7xx4]

theorem s7E_length : ∀ B : List ℕ, (s7E B).length = 2 ^ B.length
  | [] => rfl
  | b :: B => by
    simp only [s7E, List.length_append, List.length_map, s7E_length B, List.length_cons,
      Nat.pow_succ]
    omega

@[expose] def s7ind : List ℕ → Prop
  | [] => True
  | b :: B => ¬ s7spn B b ∧ s7ind B

theorem s7E_nodup : ∀ B : List ℕ, s7ind B → (s7E B).Nodup
  | [], _ => by simp [s7E]
  | b :: B, ⟨hb, hB⟩ => by
    rw [s7E, List.nodup_append]
    refine ⟨s7E_nodup B hB, ?_, ?_⟩
    · refine (s7E_nodup B hB).map ?_
      intro u v huv
      have := congrArg (· ^^^ b) huv
      simpa only [s7xx4] using this
    · intro u hu v hv huv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      apply hb
      have := s7spn_xor B _ _ ((s7E_mem B u).1 hu) ((s7E_mem B w).1 hw)
      rwa [huv, Nat.xor_comm w b, s7xx4] at this

theorem s7pigeon {Q P : List ℕ} (hQ : s7ind Q) (hQl : Q.length = 7)
    (hsub : ∀ q ∈ Q, s7spn P q) : 7 ≤ P.length := by
  have hle := ((s7E_nodup Q hQ).subperm fun y hy =>
    (s7E_mem P y).2 (s7spn_sub Q hsub y ((s7E_mem Q y).1 hy))).length_le
  rw [s7E_length, s7E_length, hQl] at hle
  by_contra hne
  have h6 : P.length ≤ 6 := by omega
  have := Nat.pow_le_pow_right (n := 2) (by norm_num) h6
  norm_num at hle this
  omega

@[expose] def s7ech (B : List ℕ) : Prop :=
  (∀ b ∈ B, b ≠ 0) ∧ B.Pairwise (fun a b => b.log2 < a.log2)

theorem s7hi {b j : ℕ} (hj : b.log2 < j) : b.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hj))

theorem s7xlt (x b : ℕ) (hb : b ≠ 0) : x ^^^ b < x ↔ x.testBit b.log2 = true := by
  have hk := Nat.testBit_log2 hb
  constructor
  · intro hlt
    by_contra hx
    have hx' : x.testBit b.log2 = false := by simpa using hx
    have : x < x ^^^ b := Nat.lt_of_testBit b.log2 hx' (by simp [hx', hk])
      (fun j hj => by simp [s7hi hj])
    omega
  · intro hx
    exact Nat.lt_of_testBit b.log2 (by simp [hx, hk]) hx (fun j hj => by simp [s7hi hj])

theorem s7blt_false {a b : ℕ} (h : Nat.blt a b = false) : ¬ a < b := fun hlt => by
  have e : Nat.blt a b = true := by simpa using hlt
  rw [e] at h
  exact absurd h (by decide)

theorem s7blt_of_not {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (by simpa using e) h

theorem s7redB_cons (b : ℕ) (B : List ℕ) (x : ℕ) :
    redB (b :: B) x = redB B (bif Nat.blt (x ^^^ b) x then x ^^^ b else x) := rfl

theorem s7red_spn : ∀ (B : List ℕ) (x : ℕ), s7spn B (redB B x ^^^ x)
  | [], x => by
    change s7spn [] (x ^^^ x)
    rw [Nat.xor_self]
    rfl
  | b :: B, x => by
    rw [s7redB_cons]
    cases Nat.blt (x ^^^ b) x
    · exact Or.inl (s7red_spn B x)
    · right
      have := s7red_spn B (x ^^^ b)
      rwa [← Nat.xor_assoc] at this

theorem s7red_hi : ∀ (B : List ℕ) (x k : ℕ), (∀ c ∈ B, c < 2 ^ k) → ∀ j, k ≤ j →
    (redB B x).testBit j = x.testBit j
  | [], _, _, _, _, _ => rfl
  | c :: B, x, k, hB, j, hj => by
    rw [s7redB_cons, s7red_hi B _ k (fun c' h' => hB c' (List.mem_cons_of_mem _ h')) j hj]
    have hc : c.testBit j = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (hB c List.mem_cons_self) (Nat.pow_le_pow_right (by norm_num) hj))
    cases Nat.blt (x ^^^ c) x <;> simp [hc]

theorem s7ech_tail {c : ℕ} {B : List ℕ} (h : s7ech (c :: B)) : s7ech B :=
  ⟨fun d hd => h.1 d (List.mem_cons_of_mem _ hd), h.2.of_cons⟩

theorem s7ech_lt {c : ℕ} {B : List ℕ} (h : s7ech (c :: B)) : ∀ d ∈ B, d < 2 ^ c.log2 :=
  fun d hd => (Nat.log2_lt (h.1 d (List.mem_cons_of_mem _ hd))).1 (List.rel_of_pairwise_cons h.2 hd)

theorem s7red_bit : ∀ (B : List ℕ) (x : ℕ), s7ech B → ∀ b ∈ B, (redB B x).testBit b.log2 = false
  | [], _, _, b, hb => absurd hb List.not_mem_nil
  | c :: B, x, hc, b, hb => by
    rw [s7redB_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [s7red_hi B _ _ (s7ech_lt hc) _ le_rfl]
      have hb0 := hc.1 b List.mem_cons_self
      have hX := s7xlt x b hb0
      cases h : Nat.blt (x ^^^ b) x
      · have h' := s7blt_false h
        simp only [cond_false]
        cases hx : x.testBit b.log2
        · rfl
        · exact absurd (hX.2 hx) h'
      · have h' : x ^^^ b < x := by simpa using h
        simp [hX.1 h', Nat.testBit_log2 hb0]
    · exact s7red_bit B _ (s7ech_tail hc) b hb

theorem s7ech_zero : ∀ (B : List ℕ), s7ech B → ∀ y, s7spn B y →
    (∀ b ∈ B, y.testBit b.log2 = false) → y = 0
  | [], _, _, hy, _ => hy
  | c :: B, hc, y, hy, hbits => by
    rcases hy with hy | hy
    · exact s7ech_zero B (s7ech_tail hc) y hy (fun b hb => hbits b (List.mem_cons_of_mem _ hb))
    · exfalso
      have h1 := Nat.testBit_lt_two_pow (s7spn_lt B _ (s7ech_lt hc) _ hy)
      rw [Nat.testBit_xor, hbits c List.mem_cons_self,
        Nat.testBit_log2 (hc.1 c List.mem_cons_self)] at h1
      exact absurd h1 (by decide)

theorem s7red_ne {B : List ℕ} {x : ℕ} (hB : s7ech B) (hr : redB B x ≠ 0) : ¬ s7spn B x := by
  intro hx
  apply hr
  refine s7ech_zero B hB _ ?_ (s7red_bit B x hB)
  have := s7spn_xor B _ _ (s7red_spn B x) hx
  rwa [s7xx4] at this

theorem s7red_eq0 {B : List ℕ} {x : ℕ} (hr : redB B x = 0) : s7spn B x := by
  have := s7red_spn B x
  rwa [hr, Nat.zero_xor] at this

theorem s7ech_ins {B C : List ℕ} {r : ℕ} (hB : s7ech B) (hr : r ≠ 0)
    (hbits : ∀ b ∈ B, r.testBit b.log2 = false) (hp : C.Perm (r :: B))
    (hs : C.Pairwise (fun a b => b ≤ a)) : s7ech C := by
  have h0 : ∀ c ∈ C, c ≠ 0 := by
    intro c hc
    rcases List.mem_cons.1 (hp.mem_iff.1 hc) with rfl | hc
    · exact hr
    · exact hB.1 c hc
  have hD : (r :: B).Pairwise (fun a b => a.log2 ≠ b.log2) := by
    refine List.pairwise_cons.2 ⟨fun b hb he => ?_, hB.2.imp fun h => (Nat.ne_of_lt h).symm⟩
    have := hbits b hb
    rw [← he, Nat.testBit_log2 hr] at this
    exact absurd this (by decide)
  have hD' := hp.symm.pairwise hD fun h => h.symm
  refine ⟨h0, (hD'.and hs).imp_of_mem fun {a b} ha hb ⟨hne, hle⟩ => ?_⟩
  have hm : b.log2 ≤ a.log2 := by
    by_cases hb0 : b = 0
    · exact absurd hb0 (h0 b hb)
    · exact (Nat.le_log2 (h0 a ha)).2 (le_trans (Nat.log2_self_le hb0) hle)
  omega

@[expose] def s7G (ins : ℕ → List ℕ → List ℕ) (st : List ℕ × List ℕ) (x : ℕ) :
    List ℕ × List ℕ :=
  if 7 ≤ st.2.length then st else
    if redB st.1 x = 0 then st else (ins (redB st.1 x) st.1, st.2 ++ [x])

@[expose] def s7Inv (S : List ℕ) (st : List ℕ × List ℕ) : Prop :=
  s7ech st.1 ∧ (∀ y, s7spn st.1 y ↔ s7spn st.2 y) ∧ s7ind st.2.reverse ∧ (∀ p ∈ st.2, p ∈ S)

theorem s7Inv_nil (S : List ℕ) : s7Inv S ([], []) :=
  ⟨⟨by simp, List.Pairwise.nil⟩, fun _ => Iff.rfl, trivial, by simp⟩

@[expose] def s7InsOK (ins : ℕ → List ℕ → List ℕ) : Prop :=
  ∀ r B, B.Pairwise (fun a b => b ≤ a) →
    (ins r B).Perm (r :: B) ∧ (ins r B).Pairwise (fun a b => b ≤ a)

theorem s7ech_dec {B : List ℕ} (hB : s7ech B) : B.Pairwise (fun a b => b ≤ a) :=
  hB.2.imp_of_mem fun {a b} ha _ h => Nat.le_of_lt (lt_of_lt_of_le Nat.lt_log2_self
    (le_trans (Nat.pow_le_pow_right (by norm_num) h) (Nat.log2_self_le (hB.1 a ha))))

theorem s7step (ins : ℕ → List ℕ → List ℕ) (hins : s7InsOK ins) (S : List ℕ)
    (st : List ℕ × List ℕ) (x : ℕ) (hI : s7Inv S st) (hl : st.2.length ≤ 7) (hx : x ∈ S) :
    s7Inv S (s7G ins st x) ∧ (s7G ins st x).2.length ≤ 7 ∧
      (7 ≤ (s7G ins st x).2.length ∨ s7spn (s7G ins st x).2 x) ∧
      ∃ Q, (s7G ins st x).2 = st.2 ++ Q := by
  obtain ⟨B, P⟩ := st
  obtain ⟨hech, hsp, hind, hmem⟩ := hI
  simp only at hech hsp hind hmem hl
  unfold s7G
  simp only
  by_cases h7 : 7 ≤ P.length
  · rw [if_pos h7]
    exact ⟨⟨hech, hsp, hind, hmem⟩, hl, Or.inl h7, [], by simp⟩
  rw [if_neg h7]
  by_cases hr : redB B x = 0
  · rw [if_pos hr]
    exact ⟨⟨hech, hsp, hind, hmem⟩, hl, Or.inr ((hsp x).1 (s7red_eq0 hr)), [], by simp⟩
  rw [if_neg hr]
  obtain ⟨hperm, hsort⟩ := hins (redB B x) B (s7ech_dec hech)
  have hnot : ¬ s7spn P x := fun h => s7red_ne hech hr ((hsp x).2 h)
  have hrx := s7red_spn B x
  refine ⟨⟨s7ech_ins hech hr (s7red_bit B x hech) hperm hsort, fun y => ?_, ?_, ?_⟩,
    by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
    Or.inr ((s7spn_perm (List.perm_append_singleton x P) x).2 (s7spn_self x P)), [x], rfl⟩
  · simp only
    rw [s7spn_perm hperm, s7spn_perm (List.perm_append_singleton x P)]
    simp only [s7spn]
    rw [hsp y, ← hsp (y ^^^ x)]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · have := s7spn_xor B _ _ h hrx
      rwa [← Nat.xor_assoc, s7xx4] at this
    · have := s7spn_xor B _ _ h hrx
      rwa [s7xx1] at this
  · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact ⟨fun h => hnot ((s7spn_perm (List.reverse_perm P) x).1 h), hind⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hmem p hp
    · rw [List.mem_singleton.1 hp]
      exact hx

theorem s7fold (ins : ℕ → List ℕ → List ℕ) (hins : s7InsOK ins) (S : List ℕ) :
    ∀ (xs : List ℕ) (st : List ℕ × List ℕ), s7Inv S st → st.2.length ≤ 7 → (∀ x ∈ xs, x ∈ S) →
      s7Inv S (xs.foldl (s7G ins) st) ∧ (xs.foldl (s7G ins) st).2.length ≤ 7 ∧
      (∀ x ∈ xs, 7 ≤ (xs.foldl (s7G ins) st).2.length ∨ s7spn (xs.foldl (s7G ins) st).2 x) ∧
      ∃ Q, (xs.foldl (s7G ins) st).2 = st.2 ++ Q
  | [], st, hI, hl, _ => ⟨hI, hl, by simp, [], by simp⟩
  | x :: xs, st, hI, hl, hS => by
    rw [List.foldl_cons]
    obtain ⟨hI1, hl1, hx1, Q1, hQ1⟩ := s7step ins hins S st x hI hl (hS x List.mem_cons_self)
    obtain ⟨hI2, hl2, hx2, Q2, hQ2⟩ :=
      s7fold ins hins S xs _ hI1 hl1 (fun y hy => hS y (List.mem_cons_of_mem _ hy))
    refine ⟨hI2, hl2, ?_, Q1 ++ Q2, by rw [hQ2, hQ1, List.append_assoc]⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [hQ2]
      rcases hx1 with h | h
      · left
        simp only [List.length_append]
        omega
      · exact Or.inr (s7spn_append h Q2)
    · exact hx2 y hy

theorem s7insD : s7InsOK insD := by
  intro r B
  induction B with
  | nil => intro _; simp [insD]
  | cons b B ih =>
    intro h
    rw [insD]
    cases hb : Nat.blt b r
    · have hrb : r ≤ b := Nat.not_lt.1 (s7blt_false hb)
      obtain ⟨hp, hs⟩ := ih h.of_cons
      refine ⟨(hp.cons b).trans (List.Perm.swap r b B), List.pairwise_cons.2 ⟨fun a ha => ?_, hs⟩⟩
      rcases List.mem_cons.1 (hp.mem_iff.1 ha) with rfl | ha
      · exact hrb
      · exact List.rel_of_pairwise_cons h ha
    · have hbr : b < r := by simpa using hb
      refine ⟨List.Perm.refl _, List.pairwise_cons.2 ⟨fun a ha => ?_, h⟩⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact Nat.le_of_lt hbr
      · exact le_trans (List.rel_of_pairwise_cons h ha) (Nat.le_of_lt hbr)

@[expose] def s7mI (r : ℕ) (B : List ℕ) : List ℕ := (r :: B).mergeSort (fun a b => decide (b ≤ a))

theorem s7mI_ok : s7InsOK s7mI := by
  intro r B _
  refine ⟨List.mergeSort_perm _ _, ?_⟩
  refine (List.pairwise_mergeSort (le := fun a b => decide (b ≤ a)) ?_ ?_ _).imp ?_
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  · intro a b h
    simpa using h

theorem s7selStep : selStep = s7G insD := by
  funext st x
  simp only [selStep, s7G, cond_eq_if, Nat.ble_eq, Nat.beq_eq]

theorem s7redB_eq (B : List ℕ) (x : ℕ) :
    B.foldl (fun acc b => if acc ^^^ b < acc then acc ^^^ b else acc) x = redB B x := by
  rw [redB]
  congr 1
  funext acc b
  by_cases h : acc ^^^ b < acc
  · have e : Nat.blt (Nat.xor acc b) acc = true := by simpa using h
    rw [if_pos h, e]
    rfl
  · have e : Nat.blt (Nat.xor acc b) acc = false := s7blt_of_not h
    rw [if_neg h, e]
    rfl

theorem s7sel7 (L : List ℕ) : sel7 L = (L.foldl (s7G s7mI) ([], [])).2.toArray := by
  rw [sel7]
  congr 3
  funext st x
  simp only [s7G, s7mI, s7redB_eq, beq_iff_eq]

theorem s7len7 {P : List ℕ} (h : P.length = 7) :
    ∃ p0 p1 p2 p3 p4 p5 p6, P = [p0, p1, p2, p3, p4, p5, p6] := by
  rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, P⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨_, _, _, _, _, _, _, rfl⟩

theorem s7appN (p0 p1 p2 p3 p4 p5 p6 : ℕ) :
    (List.range 128).map (appN [p0, p1, p2, p3, p4, p5, p6].toArray) =
      s7E [p6, p5, p4, p3, p2, p1, p0] := by
  rfl

end Certificates.Kernel.AS91I43
