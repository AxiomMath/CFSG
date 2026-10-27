module

public import Certificates.Data.Kernel.He7222.Chain
public import Mathlib.Data.Nat.Bitwise
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.PF

@[expose] def ptR (m : ℕ) (R : List ℕ) (j : ℕ) : ℕ := Nat.land (R.getD j 0) m

@[expose] def TreeAt (n w m idn : ℕ) (G : List ℕ) (b : ℕ) (R T : List ℕ) (j : ℕ) : Prop :=
  (j = 0 → ptR m R 0 = b ∧ T.getD 0 0 = idn) ∧
  (0 < j → pg w m (T.getD j 0) b = ptR m R j ∧ ∃ g < G.length, ∃ par < j,
    T.getD j 0 = pcomp n w m (G.getD g 0) (T.getD par 0))

theorem bIf_iff (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem testBit_false_of_land {s p : ℕ} (h : Nat.land s (Nat.shiftLeft 1 p) = 0) :
    s.testBit p = false := by
  have h' : (s &&& 2 ^ p) = 0 := by
    rw [← Nat.one_mul (2 ^ p), ← Nat.shiftLeft_eq]
    exact h
  have := congrArg (fun x => Nat.testBit x p) h'
  simp only [Nat.testBit_land, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at this
  exact this

theorem testBit_lor_one (s p q : ℕ) :
    (Nat.lor s (Nat.shiftLeft 1 p)).testBit q = (s.testBit q || decide (p = q)) := by
  have e : Nat.lor s (Nat.shiftLeft 1 p) = (s ||| 2 ^ p) := by
    rw [← Nat.one_mul (2 ^ p), ← Nat.shiftLeft_eq]
    rfl
  rw [e, Nat.testBit_lor, Nat.testBit_two_pow]

theorem treeW_cons (n w m idn : ℕ) (G : List ℕ) (k b : ℕ) (R T : List ℕ) (t : ℕ) (L : List ℕ)
    (j seen : ℕ) : treeW n w m idn G k b R T (t :: L) j seen =
      strictB (getS R j) (fun e =>
      strictB (Nat.land e m) (fun pt =>
      bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
      bAnd(bIf(Nat.beq j (nat_lit 0),
          bAnd(Nat.beq pt b, Nat.beq t idn),
          strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
          strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
            bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
              Nat.beq t (pcomp n w m (getS G g) (getS T par)))))))),
        strictB (Nat.succ j) (fun j' =>
          treeW n w m idn G k b R T L j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))) :=
  rfl

theorem schW_cons (n w m : ℕ) (G : List ℕ) (k b : ℕ) (R T Ref Nn : List ℕ) (s : ℕ)
    (L : List ℕ) (q : ℕ) : schW n w m G k b R T Ref Nn (s :: L) q =
      strictB (getS Ref q) (fun e =>
      strictB (Nat.land e m) (fun j =>
      strictB (Nat.shiftRight e w) (fun g =>
      strictB (getS Nn q) (fun j' =>
      bAnd(Nat.blt j (lenS R), bAnd(Nat.blt j' (lenS R), bAnd(Nat.blt g k,
      bAnd(canonK n w m (Nat.mul n w) s, bAnd(Nat.beq (pg w m s b) b,
      bAnd(Nat.beq (pcomp n w m (getS T j') s) (pcomp n w m (getS G g) (getS T j)),
        strictB (Nat.succ q) (fun q' => schW n w m G k b R T Ref Nn L q'))))))))))) :=
  rfl

theorem treeW_sound {n w m idn : ℕ} {G : List ℕ} {k b : ℕ} {R T : List ℕ} :
    ∀ (L : List ℕ) (j seen : ℕ), L = T.drop j → j ≤ T.length →
      (∀ p, seen.testBit p = true ↔ ∃ i < j, ptR m R i = p) →
      treeW n w m idn G k b R T L j seen = true →
      T.length = R.length ∧ ∀ i, j ≤ i → i < T.length →
        ((i = 0 → ptR m R 0 = b ∧ T.getD 0 0 = idn) ∧
          (0 < i → pg w m (T.getD i 0) b = ptR m R i ∧ ∃ g < k, ∃ par < i,
            T.getD i 0 = pcomp n w m (G.getD g 0) (T.getD par 0))) ∧
        ∀ i' < i, ptR m R i' ≠ ptR m R i := by
  intro L
  induction L with
  | nil =>
    intro j seen hL hj _ h
    have hT : T.length ≤ j := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq j (lenS R) = true := h
    rw [lenS_eq] at h'
    have hjR := Nat.eq_of_beq_eq_true h'
    refine ⟨by omega, fun i hi hi' => absurd hi' (by omega)⟩
  | cons t L ih =>
    intro j seen hL hj hseen h
    have hjT : j < T.length := by
      rcases Nat.lt_or_ge j T.length with h1 | h1
      · exact h1
      · have : T.drop j = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have htj : T.getD j 0 = t := by
      rw [List.getD_eq_getElem _ _ hjT]
      have := congrArg List.head? hL
      rw [List.head?_cons, List.head?_drop, List.getElem?_eq_getElem hjT] at this
      exact (Option.some.inj this).symm
    have hL' : L = T.drop (j + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    rw [treeW_cons] at h
    simp only [strictB_eqP, bAnd_iff] at h
    obtain ⟨hfresh, hcase, hrest⟩ := h
    have hpt : ptR m R j = Nat.land (getS R j) m := by rw [ptR, getS_eq]
    have hnew : seen.testBit (ptR m R j) = false := by
      rw [hpt]; exact testBit_false_of_land (Nat.eq_of_beq_eq_true hfresh)
    have hseen' : ∀ p, (Nat.lor seen (Nat.shiftLeft 1 (Nat.land (getS R j) m))).testBit p = true ↔
        ∃ i < j + 1, ptR m R i = p := by
      intro p
      rw [testBit_lor_one, Bool.or_eq_true, hseen p, decide_eq_true_iff, ← hpt]
      constructor
      · rintro (⟨i, hi, hip⟩ | hp)
        · exact ⟨i, by omega, hip⟩
        · exact ⟨j, by omega, hp⟩
      · rintro ⟨i, hi, hip⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact Or.inl ⟨i, hij, hip⟩
        · exact Or.inr (by rw [← hip, show i = j by omega])
    obtain ⟨hlen, hall⟩ := ih (j + 1) _ hL' hjT hseen' hrest
    refine ⟨hlen, fun i hi hiT => ?_⟩
    rcases Nat.lt_or_ge j i with hji | hji
    · exact hall i hji hiT
    have hij : i = j := by omega
    subst hij
    refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun i' hi' he => ?_⟩
    · subst h0
      rw [bIf_iff] at hcase
      rcases hcase with ⟨-, hc⟩ | ⟨hc, -⟩
      · rw [bAnd_iff] at hc
        refine ⟨by rw [hpt]; exact Nat.eq_of_beq_eq_true hc.1, ?_⟩
        rw [htj]; exact Nat.eq_of_beq_eq_true hc.2
      · exact absurd hc (by simp)
    · rw [bIf_iff] at hcase
      rcases hcase with ⟨hc, -⟩ | ⟨-, hc⟩
      · exact absurd (Nat.eq_of_beq_eq_true hc) (Nat.pos_iff_ne_zero.mp h0)
      · simp only [bAnd_iff, Nat.blt_eq] at hc
        obtain ⟨hpar, hg, hpg, heq⟩ := hc
        refine ⟨by rw [htj, hpt]; exact Nat.eq_of_beq_eq_true hpg, _, hg, _, hpar, ?_⟩
        rw [htj, Nat.eq_of_beq_eq_true heq]
        simp only [getS_eq]
    · have : seen.testBit (ptR m R i) = true := (hseen _).2 ⟨i', hi', he⟩
      rw [hnew] at this
      exact absurd this (by simp)

theorem treeK_sound {n w m idn : ℕ} {G : List ℕ} {b : ℕ} {R T : List ℕ}
    (h : treeK n w m idn G b R T = true) :
    T.length = R.length ∧ (∀ i < T.length, TreeAt n w m idn G b R T i) ∧
      ∀ i < T.length, ∀ i' < i, ptR m R i' ≠ ptR m R i := by
  obtain ⟨hlen, hall⟩ := treeW_sound (k := lenS G) T 0 0 rfl (Nat.zero_le _)
    (fun p => by simp) h
  refine ⟨hlen, fun i hi => ?_, fun i hi => (hall i (Nat.zero_le _) hi).2⟩
  obtain ⟨⟨h0, h1⟩, -⟩ := hall i (Nat.zero_le _) hi
  refine ⟨h0, fun hi0 => ?_⟩
  obtain ⟨hp, g, hg, par, hpar, he⟩ := h1 hi0
  exact ⟨hp, g, by rw [← lenS_eq]; exact hg, par, hpar, he⟩

@[expose] def SchAt (n w m : ℕ) (G : List ℕ) (b : ℕ) (R T Ref Nn S : List ℕ) (q : ℕ) : Prop :=
  Nat.land (Ref.getD q 0) m < R.length ∧ Nn.getD q 0 < R.length ∧
    Nat.shiftRight (Ref.getD q 0) w < G.length ∧ canonK n w m (n * w) (S.getD q 0) = true ∧
    pg w m (S.getD q 0) b = b ∧
    pcomp n w m (T.getD (Nn.getD q 0) 0) (S.getD q 0) =
      pcomp n w m (G.getD (Nat.shiftRight (Ref.getD q 0) w) 0)
        (T.getD (Nat.land (Ref.getD q 0) m) 0)

theorem schW_sound {n w m : ℕ} {G : List ℕ} {b : ℕ} {R T Ref Nn S : List ℕ} :
    ∀ (L : List ℕ) (q : ℕ), L = S.drop q → q ≤ S.length →
      schW n w m G (lenS G) b R T Ref Nn L q = true →
      Ref.length = S.length ∧ Nn.length = S.length ∧
        ∀ i, q ≤ i → i < S.length → SchAt n w m G b R T Ref Nn S i := by
  intro L
  induction L with
  | nil =>
    intro q hL hq h
    have hT : S.length ≤ q := List.drop_eq_nil_iff.mp hL.symm
    have h' : bAnd(Nat.beq q (lenS Ref), Nat.beq q (lenS Nn)) = true := h
    rw [bAnd_iff, lenS_eq, lenS_eq] at h'
    have h1 := Nat.eq_of_beq_eq_true h'.1
    have h2 := Nat.eq_of_beq_eq_true h'.2
    exact ⟨by omega, by omega, fun i hi hi' => absurd hi' (by omega)⟩
  | cons s L ih =>
    intro q hL hq h
    have hqS : q < S.length := by
      rcases Nat.lt_or_ge q S.length with h1 | h1
      · exact h1
      · have : S.drop q = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have hsq : S.getD q 0 = s := by
      rw [List.getD_eq_getElem _ _ hqS]
      have := congrArg List.head? hL
      rw [List.head?_cons, List.head?_drop, List.getElem?_eq_getElem hqS] at this
      exact (Option.some.inj this).symm
    have hL' : L = S.drop (q + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    rw [schW_cons] at h
    simp only [strictB_eqP, bAnd_iff] at h
    obtain ⟨hj, hj', hg, hc, hb, he, hrest⟩ := h
    simp only [Nat.blt_eq, lenS_eq, getS_eq] at hj hj' hg he
    have hc' : canonK n w m (n * w) s = true := hc
    obtain ⟨h2, h3, hall⟩ := ih (q + 1) hL' hqS hrest
    refine ⟨h2, h3, fun i hi hiS => ?_⟩
    rcases Nat.lt_or_ge q i with hqi | hqi
    · exact hall i hqi hiS
    have hiq : i = q := by omega
    subst hiq
    refine ⟨hj, hj', hg, by rw [hsq]; exact hc', by rw [hsq]; exact Nat.eq_of_beq_eq_true hb, ?_⟩
    rw [hsq]
    exact Nat.eq_of_beq_eq_true he

theorem schK_sound {n w m : ℕ} {G : List ℕ} {b : ℕ} {R T Ref Nn S : List ℕ}
    (h : schK n w m G b R T Ref Nn S = true) :
    Ref.length = S.length ∧ Nn.length = S.length ∧
      ∀ q < S.length, SchAt n w m G b R T Ref Nn S q := by
  obtain ⟨h1, h2, h3⟩ := schW_sound S 0 rfl (Nat.zero_le _) h
  exact ⟨h1, h2, fun q hq => h3 q (Nat.zero_le _) hq⟩

theorem commAllK_sound {n w m : ℕ} {t : ℕ} :
    ∀ {G : List ℕ}, commAllK n w m G t = true → ∀ g ∈ G, commK n w m (n * w) g t = true
  | [], _, g, hg => absurd hg List.not_mem_nil
  | x :: G, h, g, hg => by
    have h' : bAnd(commK n w m (Nat.mul n w) x t, commAllK n w m G t) = true := h
    rw [bAnd_iff] at h'
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h'.1
    · exact commAllK_sound h'.2 g hg

end CFSG.KC.HeChain

end
