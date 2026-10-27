module

public import Certificates.Data.Kernel.Parrott946.Clique
public import CFSG.Certificates.Kernel.OrbFindSound
import Mathlib.Data.Fin.Tuple.Sort
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.BfsPin

theorem allL_spec {f : Nat → Nat → Bool} : ∀ {L : List Nat} {k : Nat}, allL L f k = true →
    ∀ j < L.length, f (k + j) (L.getD j 0) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | x :: L, k, h, j, hj => by
    have h' : bAnd(f k x, allL L f (Nat.succ k)) = true := h
    rw [bAnd_eq, Bool.and_eq_true] at h'
    cases j with
    | zero => simpa using h'.1
    | succ j =>
      have := allL_spec h'.2 j (by simpa using hj)
      rw [List.getD_cons_succ, Nat.add_succ, ← Nat.succ_add]
      exact this

theorem anyL_spec {f : Nat → Nat → Bool} : ∀ {L : List Nat} {k : Nat}, anyL L f k = true →
    ∃ j < L.length, f (k + j) (L.getD j 0) = true
  | [], _, h => absurd h (by simp [anyL])
  | x :: L, k, h => by
    cases hf : f k x
    · have h' : anyL L f (Nat.succ k) = true := by
        have e : anyL (x :: L) f k =
            Bool.rec (motive := fun _ => Bool) (anyL L f (Nat.succ k)) true (f k x) := rfl
        rw [e, hf] at h
        exact h
      obtain ⟨j, hj, e⟩ := anyL_spec h'
      refine ⟨j + 1, by simpa using hj, ?_⟩
      rw [List.getD_cons_succ, ← Nat.succ_add_eq_add_succ]
      exact e
    · exact ⟨0, by simp, by simpa using hf⟩

theorem lenK_eq : ∀ L : List Nat, lenK L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenK L) = _
    rw [lenK_eq L, List.length_cons]

theorem appK_eq (R : List Nat) : ∀ L : List Nat, appK L R = L ++ R
  | [] => rfl
  | x :: L => by
    change x :: appK L R = _
    rw [appK_eq R L, List.cons_append]

theorem mapK_eq (f : Nat → Nat) : ∀ L : List Nat, mapK f L = L.map f
  | [] => rfl
  | x :: L => by
    change f x :: mapK f L = _
    rw [mapK_eq f L, List.map_cons]

theorem ltChainK_spec : ∀ {L : List Nat} {lo : Nat}, ltChainK L lo = true →
    L.Pairwise (· < ·) ∧ ∀ x ∈ L, lo < x
  | [], _, _ => ⟨List.Pairwise.nil, by simp⟩
  | x :: L, lo, h => by
    have h' : bAnd(Nat.blt lo x, ltChainK L x) = true := h
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨hp, hl⟩ := ltChainK_spec h'.2
    refine ⟨List.Pairwise.cons (fun y hy => hl y hy) hp, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h'.1
    · exact lt_trans h'.1 (hl y hy)

theorem inMaskK_spec {I : List Nat} {m e P : Nat} (h : inMaskK I m e P = true) :
    P = e ∨ ∃ j < I.length, bitB m j = true ∧ I.getD j 0 = P := by
  unfold inMaskK at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · obtain ⟨j, hj, e⟩ := anyL_spec h
    rw [Nat.zero_add, bAnd_eq, Bool.and_eq_true] at e
    exact Or.inr ⟨j, hj, e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem closedK_spec {n w : Nat} {I : List Nat} {m e : Nat} (h : closedK n w I m e = true)
    {a b : Nat} (ha : a < I.length) (hb : b < I.length) (hma : bitB m a = true)
    (hmb : bitB m b = true) :
    inMaskK I m e (pcomp n w (mask w) (I.getD a 0) (I.getD b 0)) = true := by
  unfold closedK at h
  have h1 := allL_spec h a ha
  rw [Nat.zero_add, Bool.or_eq_true, hma] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by decide)
  · have h2 := allL_spec h1 b hb
    rw [Nat.zero_add, Bool.or_eq_true, hmb] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 (by decide)
    · exact h2

theorem normMaskK_spec {n w : Nat} {I : List Nat} {m e c : Nat} {gs : List Nat}
    (h : normMaskK n w I m e c gs = true) {j : Nat} (hj : j < gs.length) :
    eq22 n w (mask w) c (gs.getD j 0) e c = true ∨
      ∃ k < I.length, bitB m k = true ∧ eq22 n w (mask w) c (gs.getD j 0) (I.getD k 0) c = true := by
  unfold normMaskK at h
  have h1 := allL_spec h j hj
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · obtain ⟨k, hk, e⟩ := anyL_spec h1
    rw [Nat.zero_add, bAnd_eq, Bool.and_eq_true] at e
    exact Or.inr ⟨k, hk, e.1, e.2⟩

theorem testBit_lor_cs (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem testBit_land_cs (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem testBit_shl_cs (a s i : Nat) :
    (Nat.shiftLeft a s).testBit i = (decide (i ≥ s) && a.testBit (i - s)) :=
  Nat.testBit_shiftLeft a

theorem testBit_shr_cs (a s i : Nat) : (Nat.shiftRight a s).testBit i = a.testBit (s + i) :=
  Nat.testBit_shiftRight a

theorem testBit_one_shl_cs (s i : Nat) : (Nat.shiftLeft 1 s).testBit i = decide (s = i) := by
  rw [PF.shl_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem brec_testBit (b : Bool) (X i : Nat) :
    (Bool.rec (motive := fun _ => Nat) 0 X b).testBit i = (b && X.testBit i) := by
  cases b
  · exact Nat.zero_testBit i
  · rfl

theorem bitB_eq_cs (m k : Nat) : bitB m k = m.testBit k := by
  have e0 : bitB m k = Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 k)) := rfl
  rw [e0]
  cases h : m.testBit k
  · have e : Nat.land m (Nat.shiftLeft 1 k) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_land_cs, testBit_one_shl_cs, Nat.zero_testBit]
      by_cases hi : k = i
      · subst hi
        simp [h]
      · simp [hi]
    rw [e]
    rfl
  · have e : Nat.land m (Nat.shiftLeft 1 k) = Nat.shiftLeft 1 k := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_land_cs, testBit_one_shl_cs]
      by_cases hi : k = i
      · subst hi
        simp [h]
      · simp [hi]
    rw [e, Nat.blt_eq, PF.shl_eq, Nat.one_mul]
    exact Nat.two_pow_pos k

theorem testBit_lane_cs (W L k b : Nat) :
    (lane W L k).testBit b = (decide (b < W) && L.testBit (W * k + b)) := by
  unfold lane
  change ((L >>> (W * k)) &&& (1 <<< W - 1)).testBit b = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

@[expose] noncomputable def selPosK (f : Nat → Bool) (J : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun y _ ih k => Nat.lor (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) k) (f y)) (ih (Nat.succ k))) J

theorem selPosK_testBit (f : Nat → Bool) : ∀ (J : List Nat) (k i : Nat),
    (selPosK f J k).testBit i = true ↔ k ≤ i ∧ i - k < J.length ∧ f (J.getD (i - k) 0) = true
  | [], k, i => by
    change (0 : Nat).testBit i = true ↔ _
    simp
  | y :: J, k, i => by
    have e : selPosK f (y :: J) k = Nat.lor (Bool.rec (motive := fun _ => Nat) 0
        (Nat.shiftLeft 1 k) (f y)) (selPosK f J (k + 1)) := rfl
    have h0 : (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 k) (f y)).testBit i =
        (f y && decide (k = i)) := by
      rw [brec_testBit, testBit_one_shl_cs]
    rw [e, testBit_lor_cs, Bool.or_eq_true, h0, selPosK_testBit f J (k + 1) i]
    rcases Nat.lt_trichotomy i k with hi | hi | hi
    · have h1 : k ≠ i := by omega
      simp only [h1, decide_false, Bool.and_false, Bool.false_eq_true, false_or]
      constructor
      · intro h
        omega
      · intro h
        omega
    · subst hi
      simp
    · obtain ⟨d, rfl⟩ : ∃ d, i = k + 1 + d := ⟨i - (k + 1), by omega⟩
      have h1 : k ≠ k + 1 + d := by omega
      have e1 : k + 1 + d - k = d + 1 := by omega
      have e2 : k + 1 + d - (k + 1) = d := by omega
      simp only [h1, decide_false, Bool.and_false, Bool.false_eq_true, false_or, e1, e2,
        List.getD_cons_succ, List.length_cons]
      constructor
      · rintro ⟨-, h2, h3⟩
        exact ⟨by omega, by omega, h3⟩
      · rintro ⟨-, h2, h3⟩
        exact ⟨by omega, by omega, h3⟩

theorem rowK_bit {n w x : Nat} {J : List Nat} {j : Nat} :
    bitB (rowK n w x J 0) j = true ↔ j < J.length ∧ eq22 n w (mask w) x (J.getD j 0) (J.getD j 0) x = true := by
  have e : rowK n w x J 0 = selPosK (fun y => eq22 n w (mask w) x y y x) J 0 := rfl
  rw [e, bitB_eq_cs, selPosK_testBit]
  simp

theorem rowK_lt {n w x : Nat} {J : List Nat} : rowK n w x J 0 < 2 ^ J.length := by
  have e : rowK n w x J 0 = selPosK (fun y => eq22 n w (mask w) x y y x) J 0 := rfl
  rw [e]
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases h : (selPosK (fun y => eq22 n w (mask w) x y y x) J 0).testBit i
  · rfl
  · have := ((selPosK_testBit _ J 0 i).1 h).2.1
    omega

theorem cmK_spec {n w : Nat} {I J C : List Nat} (h : cmK n w I J C = true) :
    C.length = I.length ∧ ∀ j < I.length, C.getD j 0 = rowK n w (I.getD j 0) J 0 := by
  induction I generalizing C with
  | nil =>
    cases C with
    | nil => exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
    | cons c cs => exact absurd (h : false = true) Bool.false_ne_true
  | cons x I ih =>
    cases C with
    | nil => exact absurd (h : false = true) Bool.false_ne_true
    | cons c cs =>
      have h' : bAnd(Nat.beq (rowK n w x J 0) c, cmK n w I J cs) = true := h
      rw [bAnd_eq, Bool.and_eq_true] at h'
      obtain ⟨h1, h2⟩ := ih h'.2
      refine ⟨by simp [h1], fun j hj => ?_⟩
      cases j with
      | zero => simpa using (Nat.eq_of_beq_eq_true h'.1).symm
      | succ j => simpa using h2 j (by simpa using hj)

theorem lane_packL {W : Nat} {C : List Nat} (hC : ∀ c ∈ C, c < 2 ^ W) {j : Nat}
    (hj : j < C.length) : lane W (packL W C) j = C.getD j 0 := by
  induction C generalizing j with
  | nil => exact absurd hj (by simp)
  | cons c C ih =>
    have hc : c < 2 ^ W := hC c (List.mem_cons.2 (Or.inl rfl))
    have hlow : ∀ i, W ≤ i → c.testBit i = false := fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hi))
    have ep : packL W (c :: C) = Nat.lor c (Nat.shiftLeft (packL W C) W) := rfl
    cases j with
    | zero =>
      apply Nat.eq_of_testBit_eq
      intro b
      rw [testBit_lane_cs, ep, testBit_lor_cs, testBit_shl_cs, List.getD_cons_zero, Nat.mul_zero,
        Nat.zero_add]
      by_cases hb : b < W
      · have : ¬ b ≥ W := by omega
        simp [hb, this]
      · simp [hb, hlow b (by omega)]
    | succ j =>
      have hj' : j < C.length := by simpa using hj
      rw [List.getD_cons_succ, ← ih (fun c hc => hC c (List.mem_cons_of_mem _ hc)) hj']
      apply Nat.eq_of_testBit_eq
      intro b
      rw [testBit_lane_cs, testBit_lane_cs, ep, testBit_lor_cs, testBit_shl_cs, Nat.mul_succ]
      have e1 : W * j + W + b - W = W * j + b := by omega
      have e2 : W * j + W + b ≥ W := by omega
      rw [hlow _ (by omega), e1]
      simp [e2]

theorem triK_bit {t d : Nat} : ∀ {Ms : List Nat}, (triK Ms t).testBit d = true →
    ∃ m ∈ Ms, Nat.land m t = t ∧ m.testBit d = true
  | [], h => by
    have h' : (0 : Nat).testBit d = true := h
    simp at h'
  | m :: Ms, h => by
    have e : triK (m :: Ms) t = Nat.lor (Bool.rec (motive := fun _ => Nat) 0 m
        (Nat.beq (Nat.land m t) t)) (triK Ms t) := rfl
    rw [e, testBit_lor_cs, Bool.or_eq_true] at h
    rcases h with h | h
    · cases hb : Nat.beq (Nat.land m t) t
      · rw [hb] at h
        have h' : (0 : Nat).testBit d = true := h
        simp at h'
      · rw [hb] at h
        exact ⟨m, List.mem_cons.2 (Or.inl rfl), Nat.eq_of_beq_eq_true hb, h⟩
    · obtain ⟨m', hm', e1, e2⟩ := triK_bit h
      exact ⟨m', List.mem_cons.2 (Or.inr hm'), e1, e2⟩

theorem cliqueK_spec {W C : Nat} {Ms : List Nat} (h : cliqueK W C Ms = true) {a b c d : Nat}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hcW : c < W)
    (h1 : bitB (lane W C a) b = true) (h2 : bitB (lane W C a) c = true)
    (h3 : bitB (lane W C b) c = true) (h4 : bitB (lane W C a) d = true)
    (h5 : bitB (lane W C b) d = true) (h6 : bitB (lane W C c) d = true) :
    ∃ m ∈ Ms, bitB m a = true ∧ bitB m b = true ∧ bitB m c = true ∧ bitB m d = true := by
  rw [bitB_eq_cs] at h1 h2 h3 h4 h5 h6
  have ha := allN_spec h a (by omega)
  simp only [strictB_eq'] at ha
  have hb := allN_spec ha b (by omega)
  have g1 : Nat.blt a b = true := Nat.blt_eq.mpr hab
  have g2 : bitB (lane W C a) b = true := by rw [bitB_eq_cs]; exact h1
  simp only [g1, g2, bAnd_eq, Bool.and_true, Bool.not_true, Bool.false_or, strictB_eq'] at hb
  have hc := allN_spec hb c hcW
  have g3 : Nat.blt b c = true := Nat.blt_eq.mpr hbc
  have g4 : bitB (Nat.land (lane W C a) (lane W C b)) c = true := by
    rw [bitB_eq_cs, testBit_land_cs, h2, h3]
    rfl
  simp only [g3, g4, bAnd_eq, Bool.and_true, Bool.not_true, Bool.false_or, strictB_eq'] at hc
  have hD := Nat.eq_of_beq_eq_true hc
  have hd : (aboveK (Nat.land (Nat.land (lane W C a) (lane W C b)) (lane W C c)) c).testBit d =
      true := by
    unfold aboveK
    rw [testBit_shl_cs, testBit_shr_cs, testBit_land_cs, testBit_land_cs]
    have e : Nat.succ c + (d - Nat.succ c) = d := by omega
    have e' : d ≥ Nat.succ c := by omega
    rw [e, h4, h5, h6]
    simp [e']
  rw [← hD, testBit_land_cs, Bool.and_eq_true] at hd
  obtain ⟨m, hm, hmt, hmd⟩ := triK_bit hd.2
  have hbit : ∀ x, (bits3 a b c).testBit x = true → bitB m x = true := by
    intro x hx
    rw [← hmt, testBit_land_cs, Bool.and_eq_true] at hx
    rw [bitB_eq_cs]
    exact hx.1
  have t3 : ∀ x, (x = a ∨ x = b ∨ x = c) → (bits3 a b c).testBit x = true := by
    intro x hx
    unfold bits3
    rw [testBit_lor_cs, testBit_lor_cs, testBit_one_shl_cs, testBit_one_shl_cs, testBit_one_shl_cs]
    rcases hx with rfl | rfl | rfl <;> simp
  refine ⟨m, hm, hbit a (t3 a (Or.inl rfl)), hbit b (t3 b (Or.inr (Or.inl rfl))),
    hbit c (t3 c (Or.inr (Or.inr rfl))), ?_⟩
  rw [bitB_eq_cs]
  exact hmd

theorem cliqueK_spec' {W C : Nat} {Ms : List Nat} (h : cliqueK W C Ms = true)
    {p : Fin 4 → Nat} (hp : Function.Injective p) (hW : ∀ i, p i < W)
    (hadj : ∀ i j, i ≠ j → bitB (lane W C (p i)) (p j) = true) :
    ∃ m ∈ Ms, ∀ i, bitB m (p i) = true := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 4), Monotone (p ∘ σ) := ⟨_, Tuple.monotone_sort p⟩
  have hm : StrictMono (p ∘ σ) := hσ.strictMono_of_injective (hp.comp σ.injective)
  have adj : ∀ i j : Fin 4, i < j → bitB (lane W C (p (σ i))) (p (σ j)) = true :=
    fun i j hij => hadj _ _ fun e => (ne_of_lt hij) (σ.injective e)
  have h01 : p (σ 0) < p (σ 1) := hm (by decide)
  have h12 : p (σ 1) < p (σ 2) := hm (by decide)
  have h23 : p (σ 2) < p (σ 3) := hm (by decide)
  obtain ⟨m, hmM, b0, b1, b2, b3⟩ := cliqueK_spec h h01 h12 h23 (hW _) (adj 0 1 (by decide))
    (adj 0 2 (by decide)) (adj 1 2 (by decide)) (adj 0 3 (by decide)) (adj 1 3 (by decide))
    (adj 2 3 (by decide))
  refine ⟨m, hmM, fun i => ?_⟩
  obtain ⟨k, rfl⟩ := σ.surjective i
  fin_cases k
  · exact b0
  · exact b1
  · exact b2
  · exact b3

@[expose] noncomputable def unionLK (f : Nat → Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun P _ ih => Nat.lor (f P) ih) L

theorem unionLK_testBit (f : Nat → Nat) (i : Nat) : ∀ L : List Nat,
    (unionLK f L).testBit i = true ↔ ∃ P ∈ L, (f P).testBit i = true
  | [] => by
    change (0 : Nat).testBit i = true ↔ _
    simp
  | P :: L => by
    have e : unionLK f (P :: L) = Nat.lor (f P) (unionLK f L) := rfl
    rw [e, testBit_lor_cs, Bool.or_eq_true, unionLK_testBit f i L]
    constructor
    · rintro (h | ⟨Q, hQ, h⟩)
      · exact ⟨P, List.mem_cons.2 (Or.inl rfl), h⟩
      · exact ⟨Q, List.mem_cons.2 (Or.inr hQ), h⟩
    · rintro ⟨Q, hQ, h⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact Or.inl h
      · exact Or.inr ⟨Q, hQ, h⟩

theorem ne_zero_bit_cs {x : Nat} (h : x ≠ 0) : ∃ i, x.testBit i = true := by
  by_contra hc
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  cases hx : x.testBit i
  · rfl
  · exact absurd ⟨i, hx⟩ hc

theorem hitH_bit {W : Nat} {I : List Nat} {e P i : Nat} :
    (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
      (Nat.beq P e))).testBit i = true ↔ (i < I.length ∧ I.getD i 0 = P) ∨ (P = e ∧ i = W) := by
  have e1 : hitK I P 0 = selPosK (fun y => Nat.beq y P) I 0 := rfl
  rw [testBit_lor_cs, Bool.or_eq_true, e1, selPosK_testBit, brec_testBit]
  simp only [Nat.zero_le, Nat.sub_zero, true_and, Nat.beq_eq]
  cases hb : Nat.beq P e
  · have : P ≠ e := fun h => by rw [h, Nat.beq_refl] at hb; exact absurd hb (by decide)
    simp [this]
  · rw [testBit_one_shl_cs]
    have hPe := Nat.eq_of_beq_eq_true hb
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨hPe, ?_⟩
        simp at h
        omega
    · rintro (h | ⟨-, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (by simp)

theorem hitE_cases (W : Nat) (I : List Nat) (e P : Nat) :
    (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
        (Nat.beq P e)) = 0 ∧ hitE W I e P = Nat.shiftLeft 1 (W + 1)) ∨
      (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
        (Nat.beq P e)) ≠ 0 ∧ hitE W I e P = Nat.lor (hitK I P 0)
          (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W) (Nat.beq P e))) := by
  have e0 : hitE W I e P = Bool.rec (motive := fun _ => Nat)
      (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
        (Nat.beq P e))) (Nat.shiftLeft 1 (W + 1))
      (Nat.beq (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
        (Nat.beq P e))) 0) := PF.strictN_eqP _ _
  rw [e0]
  cases hb : Nat.beq (Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0
      (Nat.shiftLeft 1 W) (Nat.beq P e))) 0
  · refine Or.inr ⟨fun h => ?_, rfl⟩
    rw [h] at hb
    exact absurd hb (by decide)
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true hb, rfl⟩

theorem coverK_spec {W : Nat} {I : List Nat} {e m : Nat} {L : List Nat}
    (h : coverK W I e L = Nat.lor m (Nat.shiftLeft 1 W)) (hm : m < 2 ^ W) (hI : I.length = W) :
    (∀ P ∈ L, P = e ∨ ∃ j < W, bitB m j = true ∧ I.getD j 0 = P) ∧
      ∀ j < W, bitB m j = true → ∃ P ∈ L, P = I.getD j 0 := by
  have hU : coverK W I e L = unionLK (hitE W I e) L := rfl
  have hR : ∀ i, (Nat.lor m (Nat.shiftLeft 1 W)).testBit i = (m.testBit i || decide (W = i)) :=
    fun i => by rw [testBit_lor_cs, testBit_one_shl_cs]
  have hmW : ∀ i, W ≤ i → m.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hi))
  have hcov : ∀ i, (∃ P ∈ L, (hitE W I e P).testBit i = true) ↔
      (m.testBit i || decide (W = i)) = true := fun i => by
    rw [← hR, ← h, hU, unionLK_testBit]
  have hE : ∀ P ∈ L, hitE W I e P = Nat.lor (hitK I P 0)
      (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W) (Nat.beq P e)) ∧
      Nat.lor (hitK I P 0) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 W)
        (Nat.beq P e)) ≠ 0 := by
    intro P hP
    rcases hitE_cases W I e P with ⟨-, h1⟩ | ⟨h0, h1⟩
    · exfalso
      have := (hcov (W + 1)).1 ⟨P, hP, by rw [h1, testBit_one_shl_cs]; simp⟩
      rw [hmW _ (by omega)] at this
      simp at this
    · exact ⟨h1, h0⟩
  refine ⟨fun P hP => ?_, fun j hj hmj => ?_⟩
  · obtain ⟨h1, h0⟩ := hE P hP
    obtain ⟨i, hi⟩ := ne_zero_bit_cs h0
    have hc := (hcov i).1 ⟨P, hP, by rw [h1]; exact hi⟩
    rcases hitH_bit.1 hi with ⟨hiI, hiP⟩ | ⟨hPe, -⟩
    · right
      have hWi : W ≠ i := by omega
      simp only [hWi, decide_false, Bool.or_false] at hc
      exact ⟨i, by omega, by rw [bitB_eq_cs]; exact hc, hiP⟩
    · exact Or.inl hPe
  · rw [bitB_eq_cs] at hmj
    obtain ⟨P, hP, hb⟩ := (hcov j).2 (by rw [hmj]; rfl)
    obtain ⟨h1, -⟩ := hE P hP
    rw [h1] at hb
    rcases hitH_bit.1 hb with ⟨-, hjP⟩ | ⟨-, hjW⟩
    · exact ⟨P, hP, hjP.symm⟩
    · omega

theorem idxCoverK_spec {n w : Nat} {ps : List Nat} {N : Nat} {T S : Nat → Nat} {L : List Nat}
    (h : idxCoverK n w ps N T S L = Nat.sub (Nat.shiftLeft 1 N) 1) {j : Nat} (hj : j < N) :
    ∃ P ∈ L, T j = P := by
  have hU : idxCoverK n w ps N T S L = unionLK (idxBit n w ps N T S) L := rfl
  have hm : Nat.sub (Nat.shiftLeft 1 N) 1 = 2 ^ N - 1 := by
    rw [PF.shl_eq, Nat.one_mul]
    rfl
  have hj' : (idxCoverK n w ps N T S L).testBit j = true := by
    rw [h, hm, Nat.testBit_two_pow_sub_one]
    simpa using hj
  rw [hU, unionLK_testBit] at hj'
  obtain ⟨P, hP, hb⟩ := hj'
  refine ⟨P, hP, ?_⟩
  unfold idxBit at hb
  rw [PF.strictN_eqP] at hb
  cases hc : bAnd(Nat.blt (findK n w ps T S (pkeyK n w ps P) 24 0 N) N,
      Nat.beq (T (findK n w ps T S (pkeyK n w ps P) 24 0 N)) P)
  · rw [hc] at hb
    have hb' : (Nat.shiftLeft 1 N).testBit j = true := hb
    rw [testBit_one_shl_cs] at hb'
    have := of_decide_eq_true hb'
    omega
  · rw [hc] at hb
    have hb' : (Nat.shiftLeft 1 (findK n w ps T S (pkeyK n w ps P) 24 0 N)).testBit j = true := hb
    rw [testBit_one_shl_cs] at hb'
    have e := of_decide_eq_true hb'
    rw [bAnd_eq, Bool.and_eq_true] at hc
    rw [← e]
    exact Nat.eq_of_beq_eq_true hc.2

theorem getD_lt {L : List Nat} {i : Nat} (hi : i < L.length) : L.getD i 0 = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem distinctK_spec {L : List Nat} (h : distinctK L = true) : L.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j e
  have h1 := allL_spec (allL_spec h i i.2) j j.2
  rw [Nat.zero_add, Nat.zero_add, getD_lt i.2, getD_lt j.2, Bool.or_eq_true] at h1
  have e' : L[i.1] = L[j.1] := e
  rcases h1 with h1 | h1
  · exact Fin.ext (Nat.eq_of_beq_eq_true h1)
  · rw [e', Nat.beq_refl] at h1
    exact absurd h1 (by decide)

theorem mulClosedK_spec {n w : Nat} {L : List Nat} (h : mulClosedK n w L = true) {x y : Nat}
    (hx : x ∈ L) (hy : y ∈ L) : pcomp n w (mask w) x y ∈ L := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  have h1 := allL_spec (allL_spec h i hi) j hj
  rw [getD_lt hi, getD_lt hj, strictB_eq'] at h1
  obtain ⟨k, hk, e⟩ := anyL_spec h1
  rw [← Nat.eq_of_beq_eq_true e, getD_lt hk]
  exact List.getElem_mem hk

theorem shr_zero_of_lt_cs {x k : Nat} (h : x < 2 ^ k) : x >>> k = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt h

theorem lt_of_shr_zero_cs {x k : Nat} (h : x >>> k = 0) : x < 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow] at h
  by_contra hc
  have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos k)
  omega

theorem prep_canon_eq {n w P Q : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (hQ : PRep n w Q g) (hPl : P < 2 ^ (n * w)) (hQl : Q < 2 ^ (n * w)) : P = Q := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [Nat.mul_zero, Nat.pow_zero] at hPl hQl
    omega
  · exact PF.eq_of_fields hw (shr_zero_of_lt_cs hPl) (shr_zero_of_lt_cs hQl) fun i hi =>
      (hP ⟨i, hi⟩).trans (hQ ⟨i, hi⟩).symm

theorem shl_zero_cs (s : Nat) : Nat.shiftLeft 0 s = 0 := Nat.zero_shiftLeft s

theorem pmkH_zero_cs (p q : Nat) : ∀ d lo, pmkH 0 0 p q d lo = 0
  | 0, lo => Nat.and_zero _
  | d + 1, lo => by
    have e : pmkH 0 0 p q (d + 1) lo = Nat.lor (pmkH 0 0 p q d lo)
        (Nat.shiftLeft (pmkH 0 0 p q d (Nat.add lo (Nat.shiftLeft 1 d)))
          (Nat.mul 0 (Nat.shiftLeft 1 d))) := rfl
    rw [e, pmkH_zero_cs p q d, pmkH_zero_cs p q d, shl_zero_cs]
    rfl

theorem pmkH8_zero_cs (p q : Nat) : ∀ d lo, pmkH8 0 0 p q d lo = 0
  | 0, lo => by
    have hz : ∀ x, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have hs : ∀ s, Nat.shiftLeft 0 s = 0 := shl_zero_cs
    have ho : Nat.lor 0 0 = 0 := rfl
    change Nat.lor (Nat.lor (Nat.lor (Nat.land _ 0) (Nat.shiftLeft (Nat.land _ 0) 0))
      (Nat.shiftLeft (Nat.lor (Nat.land _ 0) (Nat.shiftLeft (Nat.land _ 0) 0)) _))
      (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.land _ 0) (Nat.shiftLeft (Nat.land _ 0) 0))
        (Nat.shiftLeft (Nat.lor (Nat.land _ 0) (Nat.shiftLeft (Nat.land _ 0) 0)) _)) _) = 0
    simp only [hz, hs, ho]
  | d + 1, lo => by
    have e : pmkH8 0 0 p q (d + 1) lo = Nat.lor (pmkH8 0 0 p q d lo)
        (Nat.shiftLeft (pmkH8 0 0 p q d (Nat.add lo (Nat.shiftLeft 8 d)))
          (Nat.mul 0 (Nat.shiftLeft 8 d))) := rfl
    rw [e, pmkH8_zero_cs p q d, pmkH8_zero_cs p q d, shl_zero_cs]
    rfl

theorem pcR_zero_cs (n p q : Nat) : ∀ k b rem, PF.pcR n 0 0 p q k b rem = 0
  | 0, _, _ => rfl
  | k + 1, b, rem => by
    rw [PF.pcR_succ]
    cases Nat.beq rem (nat_lit 0)
    · cases Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0)
      · rw [PF.strictN_eqP, pcR_zero_cs n p q k]
        cases Nat.blt b (nat_lit 3)
        · change Nat.lor (Nat.shiftLeft (pmkH8 0 0 p q _ _) _) 0 = 0
          rw [pmkH8_zero_cs, shl_zero_cs]
          rfl
        · change Nat.lor (Nat.shiftLeft (pmkH 0 0 p q _ _) _) 0 = 0
          rw [pmkH_zero_cs, shl_zero_cs]
          rfl
      · exact pcR_zero_cs n p q k _ _
    · rfl

theorem pcomp_lt {n w P Q : Nat} (hn : n < 2 ^ 32) : pcomp n w (mask w) P Q < 2 ^ (n * w) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have hm : mask 0 = 0 := by rw [PF.mask_eq]
    rw [hm, PF.pcomp_eq_pcR, pcR_zero_cs]
    exact Nat.two_pow_pos _
  · exact lt_of_shr_zero_cs (PF.pcomp_shr P Q hn hw)

theorem pidn_lt {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : pidn n w < 2 ^ (n * w) :=
  lt_of_shr_zero_cs (PF.pidn_shr hn hw)

theorem lane_lt (W L k : Nat) : lane W L k < 2 ^ W := by
  unfold lane
  change (L >>> (W * k)) &&& (1 <<< W - 1) < 2 ^ W
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

theorem findK_eq_cs {n w : Nat} {ps : List Nat} {T S : Nat → Nat} {N p : Nat}
    (hmono : ∀ k l, k < l → l < N → pkeyK n w ps (T (S k)) < pkeyK n w ps (T (S l))) :
    ∀ f lo hi, lo ≤ p → p ≤ hi → hi ≤ N → p < N → hi - lo < 2 ^ f →
      findK n w ps T S (pkeyK n w ps (T (S p))) f lo hi = S p
  | 0, lo, hi, h1, h2, _, _, h5 => by
    have e : lo = p := by
      rw [Nat.pow_zero] at h5
      omega
    rw [← e]
    rfl
  | f + 1, lo, hi, h1, h2, h3, h4, h5 => by
    have e : findK n w ps T S (pkeyK n w ps (T (S p))) (f + 1) lo hi =
        nIf(Nat.blt lo hi, strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
          nIf(Nat.blt (pkeyK n w ps (T (S mid))) (pkeyK n w ps (T (S p))),
            findK n w ps T S (pkeyK n w ps (T (S p))) f (Nat.succ mid) hi,
            findK n w ps T S (pkeyK n w ps (T (S p))) f lo mid)), S lo) := rfl
    have hmid : Nat.shiftRight (Nat.add lo hi) (nat_lit 1) = (lo + hi) / 2 := by
      rw [PF.shr_eq]
      rfl
    have hp2 : 2 ^ (f + 1) = 2 ^ f * 2 := by rw [Nat.pow_succ]
    rw [hp2] at h5
    rw [e, PF.strictN_eqP]
    beta_reduce
    rw [hmid]
    cases hlt : Nat.blt lo hi
    · have hl : ¬ lo < hi := fun h => by
        rw [← Nat.blt_eq, hlt] at h
        exact Bool.false_ne_true h
      have e2 : lo = p := by omega
      exact congrArg S e2
    · have hl : lo < hi := Nat.blt_eq.mp hlt
      cases hk : Nat.blt (pkeyK n w ps (T (S ((lo + hi) / 2)))) (pkeyK n w ps (T (S p)))
      · have hk' : ¬ pkeyK n w ps (T (S ((lo + hi) / 2))) < pkeyK n w ps (T (S p)) := fun h => by
          rw [← Nat.blt_eq, hk] at h
          exact Bool.false_ne_true h
        have hpm : p ≤ (lo + hi) / 2 := by
          by_contra hc
          exact hk' (hmono _ _ (by omega) h4)
        exact findK_eq_cs hmono f lo ((lo + hi) / 2) h1 hpm (by omega) h4 (by omega)
      · have hk' := Nat.blt_eq.mp hk
        have hpm : (lo + hi) / 2 < p := by
          by_contra hc
          rcases Nat.lt_or_ge p ((lo + hi) / 2) with h6 | h6
          · exact absurd (hmono _ _ h6 (by omega)) (Nat.lt_asymm hk')
          · have e3 : (lo + hi) / 2 = p := by omega
            rw [e3] at hk'
            exact Nat.lt_irrefl _ hk'
        exact findK_eq_cs hmono f (Nat.succ ((lo + hi) / 2)) hi (by omega) h2 h3 h4 (by omega)

theorem memK_complete {n w : Nat} {ps : List Nat} {N : Nat} {T S : Nat → Nat}
    (hK : CFSG.KC.BfsPin.distinctK N (fun i => pkeyK n w ps (T i)) S = true) (hN : N ≤ 2 ^ 23)
    {j : Nat}
    (hj : j < N) : memK n w ps N T S (T j) = true := by
  unfold CFSG.KC.BfsPin.distinctK at hK
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at hK
  obtain ⟨hlt, hS, -⟩ := hK
  have hstep : ∀ k, k + 1 < N → pkeyK n w ps (T (S k)) < pkeyK n w ps (T (S (k + 1))) :=
    fun k hk => Nat.blt_eq.mp (allN_spec hlt k (by change k < N - 1; omega))
  have hmono : ∀ k l, k < l → l < N → pkeyK n w ps (T (S k)) < pkeyK n w ps (T (S l)) := by
    intro k l
    induction l with
    | zero => intro h1; omega
    | succ l ih =>
      intro hkl hl
      rcases Nat.lt_or_ge k l with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) (hstep l hl)
      · have e : k = l := by omega
        rw [e]
        exact hstep l hl
  have hS' : ∀ k < N, S k < N := fun k hk => Nat.blt_eq.mp (allN_spec hS k hk)
  let F : Fin N → Fin N := fun k => ⟨S k, hS' k k.2⟩
  have hF : Function.Injective F := fun a b e => by
    have e' : S a = S b := congrArg Fin.val e
    rcases Nat.lt_trichotomy a.1 b.1 with h1 | h1 | h1
    · exact absurd (congrArg (fun x => pkeyK n w ps (T x)) e') (Nat.ne_of_lt (hmono _ _ h1 b.2))
    · exact Fin.ext h1
    · exact absurd (congrArg (fun x => pkeyK n w ps (T x)) e').symm
        (Nat.ne_of_lt (hmono _ _ h1 a.2))
  obtain ⟨⟨p, hpN⟩, hp⟩ := (Finite.injective_iff_surjective.1 hF) ⟨j, hj⟩
  have hpj : S p = j := congrArg Fin.val hp
  have hf : findK n w ps T S (pkeyK n w ps (T j)) (nat_lit 24) (nat_lit 0) N = j := by
    have := findK_eq_cs hmono 24 0 N (Nat.zero_le p) (by omega) le_rfl hpN
      (by have : (2 : Nat) ^ 24 = 16777216 := rfl; omega)
    rw [← hpj]
    exact this
  unfold memK
  rw [strictB_eq', hf]
  beta_reduce
  rw [bAnd_eq, Bool.and_eq_true]
  exact ⟨Nat.blt_eq.mpr hj, Nat.beq_refl _⟩

end CFSG.KC.Parrott946

end
