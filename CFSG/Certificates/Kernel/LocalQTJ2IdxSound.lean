module

public import Certificates.Data.Kernel.LocalQT.J2Idx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Index
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.KC.LQT.JX

open CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Monster.B.Co2.Native

@[expose] def mtG (N ng : ℕ) (tab par lab : List ℕ) : Array ℕ :=
  (List.range N).foldl (fun acc i => (List.range N).foldl (fun acc2 j =>
    acc2.push (if j = 0 then i else
      tab.getD (acc2.getD (i * N + par.getD j 0) 0 * ng + lab.getD j 0) 0)) acc) #[]

@[expose] def mulG (N ng : ℕ) (tab par lab : List ℕ) (i j : ℕ) : ℕ :=
  (mtG N ng tab par lab).getD (i * N + j) 0

@[expose] def mulOKG (N ng : ℕ) (tab par lab : List ℕ) : Bool :=
  allLt N fun i => allLt N fun j => decide (mulG N ng tab par lab i j < N) &&
    (if j = 0 then mulG N ng tab par lab i 0 == i else
      mulG N ng tab par lab i j ==
        tab.getD (mulG N ng tab par lab i (par.getD j 0) * ng + lab.getD j 0) 0)

@[expose] def invTG (N : ℕ) (mulF : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range N).map fun s => (List.range N).findIdx fun j => mulF s j == 0).toArray

@[expose] def invG (N : ℕ) (mulF : ℕ → ℕ → ℕ) (s : ℕ) : ℕ := (invTG N mulF).getD s 0

@[expose] def invOKG (N : ℕ) (mulF : ℕ → ℕ → ℕ) : Bool :=
  allLt N fun s => decide (invG N mulF s < N) && mulF s (invG N mulF s) == 0

@[expose] def repsOKG (N : ℕ) (mulF : ℕ → ℕ → ℕ) (reps : List (ℕ × ℕ)) : Bool :=
  reps.all fun ab => decide (ab.1 < N) && decide (ab.2 < N) && isInvF mulF ab.1 &&
    isInvF mulF ab.2

@[expose] def goodG (N : ℕ) (mulF : ℕ → ℕ → ℕ) (invF : ℕ → ℕ) (reps : List (ℕ × ℕ)) (i j : ℕ) :
    Bool :=
  (goodTblF N mulF invF reps).getD (i * N + j) false

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.SV

private theorem jx_bAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem jx_bIf (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = cond c t e := by
  cases c <;> rfl

private theorem jx_c1 (c t : Bool) : cond c t false = (c && t) := by cases c <;> rfl

private theorem jx_c2 (c e : Bool) : cond c true e = (c || e) := by cases c <;> rfl

private theorem jx_c3 (c : Bool) : cond c false true = !c := by cases c <;> rfl

private theorem jx_c4 (c t : Bool) : cond c t true = (!c || t) := by cases c <;> rfl

private theorem jx_strictB (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem jx_allLt {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    have : allLt (n + 1) p = (allLt n p && p n) := by
      simp only [allLt, Nat.all_succ]
    rw [this, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · rw [h]; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem jx_allBlk {b : ℕ} {f : ℕ → Bool} {len : ℕ} :
    CFSG.KC.Enum.allBlk b f len = true ↔ ∀ l < len, f (b + l) = true := by
  constructor
  · intro h l hl
    exact CFSG.KS.allBlk_spec h l hl
  · intro h
    induction len with
    | zero => rfl
    | succ n ih =>
      have : CFSG.KC.Enum.allBlk b f (n + 1) = (f (b + n) && CFSG.KC.Enum.allBlk b f n) := by
        change Bool.rec (motive := fun _ => Bool) false (CFSG.KC.Enum.allBlk b f n) (f (b + n)) = _
        rw [jx_bAnd]
      rw [this, Bool.and_eq_true]
      exact ⟨h n (by omega), ih fun l hl => h l (by omega)⟩

private theorem row_spec {b gb N ng : ℕ} {PT LT TB MR IT GW : ℕ → ℕ} {reps : List (ℕ × ℕ)} {i : ℕ}
    (h : rowJX b gb N ng PT LT TB MR IT GW reps i = true) :
    mtJ b MR i 0 = i ∧
    (∀ j < N, mtJ b MR i j < N ∧ (j ≠ 0 → PT j < j ∧ LT j < ng ∧
      mtJ b MR i j = TB (mtJ b MR i (PT j) * ng + LT j))) ∧
    (IT i < N ∧ mtJ b MR i (IT i) = 0 ∧ ∀ j < IT i, mtJ b MR i j ≠ 0) ∧
    (∀ j < N, witJ b N MR IT reps i j (pg gb (mask gb) (GW i) j) = true) := by
  unfold rowJX at h
  simp only [jx_bIf, jx_strictB, jx_c1, jx_c2, jx_c3, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.blt_eq, jx_allBlk, Nat.zero_add, Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨h1, h2, ⟨h3, h4, h5⟩, h6⟩ := h
  refine ⟨h1, fun j hj => ?_, ⟨h3, h4, fun j hj hz => ?_⟩, h6⟩
  · obtain ⟨a, b⟩ := h2 j hj
    exact ⟨a, fun hj0 => b.resolve_left hj0⟩
  · have := h5 j hj
    rw [hz] at this
    simp at this

private def jxStep (N ng : ℕ) (tab par lab : List ℕ) (i : ℕ) (acc2 : Array ℕ) (j : ℕ) :
    Array ℕ :=
  acc2.push (if j = 0 then i else
    tab.getD (acc2.getD (i * N + par.getD j 0) 0 * ng + lab.getD j 0) 0)

private theorem jx_getD_push (a : Array ℕ) (x k : ℕ) :
    (a.push x).getD k 0 = if k = a.size then x else a.getD k 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : k = a.size <;> simp [h]

private theorem jx_inner {N ng : ℕ} {tab par lab : List ℕ} (i : ℕ)
    (hpar : ∀ j, 0 < j → j < N → par.getD j 0 < j) :
    ∀ m ≤ N, ∀ acc : Array ℕ, acc.size = i * N →
      ∀ r, (List.range m).foldl (jxStep N ng tab par lab i) acc = r →
        r.size = i * N + m ∧ (∀ k < i * N, r.getD k 0 = acc.getD k 0) ∧
        ∀ j < m, r.getD (i * N + j) 0 = if j = 0 then i else
          tab.getD (r.getD (i * N + par.getD j 0) 0 * ng + lab.getD j 0) 0 := by
  intro m
  induction m with
  | zero =>
    intro _ acc hacc r hr
    simp only [List.range_zero, List.foldl_nil] at hr
    subst hr
    exact ⟨by simpa using hacc, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    intro hm acc hacc r hr
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hr
    obtain ⟨hs, hp, hv⟩ := ih (by omega) acc hacc _ rfl
    set r0 := (List.range m).foldl (jxStep N ng tab par lab i) acc with hr0
    subst hr
    have hsz : (jxStep N ng tab par lab i r0 m).size = i * N + (m + 1) := by
      simp [jxStep, hs]; omega
    have hpush : ∀ k, (jxStep N ng tab par lab i r0 m).getD k 0 =
        if k = i * N + m then (if m = 0 then i else
          tab.getD (r0.getD (i * N + par.getD m 0) 0 * ng + lab.getD m 0) 0)
        else r0.getD k 0 := by
      intro k
      rw [jxStep, jx_getD_push, hs]
    refine ⟨hsz, fun k hk => ?_, fun j hj => ?_⟩
    · rw [hpush, if_neg (by omega), hp k hk]
    · by_cases hjm : j = m
      · subst hjm
        by_cases hj0 : j = 0
        · subst hj0
          simp only [hpush, if_true, if_pos]
        · have := hpar j (by omega) (by omega)
          simp only [hpush, if_pos, if_neg hj0, if_neg (show i * N + par.getD j 0 ≠ i * N + j by omega)]
      · have hjm' : j < m := by omega
        simp only [hpush, if_neg (show i * N + j ≠ i * N + m by omega)]
        rw [hv j hjm']
        by_cases hj0 : j = 0
        · simp [hj0]
        · have := hpar j (by omega) (by omega)
          simp only [if_neg hj0, if_neg (show i * N + par.getD j 0 ≠ i * N + m by omega)]

private theorem jx_outer {N ng : ℕ} {tab par lab : List ℕ}
    (hpar : ∀ j, 0 < j → j < N → par.getD j 0 < j) :
    ∀ n ≤ N, ∀ A : Array ℕ, (List.range n).foldl (fun acc i =>
        (List.range N).foldl (jxStep N ng tab par lab i) acc) #[] = A →
      A.size = n * N ∧ ∀ i < n, ∀ j < N, A.getD (i * N + j) 0 = if j = 0 then i else
        tab.getD (A.getD (i * N + par.getD j 0) 0 * ng + lab.getD j 0) 0 := by
  intro n
  induction n with
  | zero =>
    intro _ A hA
    simp only [List.range_zero, List.foldl_nil] at hA
    subst hA
    exact ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro hn A hA
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hA
    obtain ⟨hs, hv⟩ := ih (by omega) _ rfl
    set A0 := (List.range n).foldl (fun acc i =>
        (List.range N).foldl (jxStep N ng tab par lab i) acc) #[] with hA0
    subst hA
    obtain ⟨h1, h2, h3⟩ := jx_inner (ng := ng) (tab := tab) (lab := lab) n hpar N le_rfl A0 hs _ rfl
    refine ⟨by rw [h1]; ring, fun i hi j hj => ?_⟩
    by_cases hin : i = n
    · subst hin
      exact h3 j hj
    · have hi' : i < n := by omega
      have hlt : i * N + j < n * N := by
        calc i * N + j < i * N + N := by omega
          _ = (i + 1) * N := by ring
          _ ≤ n * N := Nat.mul_le_mul_right N hi'
      rw [h2 _ hlt, hv i hi' j hj]
      by_cases hj0 : j = 0
      · simp [hj0]
      · have := hpar j (by omega) hj
        have hlt2 : i * N + par.getD j 0 < n * N := by omega
        simp only [if_neg hj0, h2 _ hlt2]

private theorem jx_mul {N ng : ℕ} {tab par lab : List ℕ} {M : ℕ → ℕ → ℕ}
    (hpar : ∀ j, 0 < j → j < N → par.getD j 0 < j)
    (hM0 : ∀ i < N, M i 0 = i)
    (hMrec : ∀ i < N, ∀ j < N, j ≠ 0 →
      M i j = tab.getD (M i (par.getD j 0) * ng + lab.getD j 0) 0) {i : ℕ} (hi : i < N) :
    ∀ j < N, mulG N ng tab par lab i j = M i j := by
  obtain ⟨_, hv⟩ := jx_outer (ng := ng) (tab := tab) (lab := lab) hpar N le_rfl _ rfl
  have hmt : (List.range N).foldl (fun acc i =>
      (List.range N).foldl (jxStep N ng tab par lab i) acc) #[] = mtG N ng tab par lab := rfl
  rw [hmt] at hv
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h1 := hv i hi j hj
    have h2 : mulG N ng tab par lab i j = (mtG N ng tab par lab).getD (i * N + j) 0 := rfl
    by_cases hj0 : j = 0
    · subst hj0
      rw [h2, h1, if_pos rfl, hM0 i hi]
    · have hp := hpar j (by omega) hj
      have h3 : mulG N ng tab par lab i (par.getD j 0) =
          (mtG N ng tab par lab).getD (i * N + par.getD j 0) 0 := rfl
      rw [h2, h1, if_neg hj0, ← h3, ih _ hp (by omega), hMrec i hi j hj hj0]

private theorem jx_chunks {N K L : ℕ} (hKL : N ≤ K * L) {f : ℕ → Bool}
    (h : ∀ s < K, allBlk (Nat.mul s L) (fun i => bIf(Nat.blt i N, f i, true)) L = true) :
    ∀ i < N, f i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at hKL; omega
    · exact h0
  have hs : i / L < K := by
    apply (Nat.div_lt_iff_lt_mul hL).2
    calc i < N := hi
      _ ≤ K * L := hKL
  have h1 := (jx_allBlk.1 (h (i / L) hs)) (i % L) (Nat.mod_lt _ hL)
  have heq : Nat.mul (i / L) L + i % L = i := by
    rw [Nat.mul_eq, Nat.mul_comm]; exact Nat.div_add_mod i L
  rw [heq] at h1
  have hb : Nat.blt i N = true := by rw [Nat.blt_eq]; exact hi
  rw [jx_bIf, hb, cond_true] at h1
  exact h1

private theorem jx_isInv {b : ℕ} {MR : ℕ → ℕ} {k : ℕ} :
    isInvJ b MR k = true ↔ k ≠ 0 ∧ mtJ b MR k k = 0 := by
  unfold isInvJ
  simp only [jx_bIf, jx_c1, jx_c3, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => by simp [h] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by cases h : Nat.beq k 0; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1, h2⟩

private theorem jx_reps_spec {b N : ℕ} {MR : ℕ → ℕ} : ∀ reps : List (ℕ × ℕ),
    repsJX b N MR reps = true → ∀ ab ∈ reps, ab.1 < N ∧ ab.2 < N ∧
      isInvJ b MR ab.1 = true ∧ isInvJ b MR ab.2 = true
  | [], _, ab, hab => absurd hab List.not_mem_nil
  | x :: t, h, ab, hab => by
    have h' : (bAnd(Nat.blt x.1 N, bAnd(Nat.blt x.2 N, bAnd(isInvJ b MR x.1,
        bAnd(isInvJ b MR x.2, repsJX b N MR t))))) = true := h
    simp only [jx_bIf, jx_c1, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨h1, h2, h3, h4, h5⟩ := h'
    rcases List.mem_cons.1 hab with rfl | hab
    · exact ⟨h1, h2, h3, h4⟩
    · exact jx_reps_spec t h5 ab hab

private theorem jx_invs_mem {b : ℕ} {MR : ℕ → ℕ} : ∀ (n j : ℕ),
    j ∈ invsJX b n MR ↔ j < n ∧ isInvJ b MR j = true
  | 0, j => by simp [invsJX]
  | n + 1, j => by
    have ih := jx_invs_mem (b := b) (MR := MR) n j
    have e : invsJX b (n + 1) MR = Bool.rec (motive := fun _ => List Nat) (invsJX b n MR)
        (List.cons n (invsJX b n MR)) (isInvJ b MR n) := rfl
    rw [e]
    cases hn : isInvJ b MR n
    · simp only [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · subst h; rw [hn] at h2; exact absurd h2 (by simp)
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨by omega, hn⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl h

private theorem jx_rec1 (P : ℕ → Bool) : ∀ L : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun k _ ih2 => bAnd(P k, ih2)) L = true →
      ∀ k ∈ L, P k = true
  | [], _, k, hk => absurd hk List.not_mem_nil
  | x :: t, h, k, hk => by
    have h' : (bAnd(P x, List.rec (motive := fun _ => Bool) true (fun k _ ih2 => bAnd(P k, ih2)) t))
      = true := h
    rw [jx_bIf, jx_c1, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h'.1
    · exact jx_rec1 P t h'.2 k hk

private theorem jx_rec2 (Q : ℕ → ℕ → Bool) (L : List ℕ) : ∀ L' : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(List.rec (motive := fun _ => Bool)
      true (fun k _ ih2 => bAnd(Q j k, ih2)) L, ih)) L' = true →
      ∀ j ∈ L', ∀ k ∈ L, Q j k = true
  | [], _, j, hj => absurd hj List.not_mem_nil
  | x :: t, h, j, hj => by
    have h' : (bAnd(List.rec (motive := fun _ => Bool)
      true (fun k _ ih2 => bAnd(Q x k, ih2)) L, List.rec (motive := fun _ => Bool) true
      (fun j _ ih => bAnd(List.rec (motive := fun _ => Bool)
      true (fun k _ ih2 => bAnd(Q j k, ih2)) L, ih)) t)) = true := h
    rw [jx_bIf, jx_c1, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hj with rfl | hj
    · exact jx_rec1 _ L h'.1
    · exact jx_rec2 Q L t h'.2 j hj

private theorem jx_tri_spec {b gb N : ℕ} {MR GW : ℕ → ℕ} {i : ℕ}
    (h : triJX b gb N MR GW i = true) (hi : isInvJ b MR i = true) :
    ∀ j < N, isInvJ b MR j = true → ∀ k < N, isInvJ b MR k = true →
      tripJ b gb MR GW i j k = true := by
  unfold triJX at h
  rw [jx_bIf, hi, cond_true] at h
  intro j hj hjj k hk hkk
  exact jx_rec2 (fun j k => tripJ b gb MR GW i j k) _ _ h j
    ((jx_invs_mem N j).2 ⟨hj, hjj⟩) k ((jx_invs_mem N k).2 ⟨hk, hkk⟩)

private theorem jx_trip_spec {b gb : ℕ} {MR GW : ℕ → ℕ} {i j k : ℕ}
    (h : tripJ b gb MR GW i j k = true)
    (hc : i ≠ j ∧ i ≠ k ∧ i ≠ mtJ b MR j k ∧ j ≠ k ∧ mtJ b MR i j = mtJ b MR j i ∧
      mtJ b MR i k = mtJ b MR k i ∧ mtJ b MR j k = mtJ b MR k j) :
    goodJ gb GW i j = true ∨ goodJ gb GW i k = true ∨ goodJ gb GW j k = true := by
  unfold tripJ at h
  simp only [jx_bIf, jx_c1, jx_c2, jx_c3, jx_c4, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Nat.beq_eq] at h
  have e : ∀ x y : ℕ, Nat.beq x y = decide (x = y) := fun x y => by
    cases hh : Nat.beq x y
    · have : ¬ x = y := fun hxy => by rw [hxy] at hh; simp at hh
      simp [this]
    · simp [Nat.eq_of_beq_eq_true hh]
  rcases h with h | h
  · exfalso
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    have b1 : Nat.beq i j = false := by rw [e]; simpa using c1
    have b2 : Nat.beq i k = false := by rw [e]; simpa using c2
    have b3 : Nat.beq i (mtJ b MR j k) = false := by rw [e]; simpa using c3
    have b4 : Nat.beq j k = false := by rw [e]; simpa using c4
    have b5 : Nat.beq (mtJ b MR i j) (mtJ b MR j i) = true := by rw [e]; simpa using c5
    have b6 : Nat.beq (mtJ b MR i k) (mtJ b MR k i) = true := by rw [e]; simpa using c6
    have b7 : Nat.beq (mtJ b MR j k) (mtJ b MR k j) = true := by rw [e]; simpa using c7
    rw [b1, b2, b3, b4, b5, b6, b7] at h
    simp at h
  · exact h

private theorem jx_len2 (L : List (ℕ × ℕ)) : len2 L = L.length := by
  induction L with
  | nil => rfl
  | cons x t ih => exact congrArg Nat.succ ih

private theorem jx_getP2 (L : List (ℕ × ℕ)) : ∀ k, getP2 L k = L.getD k (0, 0) := by
  induction L with
  | nil => intro k; cases k <;> rfl
  | cons x t ih => intro k; cases k with
    | zero => rfl
    | succ k => exact ih k

private theorem jx_wit_spec {b N : ℕ} {MR IT : ℕ → ℕ} {reps : List (ℕ × ℕ)} {i j v : ℕ}
    (h : witJ b N MR IT reps i j v = true) (hv : v ≠ 0) :
    ∃ ab ∈ reps, ∃ s < N, isInvJ b MR i = true ∧ isInvJ b MR j = true ∧
      mtJ b MR i j = mtJ b MR j i ∧ conjJ b MR IT s i ≠ conjJ b MR IT s j ∧
      inFgJ b MR ab.1 ab.2 (conjJ b MR IT s i) = true ∧
      inFgJ b MR ab.1 ab.2 (conjJ b MR IT s j) = true := by
  unfold witJ at h
  have hv0 : Nat.beq v 0 = false := by
    cases hh : Nat.beq v 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) hv
  rw [jx_bIf, hv0, cond_false] at h
  simp only [jx_strictB, jx_bIf, jx_c1, jx_c3, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
    Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [jx_len2] at h4
  have hmem : getP2 reps ((v.sub 1).shiftRight 8) ∈ reps := by
    rw [jx_getP2, List.getD_eq_getElem _ _ h4]
    exact List.getElem_mem h4
  refine ⟨_, hmem, (v.sub 1).land 255, h5, h1, h2, h3, ?_, h7, h8⟩
  intro heq
  rw [heq] at h6
  simp at h6

private theorem jx_beq (x y : ℕ) : Nat.beq x y = decide (x = y) := by
  cases hh : Nat.beq x y
  · have : ¬ x = y := fun hxy => by rw [hxy] at hh; simp at hh
    simp [this]
  · simp [Nat.eq_of_beq_eq_true hh]

private theorem jx_goodTbl {N : ℕ} {mulF : ℕ → ℕ → ℕ} {invF : ℕ → ℕ} {reps : List (ℕ × ℕ)}
    {i j : ℕ} (hi : i < N) (hj : j < N) (h1 : isInvF mulF i = true) (h2 : isInvF mulF j = true)
    (h3 : mulF i j = mulF j i) (h4 : goodPairF N mulF invF reps i j = true) :
    (goodTblF N mulF invF reps).getD (i * N + j) false = true := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hi
  have hk : i * N + j < N * N := by
    calc i * N + j < i * N + N := by omega
      _ = (i + 1) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right N hi
  have hdiv : (i * N + j) / N = i := by
    rw [Nat.mul_comm i N, Nat.mul_add_div hN, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * N + j) % N = j := by
    rw [Nat.mul_comm i N, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp only [goodTblF, hk, hdiv, hmod, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range, Option.map_some, Option.getD_some, if_true,
    Bool.and_eq_true, h1, h2, h4, beq_iff_eq, h3, and_self]

private theorem jx_inFg {b N : ℕ} {MR : ℕ → ℕ} {mulF : ℕ → ℕ → ℕ} {a b' : ℕ}
    (ha : a < N) (hb : b' < N) (hmul : ∀ i < N, ∀ j < N, mulF i j = mtJ b MR i j) (u : ℕ) :
    inFgF mulF a b' u = inFgJ b MR a b' u := by
  unfold inFgF inFgJ
  rw [hmul a ha b' hb]
  simp only [jx_bIf, jx_beq, Bool.or_eq_true]
  by_cases h1 : u = a <;> by_cases h2 : u = b' <;> simp [h1, h2, beq_eq_decide]

open CFSG.KC.Enum CFSG.KC.LQT.SV in
theorem idxJX_sound {b gb N ng K L : ℕ} {tab par lab : List ℕ} {reps : List (ℕ × ℕ)}
    {PT LT TB MR IT GW : ℕ → ℕ}
    (hp : ∀ i < N, par.getD i 0 = PT i) (hl : ∀ i < N, lab.getD i 0 = LT i)
    (ht : ∀ i < N * ng, tab.getD i 0 = TB i) (hKL : N ≤ K * L)
    (hr : ∀ s < K, rowsJX b gb N ng PT LT TB MR IT GW reps (Nat.mul s L) L = true)
    (hR : repsJX b N MR reps = true)
    (hT : ∀ s < K, trisJX b gb N MR GW (Nat.mul s L) L = true) :
    mulOKG N ng tab par lab = true ∧ invOKG N (mulG N ng tab par lab) = true ∧
      repsOKG N (mulG N ng tab par lab) reps = true ∧
      tripleOKF N (mulG N ng tab par lab)
        (goodG N (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) reps) = true := by
  have hrow := jx_chunks hKL (f := rowJX b gb N ng PT LT TB MR IT GW reps) hr
  have htri := jx_chunks hKL (f := triJX b gb N MR GW) hT
  have hpar : ∀ j, 0 < j → j < N → par.getD j 0 < j := by
    intro j hj0 hjN
    rw [hp j hjN]
    exact (((row_spec (hrow 0 (by omega))).2.1 j hjN).2 (by omega)).1
  have hMlt : ∀ i < N, ∀ j < N, mtJ b MR i j < N := fun i hi j hj =>
    ((row_spec (hrow i hi)).2.1 j hj).1
  have hM0 : ∀ i < N, mtJ b MR i 0 = i := fun i hi => (row_spec (hrow i hi)).1
  have hMrec : ∀ i < N, ∀ j < N, j ≠ 0 →
      mtJ b MR i j = tab.getD (mtJ b MR i (par.getD j 0) * ng + lab.getD j 0) 0 := by
    intro i hi j hj hj0
    obtain ⟨hp1, hl1, he⟩ := ((row_spec (hrow i hi)).2.1 j hj).2 hj0
    rw [hp j hj, hl j hj, he]
    have hb : mtJ b MR i (PT j) * ng + LT j < N * ng := by
      have := hMlt i hi (PT j) (by omega)
      nlinarith
    exact (ht _ hb).symm
  have hmul : ∀ i < N, ∀ j < N, mulG N ng tab par lab i j = mtJ b MR i j :=
    fun i hi => jx_mul hpar hM0 hMrec hi
  have hinvG : ∀ s < N, invG N (mulG N ng tab par lab) s = IT s := by
    intro s hs
    obtain ⟨hIT, hIT0, hITmin⟩ := (row_spec (hrow s hs)).2.2.1
    unfold invG invTG
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range, hs, if_true, Option.map_some, Option.getD_some]
    rw [List.findIdx_eq (by simpa using hIT)]
    constructor
    · simp [List.getElem_range, hmul s hs _ hIT, hIT0]
    · intro j hj
      simp only [List.getElem_range]
      have := hITmin j hj
      simp [hmul s hs j (by omega), this]
  have hisInv : ∀ k < N, isInvF (mulG N ng tab par lab) k = true ↔ isInvJ b MR k = true := by
    intro k hk
    rw [isInvF_iff, jx_isInv, hmul k hk k hk]
  have hreps := jx_reps_spec reps hR
  have hgood : ∀ i < N, ∀ j < N, goodJ gb GW i j = true →
      goodG N (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) reps i j = true := by
    intro i hi j hj hg
    have hv : pg gb (mask gb) (GW i) j ≠ 0 := by
      intro h0
      unfold goodJ at hg
      rw [jx_bIf] at hg
      have : Nat.beq (pg gb (mask gb) (GW i) j) 0 = true := by rw [h0]; rfl
      rw [this] at hg
      simp at hg
    obtain ⟨ab, hab, s, hs, hi', hj', hcomm, hne, hf1, hf2⟩ :=
      jx_wit_spec ((row_spec (hrow i hi)).2.2.2 j hj) hv
    obtain ⟨a1, a2, -, -⟩ := hreps ab hab
    have hITs := (row_spec (hrow s hs)).2.2.1.1
    have hc : ∀ x < N, conjF (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) s x =
        conjJ b MR IT s x := by
      intro x hx
      unfold conjF conjJ
      rw [hinvG s hs, hmul s hs x hx, hmul _ (hMlt s hs x hx) _ hITs]
    unfold goodG
    refine jx_goodTbl (mulF := mulG N ng tab par lab) (invF := invG N (mulG N ng tab par lab))
      (reps := reps) hi hj ((hisInv i hi).2 hi') ((hisInv j hj).2 hj') ?_ ?_
    · rw [hmul i hi j hj, hmul j hj i hi]; exact hcomm
    · unfold goodPairF
      rw [List.any_eq_true]
      refine ⟨ab, hab, ?_⟩
      rw [List.any_eq_true]
      refine ⟨s, List.mem_range.2 hs, ?_⟩
      rw [hc i hi, hc j hj, jx_inFg a1 a2 hmul, jx_inFg a1 a2 hmul]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨⟨hne, hf1⟩, hf2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mulOKG
    rw [jx_allLt]
    intro i hi
    rw [jx_allLt]
    intro j hj
    have hmij := hmul i hi j hj
    have hlt := hMlt i hi j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [if_true, hmij, hM0 i hi]
      simp [hi]
    · have hpj := hpar j (by omega) hj
      simp only [if_neg hj0, hmij, hmul i hi _ (by omega : par.getD j 0 < N)]
      rw [← hMrec i hi j hj hj0]
      simp [hlt]
  · unfold invOKG
    rw [jx_allLt]
    intro s hs
    obtain ⟨hIT, hIT0, hITmin⟩ := (row_spec (hrow s hs)).2.2.1
    rw [hinvG s hs, hmul s hs _ hIT]
    simp [hIT, hIT0]
  · unfold repsOKG
    rw [List.all_eq_true]
    intro ab hab
    obtain ⟨a1, a2, a3, a4⟩ := hreps ab hab
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨a1, a2⟩, (hisInv _ a1).2 a3⟩, (hisInv _ a2).2 a4⟩
  · unfold tripleOKF
    simp only [List.all_eq_true, List.mem_filter, List.mem_range]
    intro i ⟨hi, hii⟩ j ⟨hj, hjj⟩ k ⟨hk, hkk⟩
    have hiJ := (hisInv i hi).1 hii
    have hjJ := (hisInv j hj).1 hjj
    have hkJ := (hisInv k hk).1 hkk
    have hm := hmul j hj k hk
    by_cases hcb : (i != j && i != k && i != mulG N ng tab par lab j k && j != k &&
        mulG N ng tab par lab i j == mulG N ng tab par lab j i &&
        mulG N ng tab par lab i k == mulG N ng tab par lab k i &&
        mulG N ng tab par lab j k == mulG N ng tab par lab k j) = true
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hcb
      obtain ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := hcb
      rw [hmul i hi j hj, hmul j hj i hi] at c5
      rw [hmul i hi k hk, hmul k hk i hi] at c6
      rw [hmul j hj k hk, hmul k hk j hj] at c7
      rw [hmul j hj k hk] at c3
      have hts := jx_trip_spec (jx_tri_spec (htri i hi) hiJ j hj hjJ k hk hkJ)
        ⟨c1, c2, c3, c4, c5, c6, c7⟩
      have hcase : goodG N (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) reps i j = true ∨
          goodG N (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) reps i k = true ∨
          goodG N (mulG N ng tab par lab) (invG N (mulG N ng tab par lab)) reps j k = true := by
        rcases hts with h | h | h
        · exact Or.inl (hgood i hi j hj h)
        · exact Or.inr (Or.inl (hgood i hi k hk h))
        · exact Or.inr (Or.inr (hgood j hj k hk h))
      rcases hcase with h | h | h <;> simp [h]
    · simp only [Bool.not_eq_true] at hcb
      rw [hcb]
      simp

open CFSG.KC.Enum CFSG.KC.LQT.SV in
theorem idxJX_tab {b gb N ng K L : ℕ} {tab par lab : List ℕ} {reps : List (ℕ × ℕ)}
    {PT LT TB MR IT GW : ℕ → ℕ}
    (hp : ∀ i < N, par.getD i 0 = PT i) (hl : ∀ i < N, lab.getD i 0 = LT i)
    (ht : ∀ i < N * ng, tab.getD i 0 = TB i) (hKL : N ≤ K * L)
    (hr : ∀ s < K, rowsJX b gb N ng PT LT TB MR IT GW reps (Nat.mul s L) L = true) :
    (∀ i < N, ∀ j < N, mulG N ng tab par lab i j = mtJ b MR i j ∧ mtJ b MR i j < N) ∧
      (∀ s < N, invG N (mulG N ng tab par lab) s = IT s ∧ IT s < N) ∧
      (∀ k < N, isInvJ b MR k = true ↔ k ≠ 0 ∧ mtJ b MR k k = 0) := by
  have hrow := jx_chunks hKL (f := rowJX b gb N ng PT LT TB MR IT GW reps) hr
  have hpar : ∀ j, 0 < j → j < N → par.getD j 0 < j := by
    intro j hj0 hjN
    rw [hp j hjN]
    exact (((row_spec (hrow 0 (by omega))).2.1 j hjN).2 (by omega)).1
  have hMlt : ∀ i < N, ∀ j < N, mtJ b MR i j < N := fun i hi j hj =>
    ((row_spec (hrow i hi)).2.1 j hj).1
  have hM0 : ∀ i < N, mtJ b MR i 0 = i := fun i hi => (row_spec (hrow i hi)).1
  have hMrec : ∀ i < N, ∀ j < N, j ≠ 0 →
      mtJ b MR i j = tab.getD (mtJ b MR i (par.getD j 0) * ng + lab.getD j 0) 0 := by
    intro i hi j hj hj0
    obtain ⟨hp1, hl1, he⟩ := ((row_spec (hrow i hi)).2.1 j hj).2 hj0
    rw [hp j hj, hl j hj, he]
    have hb : mtJ b MR i (PT j) * ng + LT j < N * ng := by
      have := hMlt i hi (PT j) (by omega)
      nlinarith
    exact (ht _ hb).symm
  have hmul : ∀ i < N, ∀ j < N, mulG N ng tab par lab i j = mtJ b MR i j :=
    fun i hi => jx_mul hpar hM0 hMrec hi
  refine ⟨fun i hi j hj => ⟨hmul i hi j hj, hMlt i hi j hj⟩, fun s hs => ?_,
    fun k _ => jx_isInv⟩
  obtain ⟨hIT, hIT0, hITmin⟩ := (row_spec (hrow s hs)).2.2.1
  refine ⟨?_, hIT⟩
  unfold invG invTG
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range, hs, if_true, Option.map_some, Option.getD_some]
  rw [List.findIdx_eq (by simpa using hIT)]
  constructor
  · simp [List.getElem_range, hmul s hs _ hIT, hIT0]
  · intro j hj
    simp only [List.getElem_range]
    have := hITmin j hj
    simp [hmul s hs j (by omega), this]

end CFSG.KC.LQT.JX

end
