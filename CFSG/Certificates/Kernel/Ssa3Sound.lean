module

public import Certificates.Data.Kernel.Ssa3
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.Ssa3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop

variable {d : Nat}

@[expose] noncomputable def val (A B : Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) :
    Nat → Matrix (Fin d) (Fin d) (ZMod 3)
  | 0 => A
  | 1 => B
  | 2 => 1
  | x + 3 =>
    if h : D.na.getD x 0 < x + 3 ∧ D.nb.getD x 0 < x + 3 then
      if D.nk.getD x 1 = 0 then val A B D (D.na.getD x 0) * val A B D (D.nb.getD x 0)
      else val A B D (D.na.getD x 0) ^ D.nk.getD x 1
    else 1
  termination_by x => x
  decreasing_by all_goals omega

@[expose] noncomputable def evalM (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData)
    (w : Word) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  (w.map fun p => M (D.fv.getD p.1 0) ^ p.2).prod

@[expose] def factM (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) (n : Nat) :
    MFact → Prop
  | .ord r e => r < n ∧ 0 < e ∧ M (D.fv.getD r 0) ^ e = 1
  | .conj h u w => h < n ∧ wordLt n u = true ∧ wordLt n w = true ∧
      M (D.fv.getD h 0) * evalM M D u = evalM M D w * M (D.fv.getD h 0)
  | .ne w₁ w₂ t => wordLt n w₁ = true ∧ wordLt n w₂ = true ∧
      ∃ ht : t < d, evalM M D w₁ ⟨t, ht⟩ ≠ evalM M D w₂ ⟨t, ht⟩
  | .eq w₁ w₂ => wordLt n w₁ = true ∧ wordLt n w₂ = true ∧ evalM M D w₁ = evalM M D w₂

@[expose] def cmpM (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) (q : Nat) : Prop :=
  if D.qk.getD q 0 = 0 then M (D.qx.getD q 0) = M (D.qy.getD q 0)
  else ∃ ht : D.qt.getD q 0 < d,
    M (D.qx.getD q 0) ⟨D.qt.getD q 0, ht⟩ ≠ M (D.qy.getD q 0) ⟨D.qt.getD q 0, ht⟩

theorem ssa3S_nodes : ∀ (j : Nat) (ks as bs ss : List Nat), nodesS j ks as bs ss = true →
    ∀ t < ks.length, as.getD t 0 < 3 + j + t ∧ bs.getD t 0 < 3 + j + t := by
  intro j ks
  induction ks generalizing j with
  | nil => intro _ _ _ _ t ht; simp at ht
  | cons k ks ih =>
    intro as bs ss h t ht
    rcases as with _ | ⟨a, as⟩ <;> rcases bs with _ | ⟨b, bs⟩ <;> rcases ss with _ | ⟨s, ss⟩ <;>
      try (simp [nodesS] at h; done)
    simp only [nodesS, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, _⟩, h3⟩ := h
    cases t with
    | zero => simp only [List.getD_cons_zero]; omega
    | succ t =>
      have := ih (j + 1) as bs ss h3 t (by simpa using ht)
      simp only [List.getD_cons_succ]
      omega

theorem ssa3S_bounds {D : SData} (hs : structS D = true) {t : Nat} (ht : t < D.nk.length) :
    D.na.getD t 0 < t + 3 ∧ D.nb.getD t 0 < t + 3 := by
  unfold structS at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  have := ssa3S_nodes 0 _ _ _ _ hn t ht
  omega

theorem ssa3S_val_node (A B : Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) (t : Nat)
    (hb : D.na.getD t 0 < t + 3 ∧ D.nb.getD t 0 < t + 3) :
    val A B D (t + 3) = if D.nk.getD t 1 = 0 then val A B D (D.na.getD t 0) * val A B D (D.nb.getD t 0)
      else val A B D (D.na.getD t 0) ^ D.nk.getD t 1 := by
  rw [val, dif_pos hb]

theorem ssa3S_val_two (A B : Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) : val A B D 2 = 1 := by
  rw [val]

theorem ssa3S_lt_len {l : List Nat} {t : Nat} (h : l.getD t 1 ≠ 1) : t < l.length := by
  by_contra hc
  exact h (List.getD_eq_default _ _ (by omega))

theorem ssa3S_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

theorem ssa3S_pid {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} (hs : structS D = true)
    {y e x : Nat} (h : pidS D y e x = true) : val A B D x = val A B D y ^ e := by
  unfold pidS at h
  by_cases he0 : e = 0
  · subst he0
    have hx : x = 2 := Nat.eq_of_beq_eq_true h
    rw [hx, ssa3S_val_two, pow_zero]
  · by_cases he1 : e = 1
    · subst he1
      have hx : x = y := Nat.eq_of_beq_eq_true h
      rw [hx, pow_one]
    · rw [ssa3S_beq_false he0, ssa3S_beq_false he1] at h
      simp only [cond_false, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
      obtain ⟨⟨h3, hk⟩, ha⟩ := h
      have ht : x - 3 < D.nk.length := ssa3S_lt_len (by omega)
      have hx : x = (x - 3) + 3 := by omega
      rw [hx, ssa3S_val_node A B D (x - 3) (ssa3S_bounds hs ht), if_neg (by omega), hk, ha]

theorem ssa3S_mul {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} (hs : structS D = true)
    {y z x : Nat} (h : mulS D y z x = true) : val A B D x = val A B D y * val A B D z := by
  unfold mulS at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h3, hk⟩, ha⟩, hb⟩ := h
  have ht : x - 3 < D.nk.length := ssa3S_lt_len (by omega)
  have hx : x = (x - 3) + 3 := by omega
  rw [hx, ssa3S_val_node A B D (x - 3) (ssa3S_bounds hs ht), if_pos hk, ha, hb]

theorem ssa3S_wid {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} (hs : structS D = true) :
    ∀ (w : Word) (x : Nat), widS D w x = true → val A B D x = evalM (val A B D) D w
  | [], x, h => by
    have hx : x = 2 := Nat.eq_of_beq_eq_true h
    rw [hx, ssa3S_val_two]
    rfl
  | [(r, e)], x, h => by
    rw [ssa3S_pid hs h]
    simp [evalM]
  | (r, e) :: p :: w, x, h => by
    simp only [widS, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [ssa3S_mul hs h1, ssa3S_pid hs h2, ssa3S_wid hs (p :: w) _ h3]
    simp only [evalM, List.map_cons, List.prod_cons]

theorem ssa3S_qk {l : List Nat} {q : Nat} (h : l.getD q 1 = 0) : l.getD q 0 = 0 := by
  have hq : q < l.length := ssa3S_lt_len (by omega)
  rw [List.getD_eq_getElem _ _ hq] at h ⊢
  exact h

theorem factM_of_cmp {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} {n q : Nat}
    {f : MFact} (hs : structS D = true) (hq : factS D n q f = true)
    (hm : cmpM (val A B D) D q) : factM (val A B D) D n f := by
  unfold cmpM at hm
  cases f with
  | ord r e =>
    simp only [factS, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hq
    obtain ⟨⟨⟨⟨hk, hr⟩, he⟩, hp⟩, hy⟩ := hq
    rw [if_pos (ssa3S_qk hk), ssa3S_pid hs hp, hy, ssa3S_val_two] at hm
    exact ⟨hr, he, hm⟩
  | conj h u w =>
    simp only [factS, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hq
    obtain ⟨⟨⟨⟨⟨⟨⟨hk, hh⟩, hu⟩, hw⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hq
    rw [if_pos (ssa3S_qk hk), ssa3S_mul hs h1, ssa3S_mul hs h3, ssa3S_wid hs u _ h2,
      ssa3S_wid hs w _ h4] at hm
    exact ⟨hh, hu, hw, hm⟩
  | ne w₁ w₂ t =>
    simp only [factS, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hq
    obtain ⟨⟨⟨⟨⟨hk, h1⟩, h2⟩, ht⟩, hx⟩, hy⟩ := hq
    have hk' : D.qk.getD q 0 ≠ 0 := fun e => by rw [e] at hk; exact Bool.noConfusion hk
    rw [if_neg hk', ssa3S_wid hs w₁ _ hx, ssa3S_wid hs w₂ _ hy, ht] at hm
    exact ⟨h1, h2, hm⟩
  | eq w₁ w₂ =>
    simp only [factS, Bool.and_eq_true, Nat.beq_eq] at hq
    obtain ⟨⟨⟨⟨hk, h1⟩, h2⟩, hx⟩, hy⟩ := hq
    rw [if_pos (ssa3S_qk hk), ssa3S_wid hs w₁ _ hx, ssa3S_wid hs w₂ _ hy] at hm
    exact ⟨h1, h2, hm⟩

def ssa3S_Rep (R : Ar) (X : Nat) (M : Matrix (Fin R.d) (Fin R.d) (ZMod 3)) : Prop :=
  Canon3 R.n X ∧ mat3 R.d R.n X = M

def ssa3S_RecOK (R : Ar) (D : SData) (lo : Nat) : Prop :=
  ∀ t < lo, D.ns.getD t 0 ≠ 0 →
    ssa3S_Rep R (R.mt (D.ns.getD t 0 - 1)) (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D (t + 3))

def ssa3S_LOK (R : Ar) (D : SData) (lo : Nat) (L : List Nat) : Prop :=
  ∀ t < L.length,
    ssa3S_Rep R (L.getD t 0) (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D (lo + t + 3))

@[expose] noncomputable def ssa3S_powR (mul : Nat → Nat → Nat) (one X e : Nat) (i : Nat) :
    Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Nat → Bool → Nat) (fun acc st => bif st then acc else one)
    (fun i ih acc st =>
      bif st then
        strictN (mul acc acc) fun s =>
          bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then strictN (mul s X) fun t => ih t true
          else ih s true
      else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ih X true else ih acc false)
    i

theorem ssa3S_powT_eq (mul : Nat → Nat → Nat) (one X e : Nat) :
    powT mul one X e = ssa3S_powR mul one X e 16 one false := rfl

theorem ssa3S_powR_succ (mul : Nat → Nat → Nat) (one X e i acc : Nat) (st : Bool) :
    ssa3S_powR mul one X e (i + 1) acc st =
      bif st then
        bif Nat.beq (e / 2 ^ i % 2) 1 then ssa3S_powR mul one X e i (mul (mul acc acc) X) true
        else ssa3S_powR mul one X e i (mul acc acc) true
      else bif Nat.beq (e / 2 ^ i % 2) 1 then ssa3S_powR mul one X e i X true
        else ssa3S_powR mul one X e i acc false := by
  have hb : Nat.land (Nat.shiftRight e i) 1 = e / 2 ^ i % 2 := by
    rw [land_eq3, shr_eq3, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have e0 : ssa3S_powR mul one X e (i + 1) acc st =
      bif st then
        strictN (mul acc acc) fun s =>
          bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then
            strictN (mul s X) fun t => ssa3S_powR mul one X e i t true
          else ssa3S_powR mul one X e i s true
      else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ssa3S_powR mul one X e i X true
        else ssa3S_powR mul one X e i acc false := rfl
  rw [e0]
  simp only [hb, strictN_eq3]

theorem ssa3S_powR_rep {R : Ar}
    (hmulR : ∀ X Y M N, ssa3S_Rep R X M → ssa3S_Rep R Y N → ssa3S_Rep R (R.mul X Y) (M * N))
    (hone : ssa3S_Rep R R.one 1) {X : Nat} {M : Matrix (Fin R.d) (Fin R.d) (ZMod 3)}
    (hX : ssa3S_Rep R X M) (e : Nat) :
    ∀ i acc st, (st = true → ssa3S_Rep R acc (M ^ (e / 2 ^ i))) → (st = false → e / 2 ^ i = 0) →
      ssa3S_Rep R (ssa3S_powR R.mul R.one X e i acc st) (M ^ e) := by
  have h01 : Nat.beq 0 1 = false := rfl
  have h11 : Nat.beq 1 1 = true := rfl
  intro i
  induction i with
  | zero =>
    intro acc st h1 h2
    cases st
    · have h := h2 rfl
      rw [Nat.pow_zero, Nat.div_one] at h
      rw [h, pow_zero]
      exact hone
    · have h := h1 rfl
      rw [Nat.pow_zero, Nat.div_one] at h
      exact h
  | succ i ih =>
    intro acc st h1 h2
    have hd : e / 2 ^ i = 2 * (e / 2 ^ (i + 1)) + e / 2 ^ i % 2 := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      exact (Nat.div_add_mod _ 2).symm
    rw [ssa3S_powR_succ]
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ i) with hb | hb <;> rw [hb] at hd ⊢ <;> cases st
    · simp only [h01, cond_false]
      exact ih acc false (fun h => Bool.noConfusion h) (fun _ => by have := h2 rfl; omega)
    · simp only [h01, cond_false, cond_true]
      refine ih _ true (fun _ => ?_) (fun h => Bool.noConfusion h)
      have h := hmulR _ _ _ _ (h1 rfl) (h1 rfl)
      rwa [← pow_add, ← two_mul, ← Nat.add_zero (2 * (e / 2 ^ (i + 1))), ← hd] at h
    · simp only [h11, cond_false, cond_true]
      refine ih _ true (fun _ => ?_) (fun h => Bool.noConfusion h)
      have h0 := h2 rfl
      rw [hd, h0]
      simpa using hX
    · simp only [h11, cond_true]
      refine ih _ true (fun _ => ?_) (fun h => Bool.noConfusion h)
      have h := hmulR _ _ _ _ (hmulR _ _ _ _ (h1 rfl) (h1 rfl)) hX
      rwa [← pow_add, ← pow_succ, ← two_mul, ← hd] at h

theorem ssa3S_powT_rep {R : Ar}
    (hmulR : ∀ X Y M N, ssa3S_Rep R X M → ssa3S_Rep R Y N → ssa3S_Rep R (R.mul X Y) (M * N))
    (hone : ssa3S_Rep R R.one 1) {X : Nat} {M : Matrix (Fin R.d) (Fin R.d) (ZMod 3)}
    (hX : ssa3S_Rep R X M) {e : Nat} (he : e < 65536) :
    ssa3S_Rep R (powT R.mul R.one X e) (M ^ e) := by
  rw [ssa3S_powT_eq]
  exact ssa3S_powR_rep hmulR hone hX e 16 R.one false (fun h => Bool.noConfusion h)
    (fun _ => Nat.div_eq_of_lt (lt_of_lt_of_eq he (by norm_num)))

theorem ssa3S_kinds : ∀ (j : Nat) (ks as bs ss : List Nat), nodesS j ks as bs ss = true →
    ∀ t < ks.length, ks.getD t 1 < 65536 := by
  intro j ks
  induction ks generalizing j with
  | nil => intro _ _ _ _ t ht; simp at ht
  | cons k ks ih =>
    intro as bs ss h t ht
    rcases as with _ | ⟨a, as⟩ <;> rcases bs with _ | ⟨b, bs⟩ <;> rcases ss with _ | ⟨s, ss⟩ <;>
      try (simp [nodesS] at h; done)
    simp only [nodesS, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨⟨_, hk⟩, h3⟩ := h
    cases t with
    | zero => simp only [List.getD_cons_zero]; omega
    | succ t =>
      simp only [List.getD_cons_succ]
      exact ih (j + 1) as bs ss h3 t (by simpa using ht)

theorem ssa3S_kind {D : SData} (hs : structS D = true) {t : Nat} (ht : t < D.nk.length) :
    D.nk.getD t 1 < 65536 := by
  unfold structS at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  exact ssa3S_kinds 0 _ _ _ _ hn t ht

theorem ssa3S_asc : ∀ (l : List Nat), ascS l = true →
    ∀ i j, i ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0
  | [], _, i, j, _, hj => by simp at hj
  | [a], _, i, j, hij, hj => by
    simp only [List.length_singleton] at hj
    have hj0 : j = 0 := by omega
    have hi0 : i = 0 := by omega
    rw [hj0, hi0]
  | a :: b :: l, h, i, j, hij, hj => by
    simp only [ascS, Bool.and_eq_true, Nat.ble_eq] at h
    have ih := ssa3S_asc (b :: l) h.2
    cases j with
    | zero =>
      have hi0 : i = 0 := by omega
      rw [hi0]
    | succ j =>
      cases i with
      | zero =>
        have := ih 0 j (Nat.zero_le _) (by simpa using hj)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at this ⊢
        omega
      | succ i =>
        simp only [List.getD_cons_succ]
        exact ih i j (by omega) (by simpa using hj)

theorem ssa3S_boundsS {l : List Nat} {m : Nat} (h : boundsS l m = true) :
    l.getD 0 0 = 0 ∧ l.getD (l.length - 1) 0 = m ∧ ascS l = true := by
  unfold boundsS at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0, hm⟩, ha⟩ := h
  rcases l with _ | ⟨a, l⟩
  · simp at h0
  · refine ⟨by simpa using h0, ?_, ha⟩
    rw [← hm, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem ssa3S_find (g : Nat → Nat) (q : Nat) (h0 : g 0 = 0) :
    ∀ n, q < g n → ∃ c < n, g c ≤ q ∧ q < g (c + 1)
  | 0, h => by omega
  | n + 1, h => by
    by_cases hn : g n ≤ q
    · exact ⟨n, by omega, hn, h⟩
    · obtain ⟨c, hc, h1, h2⟩ := ssa3S_find g q h0 n (by omega)
      exact ⟨c, by omega, h1, h2⟩

theorem ssa3S_recRep {R : Ar} {D : SData} {lo x : Nat} (hA : Canon3 R.n R.sa)
    (hB : Canon3 R.n R.sb) (hone : ssa3S_Rep R R.one 1) (hpre : ssa3S_RecOK R D lo)
    (hx : availS D lo x = true) :
    ssa3S_Rep R (recV R D x) (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D x) := by
  by_cases h0 : x = 0
  · subst h0
    refine ⟨hA, ?_⟩
    rw [val]
    rfl
  by_cases h1 : x = 1
  · subst h1
    refine ⟨hB, ?_⟩
    rw [val]
    rfl
  by_cases h2 : x = 2
  · subst h2
    rw [ssa3S_val_two]
    exact hone
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 3 := ⟨x - 3, by omega⟩
  unfold availS at hx
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.add_sub_cancel] at hx
  rcases hx with hx | ⟨hy, hn⟩
  · omega
  · have hn' : D.ns.getD y 0 ≠ 0 := fun e => by rw [e] at hn; exact absurd hn (by decide)
    have e : recV R D (y + 3) = R.mt (D.ns.getD y 0 - 1) := by
      unfold recV
      rw [ssa3S_beq_false h0, ssa3S_beq_false h1, ssa3S_beq_false h2]
      simp only [cond_false, Nat.add_sub_cancel, Nat.sub_eq]
    rw [e]
    exact hpre y (by omega) hn'

theorem ssa3S_getRep {R : Ar} {D : SData} {lo j x : Nat} {L : List Nat} (hA : Canon3 R.n R.sa)
    (hB : Canon3 R.n R.sb) (hone : ssa3S_Rep R R.one 1) (hpre : ssa3S_RecOK R D lo)
    (hL : L.length = j - lo) (hLv : ssa3S_LOK R D lo L)
    (hx : (Nat.ble (3 + lo) x || availS D lo x) = true) (hxj : 3 + lo ≤ x → x < 3 + j) :
    ssa3S_Rep R (getV R D lo L x) (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D x) := by
  unfold getV
  by_cases h : 3 + lo ≤ x
  · rw [Nat.ble_eq_true_of_le h, cond_true]
    have := hLv (x - (3 + lo)) (by have := hxj h; omega)
    have e : lo + (x - (3 + lo)) + 3 = x := by omega
    rwa [e] at this
  · have hf : Nat.ble (3 + lo) x = false := Bool.eq_false_iff.2 fun e => h (Nat.le_of_ble_eq_true e)
    rw [hf, cond_false]
    rw [hf, Bool.false_or] at hx
    exact ssa3S_recRep hA hB hone hpre hx

@[expose] noncomputable def ssa3S_nodeV (R : Ar) (D : SData) (lo : Nat) (L : List Nat) (j : Nat) :
    Nat :=
  bif Nat.beq (D.nk.getD j 1) 0 then
    R.mul (getV R D lo L (D.na.getD j 0)) (getV R D lo L (D.nb.getD j 0))
  else powT R.mul R.one (getV R D lo L (D.na.getD j 0)) (D.nk.getD j 1)

theorem ssa3S_runC_succ (R : Ar) (D : SData) (lo : Nat) (fin : List Nat → Nat) (m j : Nat)
    (L : List Nat) :
    runC R D lo fin (m + 1) j L =
      bif (Nat.ble (3 + lo) (D.na.getD j 0) || availS D lo (D.na.getD j 0)) &&
          (!Nat.beq (D.nk.getD j 1) 0 || Nat.ble (3 + lo) (D.nb.getD j 0) ||
            availS D lo (D.nb.getD j 0)) then
        bif Nat.beq (D.ns.getD j 0) 0 ||
            Nat.beq (ssa3S_nodeV R D lo L j) (R.mt (Nat.sub (D.ns.getD j 0) 1)) then
          runC R D lo fin m (j + 1) (L ++ [ssa3S_nodeV R D lo L j])
        else 0
      else 0 := by
  have e0 : runC R D lo fin (m + 1) j L =
      bif (Nat.ble (3 + lo) (D.na.getD j 0) || availS D lo (D.na.getD j 0)) &&
          (!Nat.beq (D.nk.getD j 1) 0 || Nat.ble (3 + lo) (D.nb.getD j 0) ||
            availS D lo (D.nb.getD j 0)) then
        strictN (ssa3S_nodeV R D lo L j) fun v =>
          bif Nat.beq (D.ns.getD j 0) 0 || Nat.beq v (R.mt (Nat.sub (D.ns.getD j 0) 1)) then
            runC R D lo fin m (j + 1) (L ++ [v])
          else 0
      else 0 := rfl
  rw [e0, strictN_eq3]

theorem ssa3S_runC {R : Ar} {D : SData} (hA : Canon3 R.n R.sa) (hB : Canon3 R.n R.sb)
    (hmulR : ∀ X Y M N, ssa3S_Rep R X M → ssa3S_Rep R Y N → ssa3S_Rep R (R.mul X Y) (M * N))
    (hone : ssa3S_Rep R R.one 1) (hs : structS D = true) {lo hi : Nat}
    (hhi : hi ≤ D.nk.length) (hpre : ssa3S_RecOK R D lo) (fin : List Nat → Nat) :
    ∀ m j L, lo ≤ j → j + m = hi → L.length = j - lo → ssa3S_LOK R D lo L →
      runC R D lo fin m j L = 1 →
      (∀ t, j ≤ t → t < hi → D.ns.getD t 0 ≠ 0 →
        ssa3S_Rep R (R.mt (D.ns.getD t 0 - 1)) (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D (t + 3))) ∧
      ∃ L', L'.length = hi - lo ∧ ssa3S_LOK R D lo L' ∧ fin L' = 1 := by
  intro m
  induction m with
  | zero =>
    intro j L hj hjm hLl hLv h
    refine ⟨fun t h1 h2 => by omega, L, by omega, hLv, h⟩
  | succ m ih =>
    intro j L hj hjm hLl hLv h
    rw [ssa3S_runC_succ] at h
    simp only [cond_eq_if] at h
    split_ifs at h with hc hd
    · rw [Bool.and_eq_true] at hc
      obtain ⟨hca, hcb⟩ := hc
      have hjn : j < D.nk.length := by omega
      have hb := ssa3S_bounds hs hjn
      have hrep : ssa3S_Rep R (ssa3S_nodeV R D lo L j)
          (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D (j + 3)) := by
        unfold ssa3S_nodeV
        rw [ssa3S_val_node _ _ D j hb]
        have ha := ssa3S_getRep hA hB hone hpre hLl hLv hca (fun _ => by omega)
        by_cases hk : D.nk.getD j 1 = 0
        · have hk' : Nat.beq (D.nk.getD j 1) 0 = true := by rw [hk]; rfl
          rw [hk', cond_true, if_pos hk]
          rw [hk'] at hcb
          simp only [Bool.not_true, Bool.false_or] at hcb
          exact hmulR _ _ _ _ ha (ssa3S_getRep hA hB hone hpre hLl hLv hcb (fun _ => by omega))
        · rw [ssa3S_beq_false hk, cond_false, if_neg hk]
          exact ssa3S_powT_rep hmulR hone ha (ssa3S_kind hs hjn)
      have hL' : ssa3S_LOK R D lo (L ++ [ssa3S_nodeV R D lo L j]) := by
        intro t ht
        simp only [List.length_append, List.length_singleton] at ht
        by_cases htl : t < L.length
        · have e : (L ++ [ssa3S_nodeV R D lo L j]).getD t 0 = L.getD t 0 := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left htl]
          rw [e]
          exact hLv t htl
        · have htl' : t = L.length := by omega
          have e : (L ++ [ssa3S_nodeV R D lo L j]).getD t 0 = ssa3S_nodeV R D lo L j := by
            simp [List.getD_eq_getElem?_getD, htl']
          have e2 : lo + t + 3 = j + 3 := by omega
          rw [e, e2]
          exact hrep
      obtain ⟨h1, h2⟩ := ih (j + 1) _ (by omega) (by omega)
        (by simp only [List.length_append, List.length_singleton]; omega) hL' h
      refine ⟨fun t ht1 ht2 hn => ?_, h2⟩
      by_cases htj : t = j
      · subst htj
        have hf : Nat.beq (D.ns.getD t 0) 0 = false := ssa3S_beq_false hn
        rw [hf, Bool.false_or] at hd
        have hv : R.mt (D.ns.getD t 0 - 1) = ssa3S_nodeV R D lo L t :=
          (Nat.eq_of_beq_eq_true hd).symm
        rw [hv]
        exact hrep
      · exact h1 t (by omega) ht2 hn

theorem ssa3S_dj {N X : Nat} (hX : Canon3 N X) (t : Nat) :
    (X.testBit t && X.testBit (N + t)) = false := by
  cases h : X.testBit t
  · rfl
  · rw [hX.2 t h]
    rfl

theorem ssa3S_rowDiff {R : Ar} {X Y t : Nat} (hrm : R.rm = 2 ^ R.d - 1)
    (hX : Canon3 R.n X) (hY : Canon3 R.n Y) (ht : t < R.d)
    (he : mat3 R.d R.n X ⟨t, ht⟩ = mat3 R.d R.n Y ⟨t, ht⟩) : rowDiff R X Y t = false := by
  have hent : ∀ k < R.d, X.testBit (R.d * t + k) = Y.testBit (R.d * t + k) ∧
      X.testBit (R.n + (R.d * t + k)) = Y.testBit (R.n + (R.d * t + k)) := by
    intro k hk
    have := congrFun he ⟨k, hk⟩
    unfold mat3 at this
    exact bv_inj _ _ _ _ (ssa3S_dj hX _) (ssa3S_dj hY _) this
  have e1 : Nat.land (Nat.shiftRight X (R.d * t)) R.rm =
      Nat.land (Nat.shiftRight Y (R.d * t)) R.rm := by
    rw [hrm, land_eq3, land_eq3, shr_eq3, shr_eq3]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.testBit_two_pow_sub_one]
    by_cases hk : k < R.d
    · rw [(hent k hk).1]
    · simp [hk]
  have e2 : Nat.land (Nat.shiftRight X (R.n + R.d * t)) R.rm =
      Nat.land (Nat.shiftRight Y (R.n + R.d * t)) R.rm := by
    rw [hrm, land_eq3, land_eq3, shr_eq3, shr_eq3]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.testBit_two_pow_sub_one, Nat.add_assoc]
    by_cases hk : k < R.d
    · rw [(hent k hk).2]
    · simp [hk]
  unfold rowDiff
  rw [e1, e2, Nat.beq_refl, Nat.beq_refl]
  rfl

theorem ssa3S_cmp {R : Ar} {D : SData} {lo hi q : Nat} {L : List Nat} (hA : Canon3 R.n R.sa)
    (hB : Canon3 R.n R.sb) (hone : ssa3S_Rep R R.one 1) (hrm : R.rm = 2 ^ R.d - 1)
    (hpre : ssa3S_RecOK R D lo) (hL : L.length = hi - lo) (hLv : ssa3S_LOK R D lo L)
    (h : cmpOK R D lo hi L q = true) :
    cmpM (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D) D q := by
  have hend : ∀ x, endS D lo hi x = true → ssa3S_Rep R (getV R D lo L x)
      (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D x) := by
    intro x hx
    unfold endS at hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hx
    refine ssa3S_getRep hA hB hone hpre hL hLv ?_ ?_
    · rcases hx with hx | ⟨hx, -⟩
      · rw [hx, Bool.or_true]
      · rw [Nat.ble_eq_true_of_le (Nat.le_of_ble_eq_true hx), Bool.true_or]
    · intro hx3
      rcases hx with hx | ⟨-, hx⟩
      · unfold availS at hx
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hx
        omega
      · omega
  unfold cmpOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hy⟩, h⟩ := h
  have hrx := hend _ hx
  have hry := hend _ hy
  unfold cmpM
  by_cases hk : D.qk.getD q 0 = 0
  · rw [if_pos hk]
    have hk' : Nat.beq (D.qk.getD q 0) 0 = true := by rw [hk]; rfl
    rw [hk', cond_true] at h
    rw [← hrx.2, ← hry.2, Nat.eq_of_beq_eq_true h]
  · rw [if_neg hk]
    rw [ssa3S_beq_false hk, cond_false, Bool.and_eq_true] at h
    obtain ⟨ht, hd⟩ := h
    have ht' : D.qt.getD q 0 < R.d := Nat.le_of_ble_eq_true ht
    refine ⟨ht', fun he => ?_⟩
    have he' : mat3 R.d R.n (getV R D lo L (D.qx.getD q 0)) ⟨D.qt.getD q 0, ht'⟩ =
        mat3 R.d R.n (getV R D lo L (D.qy.getD q 0)) ⟨D.qt.getD q 0, ht'⟩ := by
      rw [hrx.2, hry.2]
      exact he
    rw [ssa3S_rowDiff hrm hrx.1 hry.1 ht' he'] at hd
    exact absurd hd (by decide)

theorem cmpM_of_chunks {R : Ar} {D : SData} {f LO CI UP nc : Nat}
    (hc : consts3OK R.d f R.n LO R.rm CI R.one UP = true) (hmul : R.mul = mul3s R.d R.n LO CI R.rm)
    (hA : Canon3 R.n R.sa) (hB : Canon3 R.n R.sb) (hs : structS D = true)
    (hnc : D.cb.length = nc + 1) (hch : ∀ c < nc, chunkOK R D c = true) :
    ∀ q < D.qk.length, cmpM (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D) D q := by
  obtain ⟨-, -, -, hRM, -, -⟩ := consts3_facts hc
  have hone : ssa3S_Rep R R.one 1 := one3_sound hc
  have hmulR : ∀ X Y M N, ssa3S_Rep R X M → ssa3S_Rep R Y N → ssa3S_Rep R (R.mul X Y) (M * N) := by
    intro X Y M N hX hY
    rw [hmul]
    obtain ⟨h1, h2⟩ := mul3s_sound hc hX.1 hY.1
    exact ⟨h1, by rw [h2, hX.2, hY.2]⟩
  have hs' := hs
  unfold structS at hs'
  simp only [Bool.and_eq_true, Nat.beq_eq] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hcb⟩, hqb⟩, hqbl⟩, -⟩, -⟩, -⟩, -⟩ := hs'
  obtain ⟨hcb0, hcbl, hcba⟩ := ssa3S_boundsS hcb
  obtain ⟨hqb0, hqbl', -⟩ := ssa3S_boundsS hqb
  rw [hnc, Nat.add_sub_cancel] at hcbl
  rw [hqbl, hnc, Nat.add_sub_cancel] at hqbl'
  have hmono : ∀ c ≤ nc, D.cb.getD c 0 ≤ D.cb.getD (c + 1) 0 ∨ c = nc := by
    intro c hc
    by_cases h : c = nc
    · exact Or.inr h
    · exact Or.inl (ssa3S_asc _ hcba c (c + 1) (by omega) (by omega))
  have hle : ∀ c ≤ nc, D.cb.getD c 0 ≤ D.nk.length := by
    intro c hc
    rw [← hcbl]
    exact ssa3S_asc _ hcba c nc hc (by omega)
  have hchunk : ∀ c < nc, ssa3S_RecOK R D (D.cb.getD c 0) →
      (∀ t, D.cb.getD c 0 ≤ t → t < D.cb.getD (c + 1) 0 → D.ns.getD t 0 ≠ 0 →
        ssa3S_Rep R (R.mt (D.ns.getD t 0 - 1))
          (val (mat3 R.d R.n R.sa) (mat3 R.d R.n R.sb) D (t + 3))) ∧
      ∃ L', L'.length = D.cb.getD (c + 1) 0 - D.cb.getD c 0 ∧
        ssa3S_LOK R D (D.cb.getD c 0) L' ∧
        (List.range' (D.qb.getD c 0) (D.qb.getD (c + 1) 0 - D.qb.getD c 0)).all
          (cmpOK R D (D.cb.getD c 0) (D.cb.getD (c + 1) 0) L') = true := by
    intro c hc hpre
    have hlohi : D.cb.getD c 0 ≤ D.cb.getD (c + 1) 0 := by
      rcases hmono c hc.le with h | h
      · exact h
      · omega
    have hrun := Nat.eq_of_beq_eq_true (hch c hc)
    obtain ⟨h1, L', hL1, hL2, hL3⟩ := ssa3S_runC hA hB hmulR hone hs (hle (c + 1) hc) hpre _
      _ _ [] le_rfl (by omega) (by simp) (fun t ht => by simp at ht) hrun
    refine ⟨h1, L', hL1, hL2, ?_⟩
    cases hb : (List.range' (D.qb.getD c 0) (D.qb.getD (c + 1) 0 - D.qb.getD c 0)).all
        (cmpOK R D (D.cb.getD c 0) (D.cb.getD (c + 1) 0) L')
    · have h0 : (bif false then (1 : Nat) else 0) = 1 := by
        rw [← hb]
        exact hL3
      exact absurd h0 (by decide)
    · rfl
  have hpreAll : ∀ c ≤ nc, ssa3S_RecOK R D (D.cb.getD c 0) := by
    intro c
    induction c with
    | zero =>
      intro _ t ht
      rw [hcb0] at ht
      omega
    | succ c ih =>
      intro hc t ht hn
      have hp := ih (by omega)
      by_cases htc : t < D.cb.getD c 0
      · exact hp t htc hn
      · exact (hchunk c (by omega) hp).1 t (by omega) ht hn
  intro q hq
  obtain ⟨c, hc, hq1, hq2⟩ := ssa3S_find (fun c => D.qb.getD c 0) q hqb0 nc (by rw [hqbl']; exact hq)
  have hp := hpreAll c hc.le
  obtain ⟨-, L', hL1, hL2, hall⟩ := hchunk c hc hp
  have hcq := List.all_eq_true.1 hall q (List.mem_range'_1.2 ⟨hq1, by omega⟩)
  exact ssa3S_cmp hA hB hone hRM hp hL1 hL2 hcq

end CFSG.KC.Ssa3

end
