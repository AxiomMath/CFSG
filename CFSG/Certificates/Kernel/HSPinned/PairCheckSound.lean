module

public import Certificates.Data.Kernel.HSPinned6101
public import CFSG.Certificates.Kernel.HSPinned.PairBfsSim
public import CFSG.Certificates.Kernel.HSIdentSound

public section

namespace CFSG.KC.HSPinned6101

open Certificates.Kernel.HSPinned6101 CFSG.KC.HSPinnedBfs CFSG.KS.BfsReplay
  CFSG.Sporadic.Recognition.HSPinned.Native Certificates.Kernel.HSIdent

theorem bAnd_true' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem bIf_true' {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem allBelow_spec {m hi : Nat} {f : Nat → Bool} (h : CFSG.KC.Loop.allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true' hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · exact bIf_true' h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true' hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem allR_spec {lo cnt : Nat} {f : Nat → Bool} (h : allR lo cnt f = true) :
    ∀ i < cnt, f (lo + i) = true := by
  intro i hi
  have hs : Nat.shiftRight cnt 6 = cnt / 64 := by
    change cnt >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  exact allBelow_spec h i hi (by rw [Nat.add_eq, hs]; omega)

theorem allR_zero {cnt : Nat} {f : Nat → Bool} (h : allR 0 cnt f = true) :
    ∀ i < cnt, f i = true := fun i hi => by simpa using allR_spec h i hi

theorem allR_cons {lo cnt : Nat} {f : Nat → Bool} (h1 : ∀ i < lo, f i = true)
    (h2 : allR lo cnt f = true) : ∀ i < lo + cnt, f i = true := by
  intro i hi
  rcases Nat.lt_or_ge i lo with h | h
  · exact h1 i h
  · have := allR_spec h2 (i - lo) (by omega)
    rwa [Nat.add_sub_cancel' h] at this

set_option exponentiation.threshold 2048 in
theorem g1100_eq (T i : Nat) : g1100 T i = (T >>> (1100 * i)) &&& (Nat.pow 2 1100 - 1) := rfl

set_option exponentiation.threshold 2048 in
theorem lt_of_testBit_g1100 {T i t : Nat} (h : (g1100 T i).testBit t = true) : t < 1100 := by
  rw [g1100_eq, Nat.testBit_and, Nat.pow_eq, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.2

theorem starAt_spec {fa fb : Nat → Nat} {VAB i : Nat} (h : starAt fa fb VAB i = true) :
    (stars[i]!).length = 22 ∧ (stars[i]!).Nodup ∧
      ∀ x ∈ stars[i]!, fa x ∈ stars[g7 VAB i]! ∧ fb x ∈ stars[g7 VAB (100 + i)]! := by
  unfold starAt at h
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.all_eq_true, List.elem_iff,
    List.contains_iff_mem, Nat.add_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lexB_iff {a b c d : Nat} : lexB a b c d = true ↔ LexLt a b c d := by
  unfold lexB LexLt
  simp [Nat.blt_eq, Nat.beq_eq]

theorem not_lexB_iff {a b c d : Nat} : (!lexB a b c d) = true ↔ ¬ LexLt a b c d := by
  rw [← lexB_iff]
  cases lexB a b c d <;> simp

theorem imgK_eq (VAB off v : Nat) :
    imgK VAB off v = 100 * g7 VAB (off + v / 100) + g7 VAB (off + v % 100) := rfl

theorem vtx_eq {VAB : Nat} (hV : allR 0 100 (vabAt VAB) = true) {i : Nat} (hi : i < 100) :
    vtxA[i]! = g7 VAB i ∧ vtxB[i]! = g7 VAB (100 + i) := by
  have := allR_zero hV i hi
  unfold vabAt at this
  simpa [Nat.beq_eq] using this

theorem img_eqA {VAB : Nat} (hV : allR 0 100 (vabAt VAB) = true) {v : Nat} (hv : v < 10000) :
    img vtxA v = imgK VAB 0 v := by
  rw [img, imgK_eq, (vtx_eq hV (i := v / 100) (by omega)).1,
    (vtx_eq hV (i := v % 100) (by omega)).1]
  simp [pairCode]

theorem img_eqB {VAB : Nat} (hV : allR 0 100 (vabAt VAB) = true) {v : Nat} (hv : v < 10000) :
    img vtxB v = imgK VAB 100 v := by
  rw [img, imgK_eq, (vtx_eq hV (i := v / 100) (by omega)).2,
    (vtx_eq hV (i := v % 100) (by omega)).2]
  rfl

theorem pairAt_spec {D : PD} {VAB y : Nat} (h : pairAt D VAB y = true) :
    g14 D.P y < 10000 ∧ g14 D.TA y < D.n ∧ g14 D.TB y < D.n ∧
      imgK VAB 0 (g14 D.P y) = g14 D.P (g14 D.TA y) ∧
      imgK VAB 100 (g14 D.P y) = g14 D.P (g14 D.TB y) ∧
      g14 D.PS (g14 D.P y) = y ∧
      (y = 0 ∨ (g14 D.PR y < y ∧ ((g14 D.LB y = 1 ∧ g14 D.TA (g14 D.PR y) = y) ∨
        (g14 D.LB y = 2 ∧ g14 D.TB (g14 D.PR y) = y)))) ∧
      (y = 0 ∨ D.n ≤ y + 1 ∨
        LexLt (g14 D.PR y) (g14 D.LB y) (g14 D.PR (y + 1)) (g14 D.LB (y + 1))) ∧
      (g14 D.TA y = 0 ∨ ¬ LexLt y 1 (g14 D.PR (g14 D.TA y)) (g14 D.LB (g14 D.TA y))) ∧
      (g14 D.TB y = 0 ∨ ¬ LexLt y 2 (g14 D.PR (g14 D.TB y)) (g14 D.LB (g14 D.TB y))) := by
  unfold pairAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, Nat.add_eq,
    not_lexB_iff, lexB_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, or_assoc.mp h8, h9, h10⟩

theorem pairData_of {D : PD} {VAB root : Nat} (hV : allR 0 100 (vabAt VAB) = true)
    (hh : headOK D root = true) (hp : ∀ y < D.n, pairAt D VAB y = true)
    (hq : ∀ v < 10000, posAt D v = true) :
    PairData vtxA vtxB D.n (g14 D.P) (g14 D.TA) (g14 D.TB) (g14 D.PR) (g14 D.LB) (g14 D.PS) ∧
      g14 D.P 0 = root := by
  unfold headOK at hh
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hh
  obtain ⟨⟨⟨⟨hn0, hn⟩, hr⟩, hpr⟩, hlb⟩ := hh
  have hP := fun y (hy : y < D.n) => pairAt_spec (hp y hy)
  refine ⟨⟨hn0, hn, fun y hy => (hP y hy).1, fun y hy => (hP y hy).2.1,
    fun y hy => (hP y hy).2.2.1, fun y hy => ?_, fun y hy => ?_,
    fun y hy => (hP y hy).2.2.2.2.2.1, fun v hv hall => ?_, hpr, hlb, fun y h1 h2 => ?_,
    fun y h1 h2 => ?_, fun y hy => (hP y hy).2.2.2.2.2.2.2.2.1,
    fun y hy => (hP y hy).2.2.2.2.2.2.2.2.2⟩, hr⟩
  · rw [img_eqA hV (hP y hy).1]
    exact (hP y hy).2.2.2.1
  · rw [img_eqB hV (hP y hy).1]
    exact (hP y hy).2.2.2.2.1
  · have := hq v hv
    unfold posAt at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    rcases this with h | ⟨h1, h2⟩
    · exact h
    · exact absurd h2 (hall _ h1)
  · rcases (hP y h2).2.2.2.2.2.2.1 with h | h
    · omega
    · exact h
  · rcases (hP y (by omega)).2.2.2.2.2.2.2.1 with h | h | h
    · omega
    · omega
    · exact h

theorem pairOrbOK_of {D : PD} {VAB root : Nat} (hV : allR 0 100 (vabAt VAB) = true)
    (hh : headOK D root = true) (hp : ∀ y < D.n, pairAt D VAB y = true)
    (hq : ∀ v < 10000, posAt D v = true) {cov c : Nat → Nat → Bool}
    (hcc : ∀ x < 100, ∀ y < 100, cov x y = c x y)
    (hc : ∀ x < 100, ∀ y < 100, coverAt D c x y = true) :
    pairOrbOK vtxA vtxB root cov = true := by
  obtain ⟨hD, h0⟩ := pairData_of hV hh hp hq
  rw [← h0, pairOrbOK_eq hD rfl rfl cov]
  refine allIn_iff'.2 fun x _ hx => allIn_iff'.2 fun y _ hy => ?_
  have := hc x hx y hy
  unfold coverAt at this
  rw [hcc x hx y hy]
  simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.add_eq, Nat.mul_eq] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr (decide_eq_true h)

theorem lmask_eq {LM : Nat} (hL : allR 0 100 (lmAt LM) = true) {i : Nat} (hi : i < 100) :
    lmask stars[i]! = g1100 LM i := by
  have := allR_zero hL i hi
  unfold lmAt at this
  simpa [Nat.beq_eq] using this

theorem adjB_eq_adjK {LM : Nat} (hL : allR 0 100 (lmAt LM) = true) {x y : Nat} (hx : x < 100)
    (hy : y < 100) : adjB x y = adjK LM x y := by
  rw [CFSG.KC.HSIdent.adjB_eq hx hy, lmask_eq hL hx, lmask_eq hL hy]
  unfold adjK
  apply Bool.eq_iff_iff.2
  simp [← Bool.not_eq_true, Nat.beq_eq]

theorem covAdj_eq {LM : Nat} (hL : allR 0 100 (lmAt LM) = true) :
    ∀ x < 100, ∀ y < 100, covAdj x y = adjK LM x y := fun _ hx _ hy => adjB_eq_adjK hL hx hy

theorem covNon_eq {LM : Nat} (hL : allR 0 100 (lmAt LM) = true) :
    ∀ x < 100, ∀ y < 100, covNon x y = nonK LM x y := fun x hx y hy => by
  rw [covNon, nonK, adjB_eq_adjK hL hx hy]
  apply Bool.eq_iff_iff.2
  simp [← Bool.not_eq_true, Nat.beq_eq]

end CFSG.KC.HSPinned6101

end
