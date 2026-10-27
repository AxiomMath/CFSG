module

public import Certificates.Data.Kernel.Spor.CBfsK
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.KC.Pack CFSG.ONSchreier.Native

theorem bif_iff {c t e : Bool} : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c <;> simp

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rwa [Nat.blt_eq]

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · have : ¬ a < b := fun h' => by rw [blt_of_lt h'] at h; exact absurd h (by decide)
    simp [this]
  · simp [lt_of_blt h]

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have : ¬ a = b := fun h' => by rw [h', Nat.beq_refl] at h; exact absurd h (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem lexLt_eq (a b c d : Nat) : lexLt a b c d = plexLt a b c d := by
  unfold lexLt plexLt
  rw [blt_dec, beq_dec, blt_dec]
  by_cases h1 : a < c <;> by_cases h2 : a = c <;> by_cases h3 : b < d <;> simp [h1, h2, h3]

theorem allBelowN_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    allBelowN n p = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro i _
  exact h i i.2

theorem ofFn_get {m : Nat} (f : Nat → Nat) {i : Nat} (hi : i < m) :
    (Array.ofFn (n := m) fun k => f k.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem cbPt_facts {n m r k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : cbPt n m r STEP PTS POS PAR LAB k = true) :
    PTS k < n ∧ POS (PTS k) = k ∧
      (k ≠ 0 → PAR k < k ∧ LAB k < r ∧ STEP (LAB k) (PTS (PAR k)) = PTS k) ∧
      (k ≠ 0 → k + 1 < m → lexLt (PAR k) (LAB k) (PAR (k + 1)) (LAB (k + 1)) = true) ∧
      ∀ j < r, STEP j (PTS k) < n ∧ POS (STEP j (PTS k)) < m ∧
        (POS (STEP j (PTS k)) = 0 ∨
          lexLt k j (PAR (POS (STEP j (PTS k)))) (LAB (POS (STEP j (PTS k)))) = false) := by
  unfold cbPt at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  obtain ⟨h2, h3⟩ := band_iff.1 h2
  obtain ⟨h3, h4⟩ := band_iff.1 h3
  obtain ⟨h4, h5⟩ := band_iff.1 h4
  have hk0 : k ≠ 0 → Nat.beq k (nat_lit 0) = false := fun hk => by
    cases e : Nat.beq k (nat_lit 0)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk
  refine ⟨lt_of_blt h1, Nat.eq_of_beq_eq_true h2, fun hk => ?_, fun hk hk1 => ?_,
    fun j hj => ?_⟩
  · have := (bif_iff.1 h3).2 (hk0 hk)
    obtain ⟨a1, a2⟩ := band_iff.1 this
    obtain ⟨a2, a3⟩ := band_iff.1 a2
    exact ⟨lt_of_blt a1, lt_of_blt a2, Nat.eq_of_beq_eq_true a3⟩
  · have := (bif_iff.1 h4).2 (hk0 hk)
    exact (bif_iff.1 this).1 (blt_of_lt hk1)
  · have := allN_spec h5 j hj
    rw [strictB_eq, strictB_eq] at this
    obtain ⟨a1, a2⟩ := band_iff.1 this
    obtain ⟨a2, a3⟩ := band_iff.1 a2
    refine ⟨lt_of_blt a1, lt_of_blt a2, ?_⟩
    obtain ⟨b1, b2⟩ := bif_iff.1 a3
    by_cases e : POS (STEP j (PTS k)) = 0
    · exact Or.inl e
    · refine Or.inr ?_
      have e' : Nat.beq (POS (STEP j (PTS k))) (nat_lit 0) = false := by
        cases e2 : Nat.beq (POS (STEP j (PTS k))) (nat_lit 0)
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e2) e
      have := b2 e'
      cases e3 : lexLt k j (PAR (POS (STEP j (PTS k)))) (LAB (POS (STEP j (PTS k))))
      · rfl
      · rw [e3] at this
        exact absurd this (by decide)

theorem clevelOK_of_cb {n m r root : Nat} {st : Array (Array Nat)} {STEP : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat}
    (hst : st.size = r ∧ ∀ j < r, ∀ x < n, st[j]![x]! = STEP j x)
    (hh : cbHead n m root PTS PAR LAB = true)
    (hp : ∀ k < m, cbPt n m r STEP PTS POS PAR LAB k = true)
    (hz : ∀ z < n, cbPos n m PTS POS z = true) :
    clevelOK n root st ⟨Array.ofFn (n := m) fun k => PTS k.val,
      Array.ofFn (n := n) fun z => POS z.val, Array.ofFn (n := m) fun k => PAR k.val,
      Array.ofFn (n := m) fun k => LAB k.val⟩ = true := by
  unfold cbHead at hh
  obtain ⟨c1, c2⟩ := band_iff.1 hh
  obtain ⟨c2, c3⟩ := band_iff.1 c2
  obtain ⟨c3, -⟩ := band_iff.1 c3
  have hm0 : 0 < m := lt_of_blt c1
  have hmn : m ≤ n := Nat.le_of_ble_eq_true c2
  have hF := fun k (hk : k < m) => cbPt_facts (hp k hk)
  have gP := fun {k : Nat} (hk : k < m) => ofFn_get (m := m) PTS hk
  have gR := fun {k : Nat} (hk : k < m) => ofFn_get (m := m) PAR hk
  have gL := fun {k : Nat} (hk : k < m) => ofFn_get (m := m) LAB hk
  have gO := fun {z : Nat} (hz : z < n) => ofFn_get (m := n) POS hz
  simp only [clevelOK, Array.size_ofFn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hm0, hmn⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [gP hm0]
    exact Nat.eq_of_beq_eq_true c3
  · refine allBelowN_of fun k hk => ?_
    obtain ⟨f1, f2, -⟩ := hF k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [gP hk, gO f1]
    exact ⟨f1, f2⟩
  · refine allBelowN_of fun z hz' => ?_
    have h := hz z hz'
    unfold cbPos at h
    rw [strictB_eq] at h
    obtain ⟨-, b2⟩ := bif_iff.1 h
    rw [gO hz']
    cases e : Nat.beq (POS z) n
    · obtain ⟨d1, d2⟩ := band_iff.1 (b2 e)
      have hq := lt_of_blt d1
      simp only [hq, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq]
      rw [gP hq]
      exact Nat.eq_of_beq_eq_true d2
    · have hq : ¬ POS z < m := by
        rw [Nat.eq_of_beq_eq_true e]
        omega
      simp [hq]
  · refine allBelowN_of fun k hk => ?_
    by_cases k0 : k = 0
    · simp [k0]
    · obtain ⟨-, -, f3, -⟩ := hF k hk
      obtain ⟨e1, e2, e3⟩ := f3 k0
      have hpm : PAR k < m := by omega
      obtain ⟨p1, -⟩ := hF (PAR k) hpm
      simp only [k0, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, false_or]
      rw [gR hk, gL hk, gP hpm, gP hk, hst.1, hst.2 _ e2 _ p1]
      exact ⟨⟨e1, e2⟩, e3⟩
  · refine allBelowN_of fun k hk => ?_
    by_cases k0 : k = 0
    · simp [k0]
    · by_cases k1 : k + 1 < m
      · obtain ⟨-, -, -, f4, -⟩ := hF k hk
        simp only [k0, k1, Bool.or_eq_true, beq_iff_eq, decide_true, Bool.not_true, false_or]
        rw [gR hk, gL hk, gR k1, gL k1, ← lexLt_eq]
        exact Or.inr (f4 k0 k1)
      · simp [k1]
  · refine allBelowN_of fun h hh => allBelowN_of fun j hj => ?_
    rw [hst.1] at hj
    obtain ⟨f1, -, -, -, f5⟩ := hF h hh
    obtain ⟨d1, d2, d3⟩ := f5 j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true']
    rw [gP hh, hst.2 j hj _ f1, gO d1]
    refine ⟨d2, ?_⟩
    rcases d3 with d3 | d3
    · exact Or.inl d3
    · refine Or.inr ?_
      rw [gR d2, gL d2, ← lexLt_eq]
      exact d3

theorem cbPt_of_range {n m r C NS : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (hC : 0 < C) (hm : m ≤ NS * C)
    (h : ∀ s < NS, cbPtRange n m r STEP PTS POS PAR LAB (Nat.mul s C) C = true) :
    ∀ k < m, cbPt n m r STEP PTS POS PAR LAB k = true := by
  intro k hk
  have hs : k / C < NS := by
    rw [Nat.div_lt_iff_lt_mul hC]
    omega
  have h1 := allBlk_spec (h (k / C) hs) (k % C) (Nat.mod_lt _ hC)
  have e : Nat.add (Nat.mul (k / C) C) (k % C) = k := by
    change k / C * C + k % C = k
    rw [Nat.mul_comm]
    exact Nat.div_add_mod k C
  rw [e] at h1
  exact (bif_iff.1 h1).1 (blt_of_lt hk)

end CFSG.KS.CB

end
