module

public import CFSG.Certificates.Kernel.Spor.CBLevelSound
public import CFSG.Certificates.Kernel.Spor.PackFld
public import Certificates.Data.Kernel.Spor.ChainK

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KS.PackFld

@[expose] noncomputable def cbPtF (n m len : Nat) (STEP : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat)
    (k : Nat) : Bool :=
  strictB (PTS k) fun x => strictB (PAR k) fun p => strictB (LAB k) fun l =>
  bAnd(Nat.blt x n, bAnd(Nat.beq (POS x) k,
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
      bAnd(Nat.blt p k, bAnd(Nat.blt l (Nat.mul (nat_lit 2) len),
        bIf(Nat.blt l len, Nat.beq (STEP l (PTS p)) x, Nat.beq (STEP (Nat.sub l len) x) (PTS p))))),
  bAnd(bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) m,
      lexLt p l (PAR (Nat.succ k)) (LAB (Nat.succ k)), true)),
    allN len fun t => strictB (STEP t x) fun y => strictB (POS y) fun kk =>
      bAnd(Nat.blt y n, bAnd(Nat.blt kk m, bAnd(bIf(Nat.beq kk (nat_lit 0), true,
        Bool.not (lexLt k t (PAR kk) (LAB kk))),
        bIf(Nat.beq k (nat_lit 0), true,
          Bool.not (lexLt kk (Nat.add len t) (PAR k) (LAB k))))))))))

@[expose] noncomputable def cbPtRangeF (n m len : Nat) (STEP : Nat → Nat → Nat)
    (PTS POS PAR LAB : Nat → Nat) (lo cnt : Nat) : Bool :=
  allBlk lo (fun k => bIf(Nat.blt k m, cbPtF n m len STEP PTS POS PAR LAB k, true)) cnt

theorem cbf_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem cbf_ne {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact absurd h (by decide)

theorem blt_false_of{a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (lt_of_blt e) h

theorem bnot_of {b : Bool} (h : b = false) : Bool.not b = true := by
  rw [h]
  rfl

theorem false_of_bnot {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem cbPtF_facts {n m len k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : cbPtF n m len STEP PTS POS PAR LAB k = true) :
    PTS k < n ∧ POS (PTS k) = k ∧
      (k ≠ 0 → PAR k < k ∧ LAB k < 2 * len ∧
        (LAB k < len → STEP (LAB k) (PTS (PAR k)) = PTS k) ∧
        (¬ LAB k < len → STEP (LAB k - len) (PTS k) = PTS (PAR k))) ∧
      (k ≠ 0 → k + 1 < m → lexLt (PAR k) (LAB k) (PAR (k + 1)) (LAB (k + 1)) = true) ∧
      ∀ t < len, STEP t (PTS k) < n ∧ POS (STEP t (PTS k)) < m ∧
        (POS (STEP t (PTS k)) ≠ 0 →
          lexLt k t (PAR (POS (STEP t (PTS k)))) (LAB (POS (STEP t (PTS k)))) = false) ∧
        (k ≠ 0 → lexLt (POS (STEP t (PTS k))) (len + t) (PAR k) (LAB k) = false) := by
  unfold cbPtF at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  obtain ⟨h2, h3⟩ := band_iff.1 h2
  obtain ⟨h3, h4⟩ := band_iff.1 h3
  obtain ⟨h4, h5⟩ := band_iff.1 h4
  refine ⟨lt_of_blt h1, Nat.eq_of_beq_eq_true h2, fun hk => ?_, fun hk hk1 => ?_,
    fun t ht => ?_⟩
  · have := (bif_iff.1 h3).2 (cbf_beq_false hk)
    obtain ⟨a1, a2⟩ := band_iff.1 this
    obtain ⟨a2, a3⟩ := band_iff.1 a2
    refine ⟨lt_of_blt a1, lt_of_blt a2, fun hl => ?_, fun hl => ?_⟩
    · exact Nat.eq_of_beq_eq_true ((bif_iff.1 a3).1 (blt_of_lt hl))
    · exact Nat.eq_of_beq_eq_true ((bif_iff.1 a3).2 (blt_false_of hl))
  · have := (bif_iff.1 h4).2 (cbf_beq_false hk)
    exact (bif_iff.1 this).1 (blt_of_lt hk1)
  · have := allN_spec h5 t ht
    rw [strictB_eq, strictB_eq] at this
    obtain ⟨a1, a2⟩ := band_iff.1 this
    obtain ⟨a2, a3⟩ := band_iff.1 a2
    obtain ⟨a3, a4⟩ := band_iff.1 a3
    refine ⟨lt_of_blt a1, lt_of_blt a2, fun hp => ?_, fun hk => ?_⟩
    · exact false_of_bnot ((bif_iff.1 a3).2 (cbf_beq_false hp))
    · exact false_of_bnot ((bif_iff.1 a4).2 (cbf_beq_false hk))

theorem cbPt_of_facts {n m r k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h1 : PTS k < n) (h2 : POS (PTS k) = k)
    (h3 : k ≠ 0 → PAR k < k ∧ LAB k < r ∧ STEP (LAB k) (PTS (PAR k)) = PTS k)
    (h4 : k ≠ 0 → k + 1 < m → lexLt (PAR k) (LAB k) (PAR (k + 1)) (LAB (k + 1)) = true)
    (h5 : ∀ j < r, STEP j (PTS k) < n ∧ POS (STEP j (PTS k)) < m ∧
      (POS (STEP j (PTS k)) ≠ 0 →
        lexLt k j (PAR (POS (STEP j (PTS k)))) (LAB (POS (STEP j (PTS k)))) = false)) :
    cbPt n m r STEP PTS POS PAR LAB k = true := by
  unfold cbPt
  rw [strictB_eq, strictB_eq, strictB_eq]
  refine band_iff.2 ⟨blt_of_lt h1, band_iff.2 ⟨by rw [h2]; exact Nat.beq_refl k,
    band_iff.2 ⟨bif_iff.2 ⟨fun _ => rfl, fun hk => ?_⟩,
    band_iff.2 ⟨bif_iff.2 ⟨fun _ => rfl, fun hk => ?_⟩, allN_of_forall fun j hj => ?_⟩⟩⟩⟩
  · obtain ⟨a1, a2, a3⟩ := h3 (cbf_ne hk)
    exact band_iff.2 ⟨blt_of_lt a1, band_iff.2 ⟨blt_of_lt a2, by rw [a3]; exact Nat.beq_refl _⟩⟩
  · have hk' : k ≠ 0 := cbf_ne hk
    refine bif_iff.2 ⟨fun hs => h4 hk' (lt_of_blt hs), fun _ => rfl⟩
  · obtain ⟨a1, a2, a3⟩ := h5 j hj
    rw [strictB_eq, strictB_eq]
    refine band_iff.2 ⟨blt_of_lt a1, band_iff.2 ⟨blt_of_lt a2, bif_iff.2 ⟨fun _ => rfl, fun hp => ?_⟩⟩⟩
    exact bnot_of (a3 (cbf_ne hp))

theorem cbPt_of_fwd {n m len : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (hmn : m ≤ n) (hinv : ∀ t < len, ∀ x < n, STEP (len + t) (STEP t x) = x)
    (hz : ∀ z < n, cbPos n m PTS POS z = true)
    (hp : ∀ k < m, cbPtF n m len STEP PTS POS PAR LAB k = true) :
    ∀ k < m, cbPt n m (Nat.mul 2 len) STEP PTS POS PAR LAB k = true := by
  have hF := fun k (hk : k < m) => cbPtF_facts (hp k hk)
  have hpos : ∀ y < n, POS y < m → PTS (POS y) = y := by
    intro y hy hq
    have h := hz y hy
    unfold cbPos at h
    rw [strictB_eq] at h
    have hq' : POS y ≠ n := by omega
    have := (bif_iff.1 h).2 (cbf_beq_false hq')
    exact Nat.eq_of_beq_eq_true (band_iff.1 this).2
  have hsurj : ∀ t < len, ∀ k' < m, ∃ k < m, STEP t (PTS k) = PTS k' := by
    intro t ht
    let φ : Fin m → Fin m := fun k => ⟨POS (STEP t (PTS k.val)), ((hF k.val k.2).2.2.2.2 t ht).2.1⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      have e : POS (STEP t (PTS a.val)) = POS (STEP t (PTS b.val)) := congrArg Fin.val hab
      have ea := hpos _ ((hF a.val a.2).2.2.2.2 t ht).1 ((hF a.val a.2).2.2.2.2 t ht).2.1
      have eb := hpos _ ((hF b.val b.2).2.2.2.2 t ht).1 ((hF b.val b.2).2.2.2.2 t ht).2.1
      have es : STEP t (PTS a.val) = STEP t (PTS b.val) := by rw [← ea, ← eb, e]
      have ep : PTS a.val = PTS b.val := by
        rw [← hinv t ht _ (hF a.val a.2).1, ← hinv t ht _ (hF b.val b.2).1, es]
      have ev : a.val = b.val := by
        rw [← (hF a.val a.2).2.1, ← (hF b.val b.2).2.1, ep]
      exact Fin.ext ev
    intro k' hk'
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨k', hk'⟩
    have e : POS (STEP t (PTS a.val)) = k' := congrArg Fin.val ha
    refine ⟨a.val, a.2, ?_⟩
    rw [← hpos _ ((hF a.val a.2).2.2.2.2 t ht).1 ((hF a.val a.2).2.2.2.2 t ht).2.1, e]
  intro k hk
  obtain ⟨f1, f2, f3, f4, f5⟩ := hF k hk
  refine cbPt_of_facts f1 f2 (fun hk0 => ?_) f4 (fun j hj => ?_)
  · obtain ⟨a1, a2, a3, a4⟩ := f3 hk0
    refine ⟨a1, by simpa [Nat.mul_eq] using a2, ?_⟩
    by_cases hl : LAB k < len
    · exact a3 hl
    · have e := a4 hl
      have el : len + (LAB k - len) = LAB k := by omega
      have hlt : LAB k - len < len := by omega
      have hi := hinv _ hlt _ f1
      rw [el] at hi
      rw [← e]
      exact hi
  · by_cases hjl : j < len
    · obtain ⟨b1, b2, b3, -⟩ := f5 j hjl
      exact ⟨b1, b2, b3⟩
    · have hj' : j - len < len := by simp [Nat.mul_eq] at hj; omega
      have ej : j = len + (j - len) := by omega
      obtain ⟨k0, hk0, e0⟩ := hsurj (j - len) hj' k hk
      obtain ⟨g1, g2, -, -, g5⟩ := hF k0 hk0
      have es : STEP j (PTS k) = PTS k0 := by
        have hi := hinv _ hj' _ g1
        rw [← ej] at hi
        rw [← e0]
        exact hi
      obtain ⟨-, -, -, c4⟩ := g5 (j - len) hj'
      rw [es, g2]
      refine ⟨g1, hk0, fun hk0' => ?_⟩
      have := c4 hk0'
      rw [e0, f2, ← ej] at this
      exact this

theorem cbPtF_of_range {n m len NS : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    {F : Nat → Bool} (hF : ∀ s < NS, F s = true)
    (hd : ∀ s, F s = cbPtRangeF n m len STEP PTS POS PAR LAB (Nat.mul s 16) 16) (hm : m ≤ NS * 16) :
    ∀ k < m, cbPtF n m len STEP PTS POS PAR LAB k = true := by
  intro k hk
  have hs := hF (k / 16) (by omega)
  rw [hd] at hs
  unfold cbPtRangeF at hs
  have h := allBlk_spec hs (k % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 16) 16) (k % 16) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e, blt_of_lt hk] at h
  exact h

theorem stepX_inv {F FI : Nat → Nat → Nat} {IDX : Nat → Nat} {len n : Nat}
    (h : ∀ t < len, ∀ x < n, FI (IDX t) (F (IDX t) x) = x) :
    ∀ t < len, ∀ x < n, CFSG.KS.CH.stepX F FI IDX len (len + t)
      (CFSG.KS.CH.stepX F FI IDX len t x) = x := by
  intro t ht x hx
  unfold CFSG.KS.CH.stepX
  simp only [blt_of_lt ht, blt_false_of (by omega : ¬ len + t < len), Nat.sub_eq,
    Nat.add_sub_cancel_left]
  exact h t ht x hx

end CFSG.KS.CB

end
