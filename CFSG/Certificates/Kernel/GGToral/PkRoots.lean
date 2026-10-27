module

public import CFSG.Certificates.Kernel.GGToral.PkLetter
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertRoots

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType

@[simp] theorem rd_cons (k : ℕ → List ℕ → Bool) (x : ℕ) (s : List ℕ) : rd k (x :: s) = k x s := rfl

@[simp] theorem rd_nil (k : ℕ → List ℕ → Bool) : rd k [] = false := rfl

theorem hdK_spec {k : Hd → List ℕ → Bool} {D : List ℕ} (h : hdK k D = true) :
    ∃ H s, k H s = true ∧ ∀ k' : Hd → List ℕ → Bool, hdK k' D = k' H s := by
  match D, h with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: s, h =>
    exact ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, s, h, fun _ => rfl⟩

theorem rdN_spec {m : ℕ} : ∀ {k : List ℕ → List ℕ → Bool} {s : List ℕ}, rdN m k s = true →
    ∃ l t, k l t = true := by
  induction m with
  | zero => exact fun h => ⟨[], _, h⟩
  | succ m ih =>
    intro k s h
    cases s with
    | nil => exact absurd h (by simp [rdN, rd])
    | cons x s1 =>
      obtain ⟨l, t, h1⟩ := ih (k := fun l s2 => k (x :: l) s2) (s := s1) h
      exact ⟨x :: l, t, h1⟩

theorem rootIs_spec {H : Hd} {c r s k : ℕ} (h : rootIs H c r s k = true) (j : ℕ) (hj : j < k) :
    ((c / 16 ^ j % 16 : ℕ) : ℤ) - 8 = if s = 1 then -(rtC H r j : ℤ) else (rtC H r j : ℤ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    change andB _ (rootIs H c r s k) = true at h
    rw [andB_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih h2 hj
    · have hd : Nat.mod (Nat.shiftRight c (Nat.mul 4 j)) 16 = c / 16 ^ j % 16 := by
        change (c >>> (4 * j)) % 16 = _
        rw [Nat.shiftRight_eq_div_pow, pow_mul]
        norm_num
      change Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq s 1) = true at h1
      rw [hd] at h1
      unfold rtC
      by_cases hs : s = 1
      · have hb : Nat.beq s 1 = true := Nat.beq_eq_true_eq _ _ ▸ hs
        rw [hb] at h1
        have h3 : c / 16 ^ j % 16 + lane (row H.rrev r) (Nat.sub (Nat.sub H.n 1) j) = 8 :=
          Nat.eq_of_beq_eq_true h1
        rw [if_pos hs]
        omega
      · have hb : Nat.beq s 1 = false := Bool.eq_false_iff.mpr fun h => hs (Nat.eq_of_beq_eq_true h)
        rw [hb] at h1
        have h3 : c / 16 ^ j % 16 = 8 + lane (row H.rrev r) (Nat.sub (Nat.sub H.n 1) j) :=
          Nat.eq_of_beq_eq_true h1
        rw [if_neg hs]
        omega

theorem memB_iff (m r : ℕ) : memB m r = true ↔ m.testBit r = true := by
  unfold memB
  rw [Nat.blt_eq]
  change 0 < m &&& (1 <<< r) ↔ _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow]
  cases m.testBit r <;> simp

theorem rixK_spec {H : Hd} (codes : List ℕ) : ∀ (m : ℕ) (R : List ℕ), rixK H codes m R ≠ 0 →
    (∀ k < codes.length, ∃ r < H.np, ∃ s < 2, rootIs H (codes.getD k 0) r s H.n = true) ∧
    ∀ r, memB (rixK H codes m R) r = true →
      memB m r = true ∨ ∃ k < codes.length, rootIs H (codes.getD k 0) r 0 H.n = true := by
  induction codes with
  | nil =>
    intro m R h
    refine ⟨fun k hk => absurd hk (by simp), fun r hr => Or.inl ?_⟩
    cases R with
    | nil => exact hr
    | cons x xs => exact absurd rfl h
  | cons c cs ih =>
    intro m R h
    cases R with
    | nil => exact absurd rfl h
    | cons x xs =>
      change Bool.rec (motive := fun _ => ℕ) 0 _ _ ≠ 0 at h
      change (∀ k < (c :: cs).length, _) ∧ ∀ r, memB (Bool.rec (motive := fun _ => ℕ) 0 _ _) r = true → _
      generalize hok : andB (Nat.blt (x / 2) H.np) (andB (Nat.blt (x % 2) 2)
        (rootIs H c (x / 2) (x % 2) H.n)) = ok at h ⊢
      cases ok with
      | false => exact absurd rfl h
      | true =>
        simp only [andB_eq_true, Nat.blt_eq] at hok
        obtain ⟨hx1, hx2, hx3⟩ := hok
        simp only at h ⊢
        obtain ⟨ih1, ih2⟩ := ih _ xs h
        refine ⟨fun k hk => ?_, fun r hr => ?_⟩
        · cases k with
          | zero => exact ⟨x / 2, hx1, x % 2, hx2, hx3⟩
          | succ k => exact ih1 k (by simp at hk; omega)
        · rcases ih2 r hr with h1 | ⟨k, hk, h2⟩
          · generalize hs : Nat.beq (x % 2) 0 = b at h1
            cases b with
            | false => exact Or.inl h1
            | true =>
              simp only at h1
              rw [memB_iff] at h1
              change (m ||| (1 <<< (x / 2))).testBit r = true at h1
              rw [Nat.testBit_or] at h1
              rcases Bool.or_eq_true_iff.mp h1 with h3 | h3
              · exact Or.inl ((memB_iff m r).mpr h3)
              · rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h3
                have h4 : x / 2 = r := of_decide_eq_true h3
                have h5 : x % 2 = 0 := Nat.eq_of_beq_eq_true hs
                refine Or.inr ⟨0, by simp, ?_⟩
                rw [← h4]
                rw [h5] at hx3
                exact hx3
          · exact Or.inr ⟨k + 1, by simp; omega, h2⟩

theorem pkHead_spec {codes D : List ℕ} {H : Hd} {s : List ℕ}
    (hD : ∀ k' : Hd → List ℕ → Bool, hdK k' D = k' H s) (hnp : 0 < H.np)
    (h : pkHead codes D = true) :
    (∀ k < codes.length, ∃ r < H.np, ∃ t < 2, rootIs H (codes.getD k 0) r t H.n = true) ∧
    ∀ r < H.np, ∃ k < codes.length, rootIs H (codes.getD k 0) r 0 H.n = true := by
  unfold pkHead at h
  rw [hD] at h
  cases s with
  | nil => exact absurd h (by simp)
  | cons nr s1 =>
    simp only [rd_cons] at h
    obtain ⟨R, -, hR⟩ := rdN_spec h
    have hm : rixK H codes 0 R = 2 ^ H.np - 1 := by
      rw [Nat.eq_of_beq_eq_true hR]
      change (1 <<< H.np) - 1 = _
      rw [Nat.shiftLeft_eq, one_mul]
    have hne : rixK H codes 0 R ≠ 0 := by
      rw [hm]
      have : 2 ≤ 2 ^ H.np := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
      omega
    obtain ⟨h1, h2⟩ := rixK_spec codes 0 R hne
    refine ⟨h1, fun r hr => ?_⟩
    have hb : memB (rixK H codes 0 R) r = true := by
      rw [memB_iff, hm, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hr
    rcases h2 r hb with h3 | h3
    · rw [memB_iff, Nat.zero_testBit] at h3
      exact absurd h3 (by simp)
    · exact h3

@[expose] noncomputable def rowZ (τ : Tag) (H : Hd) (r : ℕ) : Fin τ.rank → ℤ := fun j => (rtC H r j : ℤ)

theorem rows_roots {τ : Tag} {D : List ℕ} {H : Hd} {s : List ℕ}
    (hD : ∀ k' : Hd → List ℕ → Bool, hdK k' D = k' H s) (hnp : 0 < H.np) (hn : H.n = τ.rank)
    (h : pkHead τ.rootCertificate.roots D = true) :
    (∀ r < H.np, IsRoot τ (rowZ τ H r)) ∧
    ∀ α, IsRoot τ α → ∃ r < H.np, α = rowZ τ H r ∨ α = -rowZ τ H r := by
  obtain ⟨h1, h2⟩ := pkHead_spec hD hnp h
  have hcode : ∀ {k r t : ℕ}, rootIs H (τ.rootCertificate.roots.getD k 0) r t H.n = true →
      τ.rootCertificate.root k = if t = 1 then -rowZ τ H r else rowZ τ H r := fun hk => by
    funext j
    have := rootIs_spec hk j (by rw [hn]; exact j.2)
    unfold RootCertificate.root decodeVec
    rw [this]
    split_ifs <;> rfl
  refine ⟨fun r hr => ?_, fun α hα => ?_⟩
  · obtain ⟨k, hk, hroot⟩ := h2 r hr
    have := hcode hroot
    rw [if_neg (by omega)] at this
    exact StepTwoToralCert.isRoot_iff_exists_index.mpr ⟨k, hk, this.symm⟩
  · obtain ⟨k, hk, rfl⟩ := StepTwoToralCert.isRoot_iff_exists_index.mp hα
    obtain ⟨r, hr, t, ht, hroot⟩ := h1 k hk
    refine ⟨r, hr, ?_⟩
    rw [hcode hroot]
    by_cases h1t : t = 1
    · exact Or.inr (if_pos h1t)
    · exact Or.inl (if_neg h1t)

theorem rtC_le {codes D : List ℕ} {H : Hd} {s : List ℕ}
    (hD : ∀ k' : Hd → List ℕ → Bool, hdK k' D = k' H s) (hnp : 0 < H.np)
    (h : pkHead codes D = true) : ∀ r < H.np, ∀ j < H.n, rtC H r j ≤ 7 := by
  intro r hr j hj
  obtain ⟨k, -, hk⟩ := (pkHead_spec hD hnp h).2 r hr
  have h1 := rootIs_spec hk j hj
  rw [if_neg (by omega)] at h1
  have h2 := Nat.mod_lt (codes.getD k 0 / 16 ^ j) (by norm_num : 0 < 16)
  omega

theorem tagHdOK_rrev {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) :
    ∀ r < H.np, row H.rrev r < 2 ^ (16 * H.n) := by
  simp only [tagHdOK, andB_eq_true] at h
  intro r hr
  have := allN_eq_true.mp h.2.2.2.2.2.2.2.2.2.2.1 r hr
  rw [Nat.blt_eq] at this
  change row H.rrev r < 1 <<< (16 * H.n) at this
  rwa [Nat.shiftLeft_eq, one_mul] at this

theorem killed_iff {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) {r : ℕ}
    (hr : r < H.np) (h7 : ∀ j < H.n, rtC H r j ≤ 7) {v : ℕ} (hv : red H v = true) :
    killed H r v = true ↔ latChar p (vecZ p τ.rank v) (rowZ τ H r) = 0 := by
  obtain ⟨-, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hvlt, hvl⟩ := red_spec hpos hv
  have hrow := tagHdOK_rrev h r hr
  have hn0 : 0 < H.n := by
    rw [hn]
    cases τ <;> decide
  have hr' : row H.rrev r = packN H.n (fun k => rtC H r (H.n - 1 - k)) :=
    (eq_packN_lane hrow).trans (packN_congr fun k hk => by
      unfold rtC
      congr 1
      change k = H.n - 1 - (H.n - 1 - k)
      omega)
  have hdot : dotR H (row H.rrev r) v = ∑ l ∈ Finset.range H.n, rtC H r l * lane v l := by
    unfold dotR
    rw [hr']
    nth_rewrite 1 [eq_packN_lane hvlt]
    exact lane_mul_rev (F := 7) (G := 15) hn0 h7 (fun j hj => by have := hvl j hj; omega)
      (by have : H.n ≤ 8 := by rw [hn]; cases τ <;> decide
          omega)
  have hlat : latChar p (vecZ p τ.rank v) (rowZ τ H r) =
      ((∑ l ∈ Finset.range H.n, rtC H r l * lane v l : ℕ) : ZMod p) := by
    rw [latChar, hn]
    push_cast
    rw [Finset.sum_range (fun l => ((rtC H r l : ℕ) : ZMod p) * ((lane v l : ℕ) : ZMod p))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [rowZ, vecZ, Int.cast_natCast]
  have : NeZero p := ⟨by omega⟩
  unfold killed
  rw [hdot, hlat, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, ← hpp]
  exact ⟨Nat.eq_of_beq_eq_true, fun h0 => Nat.beq_eq_true_eq _ _ ▸ h0⟩

end CFSG.KC.GGToral
