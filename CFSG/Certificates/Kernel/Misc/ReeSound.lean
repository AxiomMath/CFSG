module

public import CFSG.Certificates.Kernel.Misc.ReeLanes
public import CFSG.Walter.Ree.Bombieri.AppSpec

public section

namespace CFSG.KC.Misc.Ree

open Polynomial CFSG.Walter.Ree.Bombieri

theorem root_sound {k F G M15 ML nb : ℕ} (hs : setupK k F G M15 ML = true)
    (hr : rootK k G M15 ML nb = true) :
    (decL F).coeff k ≠ 0 ∧ decL F ∣ X ^ 3 ^ k - X := by
  obtain ⟨E, hc⟩ := setup_env hs
  refine ⟨hc, ?_⟩
  unfold rootK at hr
  simp only [strictB_eq, bAnd_eq] at hr
  obtain ⟨hb, hp⟩ := hr
  have hX := rep_X (k := k) E.one_lt
  obtain ⟨Q, hQ, hQe⟩ := E.powK (e := 3 ^ k) hX (bitsLe_lt hb)
  have h1 : Rep 4294967296 2 k Q :=
    Eq.mp (congrArg (fun x => Rep x 2 k Q) (Nat.eq_of_beq_eq_true hp)) hQ
  have hQX : Q = X := by rw [← h1.decL_eq (by norm_num), hX.decL_eq (by norm_num)]
  apply dvd_of_qf
  rw [map_pow, ← hQe, hQX]

theorem arith_of {k b s a : ℕ} (h : arithK k b s a = true) : ArithFacts k b s a := by
  unfold arithK at h
  simp only [strictB_eq, bAnd_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7⟩

theorem case_sound {k F G M15 ML b s a w ns na nq : ℕ} (hs : setupK k F G M15 ML = true)
    (hc : caseB k G M15 ML b s a w ns na nq = true) : CaseFacts (decL F) k b := by
  obtain ⟨E, -⟩ := setup_env hs
  unfold caseB at hc
  simp only [strictB_eq, bAnd_eq] at hc
  obtain ⟨hA, hsn, han, hen, hw1, hw2, hfin⟩ := hc
  refine ⟨s, a, arith_of hA, ?_⟩
  have hk : 2 ≤ k := E.one_lt
  obtain ⟨Z, hZ, hZe⟩ := E.powK (e := s) (rep_X1 hk) (bitsLe_lt hsn)
  obtain ⟨Y, hY, hYe⟩ := E.powK (e := s) (rep_X2 hk) (bitsLe_lt hsn)
  obtain ⟨Z1, hZ1, hZ1e⟩ := E.powK (e := 3 ^ b + 1) hZ (bitsLe_lt hen)
  obtain ⟨Y1, hY1, hY1e⟩ := E.powK (e := 3 ^ b + 1) hY (bitsLe_lt hen)
  have hU := E.red3' (hZ1.add (hY1.add hY1)) (by norm_num) (by omega)
  have hUm := E.red3' (hU.add (Rep.natCast 2)) (by norm_num) (by omega)
  have hUp := E.red3' (hU.add (Rep.natCast 1)) (by norm_num) (by omega)
  obtain ⟨Am, hAm, hAme⟩ := E.powK (e := a) hUm (bitsLe_lt han)
  obtain ⟨Cp, hCp, hCpe⟩ := E.powK (e := a) hUp (bitsLe_lt han)
  obtain ⟨Bu, hBu, hBue⟩ := E.powK (e := a) hU (bitsLe_lt han)
  have hzy := E.red3' ((hZ.add (hY.add hY)).add (Rep.natCast 1)) (by norm_num) (by omega)
  obtain ⟨M1, hM1, hM1e⟩ := E.mulK hZ hAm
  obtain ⟨M2, hM2, hM2e⟩ := E.mulK hzy hBu
  obtain ⟨M3, hM3, hM3e⟩ := E.mulK hY hCp
  obtain ⟨M4, hM4, hM4e⟩ := E.mulK hAm hCp
  have hT := E.red3' ((hM1.add ((Rep.natCast 2).mul hM2)).add
    (((Rep.natCast 2).mul hM3).add hM4)) (by norm_num) (by omega)
  obtain ⟨P1, hP1, hP1e⟩ := E.mulK hU hUm
  obtain ⟨P2, hP2, hP2e⟩ := E.mulK hP1 hUp
  obtain ⟨P3, hP3, hP3e⟩ := E.mulK hP2 hT
  obtain ⟨W, hW⟩ := E.rep_of_checks hw1 hw2
  obtain ⟨R, hR, hRe⟩ := E.mulK hP3 hW
  have hR1 : Rep 1 2 k R :=
    Eq.mp (congrArg (fun x => Rep x 2 k R) (Nat.eq_of_beq_eq_true hfin)) hR
  have hR1' : R = 1 := by
    rw [← hR1.decL_eq (by norm_num), (Rep.one (k := k) (by omega)).decL_eq (by norm_num)]
  refine ⟨W, dvd_of_qf ?_⟩
  set π := qf (decL F)
  have h3 := qf_three (decL F)
  have hx2 : π X + 2 = π X - 1 := by linear_combination h3
  have hz : π Z = (π X + 1) ^ s := by rw [hZe, map_add, map_one]
  have hy : π Y = (π X - 1) ^ s := by rw [hYe, map_add, map_ofNat, hx2]
  have hUe : π (Z1 + (Y1 + Y1)) = π (oddU b s) := by
    rw [map_add, map_add, hZ1e, hY1e, hz, hy]
    simp only [oddU, map_sub, map_pow, map_add, map_one]
    linear_combination ((π X - 1) ^ s) ^ (3 ^ b + 1) * h3
  have hUme : π (Z1 + (Y1 + Y1) + ((2 : ℕ) : (ZMod 3)[X])) = π (oddU b s) - 1 := by
    rw [map_add, hUe, map_natCast, Nat.cast_ofNat]
    linear_combination h3
  have hUpe : π (Z1 + (Y1 + Y1) + ((1 : ℕ) : (ZMod 3)[X])) = π (oddU b s) + 1 := by
    rw [map_add, hUe, map_natCast, Nat.cast_one]
  have hzye : π (Z + (Y + Y) + ((1 : ℕ) : (ZMod 3)[X])) =
      (π X + 1) ^ s + 2 * (π X - 1) ^ s + 1 := by
    rw [map_add, map_add, map_add, hz, hy, map_natCast, Nat.cast_one]
    ring
  have hTe : π (M1 + ((2 : ℕ) : (ZMod 3)[X]) * M2 + (((2 : ℕ) : (ZMod 3)[X]) * M3 + M4)) =
      π (oddT b s a) := by
    rw [map_add, map_add, map_add, map_mul, map_mul, hM1e, hM2e, hM3e, hM4e, hAme, hCpe, hBue,
      hUme, hUpe, hUe, hzye, hz, hy, map_natCast, Nat.cast_ofNat]
    simp only [oddT, map_sub, map_mul, map_pow, map_add, map_one]
    linear_combination (((π X + 1) ^ s + (π X - 1) ^ s + 1) * π (oddU b s) ^ a +
      (π X - 1) ^ s * (π (oddU b s) + 1) ^ a) * h3
  have hfin : π 1 = π P3 * π W := by rw [← hR1', hRe]
  rw [hfin, hP3e, hP2e, hP1e, hTe, hUme, hUpe, hUe]
  simp only [map_mul, map_sub, map_add, map_one]

theorem skip_sound {k b : ℕ} (h : skipB k b = true) : Skip k b := by
  unfold skipB at h
  unfold Skip
  cases h1 : Nat.beq (Nat.gcd b k) (nat_lit 1)
  · exact Or.inl (Nat.ne_of_beq_eq_false h1)
  · rw [h1] at h
    cases h2 : Nat.beq (Nat.mod (Nat.add b b) k) (nat_lit 1)
    · rw [h2] at h
      cases h3 : Nat.beq (Nat.gcd (Nat.add (Nat.pow (nat_lit 3) b) (nat_lit 2))
          (Nat.sub (Nat.pow (nat_lit 3) k) (nat_lit 1))) (nat_lit 1)
      · exact Or.inr (Or.inr (Nat.ne_of_beq_eq_false h3))
      · rw [h3] at h
        exact absurd h (by decide)
    · exact Or.inr (Or.inl (by rw [two_mul]; exact Nat.eq_of_beq_eq_true h2))

@[expose] def CaseOK (k G M15 ML b : ℕ) : Prop :=
  skipB k b = true ∨ ∃ s a w ns na nq : ℕ, caseB k G M15 ML b s a w ns na nq = true

theorem caseOK_skip (k G M15 ML b : ℕ) (h : skipB k b = true) : CaseOK k G M15 ML b := Or.inl h

theorem caseOK_case (k G M15 ML b s a w ns na nq : ℕ)
    (h : caseB k G M15 ML b s a w ns na nq = true) : CaseOK k G M15 ML b :=
  Or.inr ⟨s, a, w, ns, na, nq, h⟩

theorem all_lt_succ {P : ℕ → Prop} {n : ℕ} (h : ∀ b < n, P b) (hn : P n) : ∀ b < n + 1, P b := by
  intro b hb
  rcases Nat.lt_or_ge b n with h1 | h1
  · exact h b h1
  · obtain rfl : b = n := by omega
    exact hn

theorem all_lt_zero {P : ℕ → Prop} : ∀ b < 0, P b := fun _ hb => absurd hb (Nat.not_lt_zero _)

theorem odd_range {P : ℕ → Prop} {lo n : ℕ} (hlo : lo % 2 = 1) (h : ∀ i < n, P (lo + 2 * i)) :
    ∀ k, lo ≤ k → k + 2 ≤ lo + 2 * n → k % 2 = 1 → P k := by
  intro k h1 h2 h3
  obtain ⟨i, rfl⟩ : ∃ i, k = lo + 2 * i := ⟨(k - lo) / 2, by omega⟩
  exact h i (by omega)

theorem appOK_of {k F G M15 ML nb : ℕ} (hs : setupK k F G M15 ML = true)
    (hr : rootK k G M15 ML nb = true) (hb : ∀ b < k, CaseOK k G M15 ML b) : AppOK k := by
  obtain ⟨h1, h2⟩ := root_sound hs hr
  refine ⟨decL F, h1, h2, fun b hb' => ?_⟩
  rcases hb b hb' with h | ⟨s, a, w, ns, na, nq, h⟩
  · exact Or.inl (skip_sound h)
  · exact Or.inr (case_sound hs h)

end CFSG.KC.Misc.Ree

end
