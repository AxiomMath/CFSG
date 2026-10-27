module

public import CFSG.ClassicalInvolution.Phan.PhanS21Q7SoundB
public import CFSG.ClassicalInvolution.Phan.PhanS20Model

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

theorem two_ne_zero_gf49 : (2 : GF49) ≠ 0 := by decide

@[expose] def candV (c : V7) (b1 b2 b4 b5 b6 : GF49) : V7 :=
  ⟨-(c.x1 * b4 + c.x2 * b5 + (c.x4 * b1 + c.x5 * b2) + (-2) * (c.x6 * b6)), b1, b2, 0, b4, b5,
    b6⟩

theorem candN_dec (c : N7) (n1 n2 n4 n5 n6 : Nat) :
    (candN c n1 n2 n4 n5 n6).dec =
      candV c.dec (gfDec n1) (gfDec n2) (gfDec n4) (gfDec n5) (gfDec n6) := by
  simp only [candN, candV, N7.dec, gfDec_neg, gfDec_add, gfDec_mul, gfDec_kappa, gfDec_zero]

theorem bfC_e0C (b : V7) : bfC e0C b = b.x3 := by
  simp [bfC, e0C]

theorem eq_candV {c b : V7} (hc3 : c.x3 = 1) (hb3 : b.x3 = 0) (h : bfC c b = 0) :
    b = candV c b.x1 b.x2 b.x4 b.x5 b.x6 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := b
  simp only at hc3 hb3
  subst hc3 hb3
  simp only [bfC, candV, V7.mk.injEq, and_true] at h ⊢
  linear_combination h

theorem quad_of_bfC {b : V7} (hb3 : b.x3 = 0) (h : bfC b b = 0) :
    b.x1 * b.x4 + b.x2 * b.x5 = b.x6 ^ 2 := by
  have h1 : (2 : GF49) * (b.x1 * b.x4 + b.x2 * b.x5 - b.x6 ^ 2) = 0 := by
    simp only [bfC, hb3] at h
    linear_combination h
  have h2 := (mul_eq_zero.1 h1).resolve_left two_ne_zero_gf49
  linear_combination h2

@[expose] def NormShape (b : V7) : Prop :=
  b.x1 = 1 ∨ (b.x1 = 0 ∧ b.x2 = 1) ∨ (b.x1 = 0 ∧ b.x2 = 0 ∧ b.x4 = 1) ∨
    (b.x1 = 0 ∧ b.x2 = 0 ∧ b.x4 = 0 ∧ b.x5 = 1)

theorem exists_cand {cN : N7} (hc3 : cN.dec.x3 = 1) {b : V7} (hb3 : b.x3 = 0)
    (hbc : bfC cN.dec b = 0) (hq : b.x1 * b.x4 + b.x2 * b.x5 = b.x6 ^ 2) (hn : NormShape b) :
    ∃ p ∈ q7Cands cN, p.dec = b := by
  have hb := eq_candV hc3 hb3 hbc
  rcases hn with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h4⟩ | ⟨h1, h2, h4, h5⟩
  · obtain ⟨n2, hn2, e2⟩ := gfDec_surj b.x2
    obtain ⟨n5, hn5, e5⟩ := gfDec_surj b.x5
    obtain ⟨n6, hn6, e6⟩ := gfDec_surj b.x6
    refine ⟨candN cN 1 n2 (gfAdd (gfNeg (gfMul n2 n5)) (gfMul n6 n6)) n5 n6, ?_, ?_⟩
    · simp only [q7Cands, candsA, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl (Or.inl ⟨n2, hn2, n5, hn5, n6, hn6, rfl⟩))
    · have h4 : b.x4 = -(b.x2 * b.x5) + b.x6 * b.x6 := by
        rw [h1] at hq
        linear_combination hq
      rw [candN_dec, gfDec_add, gfDec_neg, gfDec_mul, gfDec_mul, gfDec_one, e2, e5, e6]
      conv_rhs => rw [hb, h1, h4]
  · obtain ⟨n4, hn4, e4⟩ := gfDec_surj b.x4
    obtain ⟨n6, hn6, e6⟩ := gfDec_surj b.x6
    refine ⟨candN cN 0 1 n4 (gfMul n6 n6) n6, ?_, ?_⟩
    · simp only [q7Cands, candsB, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨n4, hn4, n6, hn6, rfl⟩))
    · have h5 : b.x5 = b.x6 * b.x6 := by
        rw [h1, h2] at hq
        linear_combination hq
      rw [candN_dec, gfDec_mul, gfDec_zero, gfDec_one, e4, e6]
      conv_rhs => rw [hb, h1, h2, h5]
  · obtain ⟨n5, hn5, e5⟩ := gfDec_surj b.x5
    refine ⟨candN cN 0 0 1 n5 0, ?_, ?_⟩
    · simp only [q7Cands, candsC, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨n5, hn5, rfl⟩)
    · have h6 : b.x6 = 0 := by
        rw [h1, h2] at hq
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (by linear_combination -hq)
      rw [candN_dec, gfDec_zero, gfDec_one, e5]
      conv_rhs => rw [hb, h1, h2, h4, h6]
  · refine ⟨candN cN 0 0 0 1 0, ?_, ?_⟩
    · simp [q7Cands, candsD]
    · have h6 : b.x6 = 0 := by
        rw [h1, h2] at hq
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (by linear_combination -hq)
      rw [candN_dec, gfDec_zero, gfDec_one]
      conv_rhs => rw [hb, h1, h2, h4, h5, h6]

theorem bfC_smulC_right (u : GF49) (c b : V7) : bfC c (smulC u b) = u * bfC c b := by
  simp only [bfC, smulC]
  ring

theorem isFFC_smulC {u : GF49} (hu : u ≠ 0) (x : V7) :
    isFFC (smulC u x) = true ↔ isFFC x = true := by
  rw [← isFF_toVec, ← isFF_toVec, toVec_smulC, isFF_smul m0 hu]

theorem colC_smulC_right {u : GF49} (hu : u ≠ 0) (x y : V7) :
    colC x (smulC u y) = true ↔ colC x y = true := by
  rw [← col_toVec, ← col_toVec, toVec_smulC]
  have := col_smul m0 (c := (1 : GF49)) (d := u) one_ne_zero hu (x := toVec x) (y := toVec y)
  rwa [one_smul] at this

theorem herC_eq_zero_of_zero {c b : V7} (hc3 : c.x3 = 1) (hb3 : b.x3 = 0) (hbc : bfC c b = 0)
    (h1 : b.x1 = 0) (h2 : b.x2 = 0) (h4 : b.x4 = 0) (h5 : b.x5 = 0) (h6 : b.x6 = 0) :
    herC b b = 0 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := b
  simp only at hc3 hb3 h1 h2 h4 h5 h6
  subst hc3 hb3 h1 h2 h4 h5 h6
  have h0 : b0 = 0 := by
    simp only [bfC] at hbc
    linear_combination hbc
  subst h0
  simp [herC, bfC, tauC]

theorem exists_norm {c b : V7} (hc3 : c.x3 = 1) (hb3 : b.x3 = 0) (hbc : bfC c b = 0)
    (hq : b.x1 * b.x4 + b.x2 * b.x5 = b.x6 ^ 2) (hher : herC b b ≠ 0) :
    ∃ u : GF49, u ≠ 0 ∧ NormShape (smulC u b) := by
  by_cases h1 : b.x1 = 0
  · by_cases h2 : b.x2 = 0
    · by_cases h4 : b.x4 = 0
      · by_cases h5 : b.x5 = 0
        · exfalso
          have h6 : b.x6 = 0 := by
            rw [h1, h2] at hq
            exact pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination -hq)
          exact hher (herC_eq_zero_of_zero hc3 hb3 hbc h1 h2 h4 h5 h6)
        · refine ⟨(b.x5)⁻¹, inv_ne_zero h5, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))⟩
          · simp [smulC, h1]
          · simp [smulC, h2]
          · simp [smulC, h4]
          · simp [smulC, h5]
      · refine ⟨(b.x4)⁻¹, inv_ne_zero h4, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩
        · simp [smulC, h1]
        · simp [smulC, h2]
        · simp [smulC, h4]
    · refine ⟨(b.x2)⁻¹, inv_ne_zero h2, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · simp [smulC, h1]
      · simp [smulC, h2]
  · exact ⟨(b.x1)⁻¹, inv_ne_zero h1, Or.inl (by simp [smulC, h1])⟩

theorem exists_mem_pts {cN : N7} (hc3 : cN.x3 = 1) {b : V7} (hb : isFFC b = true)
    (h0 : colC e0C b = true) (hc : colC cN.dec b = true) :
    ∃ (u : GF49) (p : N7), u ≠ 0 ∧ p ∈ q7Pts cN ∧ p.dec = smulC u b := by
  have hc3' : cN.dec.x3 = 1 := by
    simp only [N7.dec, hc3, gfDec_one]
  have hb' := hb
  have h0' := h0
  have hc' := hc
  simp only [isFFC, colC, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hb' h0' hc'
  have hb3 : b.x3 = 0 := by
    rw [← bfC_e0C]
    exact h0'.1
  have hq := quad_of_bfC hb3 hb'.1
  obtain ⟨u, hu, hn⟩ := exists_norm hc3' hb3 hc'.1 hq hb'.2
  have hb3' : (smulC u b).x3 = 0 := by
    simp [smulC, hb3]
  have hbc' : bfC cN.dec (smulC u b) = 0 := by
    rw [bfC_smulC_right, hc'.1, mul_zero]
  have hq' : (smulC u b).x1 * (smulC u b).x4 + (smulC u b).x2 * (smulC u b).x5 =
      (smulC u b).x6 ^ 2 := by
    simp only [smulC]
    linear_combination u ^ 2 * hq
  obtain ⟨p, hp, hpb⟩ := exists_cand hc3' hb3' hbc' hq' hn
  refine ⟨u, p, hu, ?_, hpb⟩
  unfold q7Pts
  rw [List.mem_filter]
  refine ⟨hp, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isFFN_iff, hpb, isFFC_smulC hu]
    exact hb
  · rw [colN_iff, hpb, e0N_dec, colC_smulC_right hu]
    exact h0
  · rw [colN_iff, hpb, colC_smulC_right hu]
    exact hc

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
