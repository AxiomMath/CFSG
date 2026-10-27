module

import CFSG.ClassicalInvolution.Phan.PhanS8Q5Conic
import CFSG.ClassicalInvolution.Phan.PhanS8Q6HerNV
public import CFSG.ClassicalInvolution.Phan.PhanS8Q7Phi
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] {M : Model K}

variable (M) in
@[expose] def lin (b u u' : Vec K) : K := bf M b u * M.τ (bf M b u')

theorem sesq_lin (b : Vec K) : Sesq M (lin M b) := by
  refine ⟨fun u u' y => ?_, fun u y y' => ?_, fun c u y => ?_, fun c u y => ?_⟩
  · simp only [lin, bf_add_right]; ring
  · simp only [lin, bf_add_right, map_add]; ring
  · simp only [lin, bf_smul_right]; ring
  · simp only [lin, bf_smul_right, map_mul]; ring

theorem lin_self_ne {b u : Vec K} (h : bf M b u ≠ 0) : lin M b u u ≠ 0 :=
  mul_ne_zero h (tau_ne_zero M h)

theorem eq_smul_of_mem_span_flag {d a c b : Vec K} (hd0 : bf M d d = 0) (hda : bf M d a = 0)
    (hdc : bf M d c = 0) (haa : bf M a a = 0) (hac : bf M a c ≠ 0)
    (hdd : her M d d ≠ 0) (hbd : bf M b d = 0) (hba : bf M b a = 0) (hbc : bf M b c = 0)
    (hmem : b ∈ Submodule.span K (Set.range ![d, a, c, tauV M d])) :
    ∃ l : K, b = l • d := by
  obtain ⟨l, rfl⟩ := mem_span_range_four hmem
  rw [bf_sum_left] at hbd hba hbc
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at hbd hba hbc
  have e1 : bf M a d = 0 := by rw [bf_comm]; exact hda
  have e2 : bf M c d = 0 := by rw [bf_comm]; exact hdc
  have e3 : bf M (tauV M d) d = her M d d := by rw [bf_comm]; rfl
  have e4 : bf M c a = bf M a c := bf_comm M _ _
  rw [hd0, e1, e2, e3] at hbd
  have l3 : l 3 = 0 := by
    have : l 3 * her M d d = 0 := by linear_combination hbd
    exact (mul_eq_zero.1 this).resolve_right hdd
  rw [hda, haa, e4, l3] at hba
  have l2 : l 2 = 0 := by
    have : l 2 * bf M a c = 0 := by linear_combination hba
    exact (mul_eq_zero.1 this).resolve_right hac
  rw [hdc, l3, l2] at hbc
  have l1 : l 1 = 0 := by
    have : l 1 * bf M a c = 0 := by linear_combination hbc
    exact (mul_eq_zero.1 this).resolve_right hac
  refine ⟨l 0, ?_⟩
  simp [Fin.sum_univ_four, l1, l2, l3]

theorem exists_move [Finite K] (hq : 7 ≤ M.q) {a b c d : Vec K} (ha : IsFF M a)
    (hd : IsFF M d) (hab : Col M a b) (hbc : Col M b c) (hcd : Col M c d) (hda : Col M d a)
    (hc : IsFF M c) (hac : bf M a c ≠ 0) (hbd : bf M b d = 0) (hne : ∀ l : K, b ≠ l • d) :
    ∃ d' : Vec K, IsFF M d' ∧ Col M d' a ∧ Col M d' c ∧ Col M d' d ∧ bf M b d' ≠ 0 := by
  have hq3 : 3 ≤ M.q := by omega
  have bdc : bf M d c = 0 := by rw [bf_comm]; exact hcd.1
  have bba : bf M b a = 0 := by rw [bf_comm]; exact hab.1
  have bcb : bf M b c = 0 := hbc.1
  have hx : GramInj M ![d, a, c, tauV M d] :=
    gramInj_flag hd.1 hda.1 bdc ha.1 hc.1 hac (by simpa [her] using hd.2)
  let Φ : Fin 2 → Vec K → Vec K → K := ![her M, lin M b]
  have hΦ : ∀ k, Sesq M (Φ k) := by
    intro k
    fin_cases k
    · exact sesq_her M
    · exact sesq_lin b
  have hw : ∀ k, ∃ u ∈ orthSpan M (Set.range ![d, a, c, tauV M d]),
      ∃ u' ∈ orthSpan M (Set.range ![d, a, c, tauV M d]), Φ k u u' ≠ 0 := by
    intro k
    fin_cases k
    · obtain ⟨u, hu, u', hu', hne'⟩ := exists_her_ne hx (i := 0) (j := 1) (by simpa using hda.2)
      exact ⟨u, hu, u', hu', hne'⟩
    · have : ∃ z ∈ orthSpan M (Set.range ![d, a, c, tauV M d]), bf M b z ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨l, hl⟩ := eq_smul_of_mem_span_flag hd.1 hda.1 bdc ha.1 hac (by simpa using hd.2)
          hbd bba bcb (mem_span_of_forall_orth M hcon)
        exact hne l hl
      obtain ⟨z, hz, hbz⟩ := this
      exact ⟨z, hz, z, hz, lin_self_ne hbz⟩
  obtain ⟨t, htZ, htt, hΦt⟩ := exists_good_conic_pt hq3 hx hΦ hw (by
    rw [M.card_K]; nlinarith)
  have hht : her M t t ≠ 0 := by simpa [Φ] using hΦt 0
  have hbt : bf M b t ≠ 0 := by
    have : lin M b t t ≠ 0 := by simpa [Φ] using hΦt 1
    intro h0
    exact this (by simp [lin, h0])
  rw [mem_orthSpan_four] at htZ
  obtain ⟨htd, hta, htc, htd'⟩ := htZ
  have hpt : ∀ ν, conicPt d t 0 ν = d + ν • t := fun ν => by simp [conicPt]
  have hcd' : gram M d c ≠ 0 := by rw [gram_comm]; exact hcd.2
  let f : Fin 4 → K → K := fun k ν =>
    ![her M (conicPt d t 0 ν) (conicPt d t 0 ν), phi M a (conicPt d t 0 ν) (conicPt d t 0 ν),
      phi M c (conicPt d t 0 ν) (conicPt d t 0 ν), ν] k
  have hB : ∀ k, Nat.card {ν : K // f k ν = 0} ≤ M.q + 1 := by
    intro k
    fin_cases k
    · exact card_zeros_le_pencil hq3 (sesq_her M) (c₀ := d) (c₁ := t) ⟨0, 0, hd.2⟩
    · refine card_zeros_le_pencil hq3 (sesq_phi a) (c₀ := d) (c₁ := t) ⟨0, 0, ?_⟩
      show phi M a d d ≠ 0
      rw [phi_self]
      exact hda.2
    · refine card_zeros_le_pencil hq3 (sesq_phi c) (c₀ := d) (c₁ := t) ⟨0, 0, ?_⟩
      show phi M c d d ≠ 0
      rw [phi_self]
      exact hcd'
    · show Nat.card {ν : K // f 3 ν = 0} ≤ M.q + 1
      have : Nat.card {ν : K // f 3 ν = 0} ≤ 1 := by
        classical
        have := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        refine (Finset.card_le_one.2 fun x hx y hy => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        exact hx.trans hy.symm
      omega
  obtain ⟨ν, hν⟩ := exists_nonzero_all f hB (by rw [M.card_K]; nlinarith)
  have h0 : her M (d + ν • t) (d + ν • t) ≠ 0 := by simpa [f, hpt] using hν 0
  have h1 : phi M a (d + ν • t) (d + ν • t) ≠ 0 := by simpa [f, hpt] using hν 1
  have h2 : phi M c (d + ν • t) (d + ν • t) ≠ 0 := by simpa [f, hpt] using hν 2
  have h3 : ν ≠ 0 := by simpa [f] using hν 3
  rw [phi_self] at h1 h2
  have bta : bf M t a = 0 := by rw [bf_comm]; exact hta
  have btc : bf M t c = 0 := by rw [bf_comm]; exact htc
  have btd : bf M t d = 0 := by rw [bf_comm]; exact htd
  refine ⟨d + ν • t, ⟨?_, h0⟩, ⟨?_, h1⟩, ⟨?_, h2⟩, ⟨?_, ?_⟩, ?_⟩
  · have : bf M (d + ν • t) (d + ν • t) =
        bf M d d + ν * bf M d t + ν * bf M t d + ν * (ν * bf M t t) := by
      rw [bf_add_left, bf_add_right, bf_add_right, bf_smul_left, bf_smul_left, bf_smul_right,
        bf_smul_right]
      ring
    rw [this, hd.1, htd, btd, htt]
    ring
  · rw [bf_add_left, bf_smul_left, hda.1, bta]
    ring
  · rw [bf_add_left, bf_smul_left, bdc, btc]
    ring
  · rw [bf_add_left, bf_smul_left, hd.1, btd]
    ring
  · have hc1 : her M t d = 0 := by
      simp only [her]
      rw [bf_comm]
      exact htd'
    have hc2 : her M d t = 0 := by
      rw [her_conj_symm M t d, hc1, map_zero]
    have hself : her M (d + ν • t) (d + ν • t) =
        her M d d + ν * M.τ ν * her M t t := by
      rw [her_add_left, her_add_right, her_add_right, her_smul_left, her_smul_left,
        her_smul_right, her_smul_right, hc1, hc2]
      ring
    have hmix1 : her M (d + ν • t) d = her M d d := by
      rw [her_add_left, her_smul_left, hc1]
      ring
    have hmix2 : her M d (d + ν • t) = her M d d := by
      rw [her_add_right, her_smul_right, hc2]
      ring
    have hg : gram M (d + ν • t) d = her M d d * (ν * M.τ ν) * her M t t := by
      unfold gram
      rw [hmix1, hmix2, hself]
      ring
    rw [hg]
    exact mul_ne_zero (mul_ne_zero hd.2 (mul_ne_zero h3 (tau_ne_zero M h3))) hht
  · rw [bf_add_right, bf_smul_right, hbd]
    simp only [zero_add]
    exact mul_ne_zero h3 hbt

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
