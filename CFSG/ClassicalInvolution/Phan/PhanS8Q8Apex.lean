module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q7Phi
import CFSG.ClassicalInvolution.Phan.PhanS8Q5Conic
import CFSG.ClassicalInvolution.Phan.PhanS8Q6HerNV
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] {M : Model K}

variable (M) in
@[expose] def forms5 (a b c d : Vec K) : Fin 5 → Vec K → Vec K → K :=
  ![her M, phi M a, phi M b, phi M c, phi M d]

theorem sesq_forms5 (a b c d : Vec K) : ∀ k, Sesq M (forms5 M a b c d k) := by
  intro k
  fin_cases k
  · exact sesq_her M
  · exact sesq_phi a
  · exact sesq_phi b
  · exact sesq_phi c
  · exact sesq_phi d

theorem card_bound (hq : 11 ≤ M.q) [Finite K] : 5 * (2 * M.q + 2) < Nat.card K := by
  rw [M.card_K]
  nlinarith

theorem card_bound_pencil (hq : 7 ≤ M.q) [Finite K] : 5 * (M.q + 1) < Nat.card K := by
  rw [M.card_K]
  nlinarith

theorem apex_of_forms5 {a b c d p : Vec K} (hp : bf M p p = 0)
    (ha : bf M a p = 0) (hb : bf M b p = 0) (hc : bf M c p = 0) (hd : bf M d p = 0)
    (h : ∀ k, forms5 M a b c d k p p ≠ 0) :
    IsFF M p ∧ Col M p a ∧ Col M p b ∧ Col M p c ∧ Col M p d := by
  have h0 : her M p p ≠ 0 := by simpa [forms5] using h 0
  have h1 : phi M a p p ≠ 0 := by simpa [forms5] using h 1
  have h2 : phi M b p p ≠ 0 := by simpa [forms5] using h 2
  have h3 : phi M c p p ≠ 0 := by simpa [forms5] using h 3
  have h4 : phi M d p p ≠ 0 := by simpa [forms5] using h 4
  rw [phi_self] at h1 h2 h3 h4
  exact ⟨⟨hp, h0⟩, ⟨by rw [bf_comm]; exact ha, h1⟩, ⟨by rw [bf_comm]; exact hb, h2⟩,
    ⟨by rw [bf_comm]; exact hc, h3⟩, ⟨by rw [bf_comm]; exact hd, h4⟩⟩

theorem apex_DD [Finite K] (hq : 7 ≤ M.q) {a b c d : Vec K} (ha : IsFF M a) (hb : IsFF M b)
    (hab : Col M a b) (hbc : Col M b c) (hda : Col M d a)
    (hac : bf M a c = 0) (hbd : bf M b d = 0) :
    ∃ p : Vec K, IsFF M p ∧ Col M p a ∧ Col M p b ∧ Col M p c ∧ Col M p d := by
  have hq3 : 3 ≤ M.q := by omega
  have w0 : ∃ i j : Fin 3, her M (cs a b 0 i) (cs a b 0 j) ≠ 0 := ⟨0, 0, by simpa [cs] using ha.2⟩
  have w1 : ∃ i j : Fin 3, phi M a (cs a b 0 i) (cs a b 0 j) ≠ 0 := by
    refine ⟨1, 1, ?_⟩
    show phi M a b b ≠ 0
    rw [phi_self, gram_comm]
    exact hab.2
  have w2 : ∃ i j : Fin 3, phi M b (cs a b 0 i) (cs a b 0 j) ≠ 0 := by
    refine ⟨0, 0, ?_⟩
    show phi M b a a ≠ 0
    rw [phi_self]
    exact hab.2
  have w3 : ∃ i j : Fin 3, phi M c (cs a b 0 i) (cs a b 0 j) ≠ 0 := by
    refine ⟨1, 1, ?_⟩
    show phi M c b b ≠ 0
    rw [phi_self]
    exact hbc.2
  have w4 : ∃ i j : Fin 3, phi M d (cs a b 0 i) (cs a b 0 j) ≠ 0 := by
    refine ⟨0, 0, ?_⟩
    show phi M d a a ≠ 0
    rw [phi_self, gram_comm]
    exact hda.2
  have hw : ∀ k, ∃ i j : Fin 3, forms5 M a b c d k (cs a b 0 i) (cs a b 0 j) ≠ 0 := by
    intro k
    fin_cases k
    exacts [w0, w1, w2, w3, w4]
  obtain ⟨μ, hμ⟩ := exists_good_pencil hq3 (sesq_forms5 a b c d) hw (card_bound_pencil hq)
  have hpt : conicPt a b 0 μ = a + μ • b := by simp [conicPt]
  have bab : bf M a b = 0 := hab.1
  have bba : bf M b a = 0 := by rw [bf_comm]; exact bab
  have bad : bf M a d = 0 := by rw [bf_comm]; exact hda.1
  have key : ∀ y, bf M a y = 0 → bf M b y = 0 → bf M (conicPt a b 0 μ) y = 0 := by
    intro y h1 h2
    rw [hpt, bf_add_left, bf_smul_left, h1, h2]
    ring
  have hpp : bf M (conicPt a b 0 μ) (conicPt a b 0 μ) = 0 := by
    rw [hpt]
    have : bf M (a + μ • b) (a + μ • b) =
        bf M a a + μ * bf M a b + μ * bf M b a + μ * (μ * bf M b b) := by
      rw [bf_add_left, bf_add_right, bf_add_right, bf_smul_left, bf_smul_left, bf_smul_right,
        bf_smul_right]
      ring
    rw [this, ha.1, hb.1, bab, bba]
    ring
  refine ⟨conicPt a b 0 μ, apex_of_forms5 (a := a) (b := b) (c := c) (d := d) hpp ?_ ?_ ?_ ?_ hμ⟩
  · rw [bf_comm]; exact key a ha.1 bba
  · rw [bf_comm]; exact key b bab hb.1
  · rw [bf_comm]; exact key c hac hbc.1
  · rw [bf_comm]; exact key d bad hbd

theorem apex_BB [Finite K] (hq : 11 ≤ M.q) {a b c d : Vec K} (ha : IsFF M a) (hb : IsFF M b)
    (hc : IsFF M c) (hd : IsFF M d) (hab : Col M a b) (hbc : Col M b c) (hcd : Col M c d)
    (hda : Col M d a) (hac : bf M a c ≠ 0) (hbd : bf M b d ≠ 0) :
    ∃ p : Vec K, IsFF M p ∧ Col M p a ∧ Col M p b ∧ Col M p c ∧ Col M p d := by
  have hq3 : 3 ≤ M.q := by omega
  have hx : GramInj M ![a, b, c, d] :=
    gramInj_quad ha.1 hb.1 hc.1 hd.1 hab.1 hbc.1 hcd.1 hda.1 hac hbd
  have bca : bf M c a ≠ 0 := by rw [bf_comm]; exact hac
  have bdb : bf M d b ≠ 0 := by rw [bf_comm]; exact hbd
  have bad : bf M a d = 0 := by rw [bf_comm]; exact hda.1
  have bba : bf M b a = 0 := by rw [bf_comm]; exact hab.1
  have bcb : bf M c b = 0 := by rw [bf_comm]; exact hbc.1
  have bdc : bf M d c = 0 := by rw [bf_comm]; exact hcd.1
  have hw : ∀ k, ∃ u ∈ orthSpan M (Set.range ![a, b, c, d]),
      ∃ u' ∈ orthSpan M (Set.range ![a, b, c, d]), forms5 M a b c d k u u' ≠ 0 := by
    intro k
    fin_cases k
    · obtain ⟨u, hu, u', hu', hne⟩ := exists_her_ne hx (i := 0) (j := 1) (by simpa using hab.2)
      exact ⟨u, hu, u', hu', by simpa [forms5] using hne⟩
    · obtain ⟨u, u', ⟨h1, h2, h3, h4⟩, ⟨h1', h2', h3', h4'⟩, hne⟩ :=
        exists_phi_ne (x := a) (n := b) (p := d) (o := c) ha.2 ha.1 hb.1 hd.1 hab.1 bad hbd hac
          hab.2
      exact ⟨u, mem_orthSpan_four.2 ⟨h1, h2, h4, h3⟩, u', mem_orthSpan_four.2 ⟨h1', h2', h4', h3'⟩,
        by simpa [forms5] using hne⟩
    · obtain ⟨u, u', ⟨h1, h2, h3, h4⟩, ⟨h1', h2', h3', h4'⟩, hne⟩ :=
        exists_phi_ne (x := b) (n := c) (p := a) (o := d) hb.2 hb.1 hc.1 ha.1 hbc.1 bba bca hbd
          hbc.2
      exact ⟨u, mem_orthSpan_four.2 ⟨h3, h1, h2, h4⟩, u', mem_orthSpan_four.2 ⟨h3', h1', h2', h4'⟩,
        by simpa [forms5] using hne⟩
    · obtain ⟨u, u', ⟨h1, h2, h3, h4⟩, ⟨h1', h2', h3', h4'⟩, hne⟩ :=
        exists_phi_ne (x := c) (n := d) (p := b) (o := a) hc.2 hc.1 hd.1 hb.1 hcd.1 bcb bdb bca
          hcd.2
      exact ⟨u, mem_orthSpan_four.2 ⟨h4, h3, h1, h2⟩, u', mem_orthSpan_four.2 ⟨h4', h3', h1', h2'⟩,
        by simpa [forms5] using hne⟩
    · obtain ⟨u, u', ⟨h1, h2, h3, h4⟩, ⟨h1', h2', h3', h4'⟩, hne⟩ :=
        exists_phi_ne (x := d) (n := a) (p := c) (o := b) hd.2 hd.1 ha.1 hc.1 hda.1 bdc hac bdb
          hda.2
      exact ⟨u, mem_orthSpan_four.2 ⟨h2, h4, h3, h1⟩, u', mem_orthSpan_four.2 ⟨h2', h4', h3', h1'⟩,
        by simpa [forms5] using hne⟩
  obtain ⟨p, hpZ, hpp, hpk⟩ :=
    exists_good_conic_pt hq3 hx (sesq_forms5 a b c d) hw (card_bound hq)
  rw [mem_orthSpan_four] at hpZ
  exact ⟨p, apex_of_forms5 (a := a) (b := b) (c := c) (d := d) hpp hpZ.1 hpZ.2.1 hpZ.2.2.1
    hpZ.2.2.2 hpk⟩

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
