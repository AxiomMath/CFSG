module

public import CFSG.ClassicalInvolution.Phan.PhanS7P2Orth
public import CFSG.ClassicalInvolution.Phan.PhanS7P3Core

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.P

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] {M : Model K}

theorem cpr_ne_or {a c d : Vec K} (hd : IsFF M d) (hcd : Col M c d)
    (h : ¬ (bf M c a = 0 ∧ bf M d a = 0)) :
    bf M (cpr M c d) a ≠ 0 ∨ bf M (cpr M d c) a ≠ 0 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [bf_cpr_left] at h1 h2
  have key : gram M c d * bf M d a = 0 := by
    simp only [gram]
    linear_combination (her M d d) * h1 + (her M d c) * h2
  have hda : bf M d a = 0 := (mul_eq_zero.1 key).resolve_left hcd.2
  have hca : bf M c a = 0 := by
    rw [hda] at h2
    have : her M d d * bf M c a = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_left hd.2
  exact h ⟨hca, hda⟩

theorem exists_apex [Finite K] (hq : 7 ≤ M.q) {a c d : Vec K} (ha : IsFF M a) (hc : IsFF M c)
    (hd : IsFF M d) (hcd : Col M c d) :
    ∃ f : Vec K, IsFF M f ∧ Col M f c ∧ Col M f d ∧ Col M f a := by
  by_cases h : bf M c a = 0 ∧ bf M d a = 0
  · exact exists_apex_orth (by omega) ha hc hd hcd h.1 h.2
  · rcases cpr_ne_or hd hcd h with hA | hA
    · exact exists_apex_cprime hq ha hc hd hcd hA
    · obtain ⟨f, hf, h1, h2, h3⟩ := exists_apex_cprime hq ha hd hc (Col.symm M hcd) hA
      exact ⟨f, hf, h2, h1, h3⟩

theorem pentApex_of_model {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q) :
    PentApex M := by
  intro a c d hcd
  obtain ⟨va, hva, rfl⟩ := FFPt.exists_vec M a
  obtain ⟨vc, hvc, rfl⟩ := FFPt.exists_vec M c
  obtain ⟨vd, hvd, rfl⟩ := FFPt.exists_vec M d
  have hcol : Col M vc vd := (ffGraph_adj_mk M hvc hvd).1 hcd
  obtain ⟨f, hf, h1, h2, h3⟩ := exists_apex hq hva hvc hvd hcol
  exact ⟨FFPt.mk M hf, (ffGraph_adj_mk M hf hvc).2 h1, (ffGraph_adj_mk M hf hvd).2 h2,
    (ffGraph_adj_mk M hva hf).2 (Col.symm M h3)⟩

theorem pentNullStd_of_model {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q)
    (hQ : QuadNullStd M) : PentNullStd M :=
  pentNullStd_of_pentApex M hQ (pentApex_of_model M hq)

end CFSG.ClassicalInvolution.PhanB3.S.Std.P
