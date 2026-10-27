module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import CFSG.ClassicalInvolution.Phan.PhanS8Q1Graph
import CFSG.ClassicalInvolution.Phan.PhanS8Q9Move
import CFSG.ClassicalInvolution.Phan.PhanS8Q8Apex

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S

variable {K : Type} [Field K] [Finite K] {M : Model K}

omit [Finite K] in
theorem adj_mk_right (X : FFPt M) {p : Vec K} (hp : IsFF M p) :
    (ffGraph M).Adj X (FFPt.mk M hp) ↔ Col M X.1.rep p := by
  obtain ⟨c, hc, hcp⟩ := FFPt.mk_rep M hp
  show Col M X.1.rep (FFPt.mk M hp).1.rep ↔ _
  rw [hcp]
  simpa using (col_smul M (c := 1) (d := c) one_ne_zero hc (x := X.1.rep) (y := p))

omit [Finite K] in
theorem col_mk_right {p v : Vec K} (hv : IsFF M v) :
    Col M p (FFPt.mk M hv).1.rep ↔ Col M p v := by
  obtain ⟨c, hc, hcp⟩ := FFPt.mk_rep M hv
  rw [hcp]
  simpa using (col_smul M (c := 1) (d := c) one_ne_zero hc (x := p) (y := v))

omit [Finite K] in
theorem qn_of_apex_vec {A B C D : FFPt M} {p : Vec K} (hp : IsFF M p)
    (hpa : Col M p A.1.rep) (hpb : Col M p B.1.rep) (hpc : Col M p C.1.rep)
    (hpd : Col M p D.1.rep) : QN (ffGraph M) A B C D := by
  refine QN.of_apex (z := FFPt.mk M hp) ?_ ?_ ?_ ?_
  · rw [adj_mk_right]; exact hpa.symm M
  · rw [adj_mk_right]; exact hpb.symm M
  · rw [adj_mk_right]; exact hpc.symm M
  · rw [adj_mk_right]; exact hpd.symm M

@[expose] def BBQuad (M : Model K) : Prop :=
  ∀ A B C D : FFPt M, bf M A.1.rep C.1.rep ≠ 0 → bf M B.1.rep D.1.rep ≠ 0 →
    QN (ffGraph M) A B C D

theorem bbQuad_of_apex (hq : 11 ≤ M.q) : BBQuad M := by
  intro A B C D hac hbd hab hbc hcd hda
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := apex_BB hq A.2 B.2 C.2 D.2 hab hbc hcd hda hac hbd
  exact (qn_of_apex_vec hp h1 h2 h3 h4) hab hbc hcd hda

@[expose] def HardWay (M : Model K) : Prop :=
  ∀ a b c d : Vec K, IsFF M a → IsFF M b → IsFF M c → IsFF M d →
    Col M a b → Col M b c → Col M c d → Col M d a → bf M a c ≠ 0 → bf M b d ≠ 0 →
    (∃ p : Vec K, IsFF M p ∧ Col M p a ∧ Col M p b ∧ Col M p c ∧ Col M p d) ∨
      ∃ d' : Vec K, IsFF M d' ∧ Col M d' a ∧ Col M d' c ∧ Col M d' d ∧ bf M b d' ≠ 0 ∧
        ∃ p : Vec K, IsFF M p ∧ Col M p a ∧ Col M p b ∧ Col M p c ∧ Col M p d'

theorem hardWay_of_apex (hq : 11 ≤ M.q) : HardWay M :=
  fun _ _ _ _ ha hb hc hd hab hbc hcd hda hac hbd =>
    Or.inl (apex_BB hq ha hb hc hd hab hbc hcd hda hac hbd)

omit [Finite K] in
theorem bbQuad_of_hardWay (h : HardWay M) : BBQuad M := by
  intro A B C D hac hbd hab hbc hcd hda
  rcases h A.1.rep B.1.rep C.1.rep D.1.rep A.2 B.2 C.2 D.2 hab hbc hcd hda hac hbd with
    ⟨p, hp, h1, h2, h3, h4⟩ | ⟨d', hd', h1, h2, h3, _, p, hp, g1, g2, g3, g4⟩
  · exact (qn_of_apex_vec hp h1 h2 h3 h4) hab hbc hcd hda
  · have hAD' : (ffGraph M).Adj A (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h1.symm M
    have hCD' : (ffGraph M).Adj C (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h2.symm M
    have hDD' : (ffGraph M).Adj D (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h3.symm M
    have hq' : QN (ffGraph M) A B C (FFPt.mk M hd') :=
      qn_of_apex_vec hp g1 g2 g3 ((col_mk_right hd').2 g4)
    exact QN.move_fourth hAD' hCD' hDD' hq' hab hbc hcd hda

theorem qn_DD (hq : 7 ≤ M.q) {A B C D : FFPt M} (hab : (ffGraph M).Adj A B)
    (hbc : (ffGraph M).Adj B C) (hda : (ffGraph M).Adj D A)
    (hac : bf M A.1.rep C.1.rep = 0) (hbd : bf M B.1.rep D.1.rep = 0) :
    QN (ffGraph M) A B C D := by
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := apex_DD hq A.2 B.2 hab hbc hda hac hbd
  exact qn_of_apex_vec hp h1 h2 h3 h4

theorem qn_BD (hq : 7 ≤ M.q) (hBB : BBQuad M) {A B C D : FFPt M} (hab : (ffGraph M).Adj A B)
    (hbc : (ffGraph M).Adj B C) (hcd : (ffGraph M).Adj C D) (hda : (ffGraph M).Adj D A)
    (hac : bf M A.1.rep C.1.rep ≠ 0) (hbd : bf M B.1.rep D.1.rep = 0) :
    QN (ffGraph M) A B C D := by
  by_cases hBD : B = D
  · subst hBD
    exact QN.of_eq_diag
  · have hne : ∀ l : K, B.1.rep ≠ l • D.1.rep := by
      intro l hl
      apply hBD
      have hl0 : l ≠ 0 := by
        rintro rfl
        exact B.1.rep_nonzero (by simpa using hl)
      apply Subtype.ext
      rw [← Projectivization.mk_rep B.1, ← Projectivization.mk_rep D.1]
      exact (Projectivization.mk_eq_mk_iff' K _ _ B.1.rep_nonzero D.1.rep_nonzero).2
        ⟨l, hl.symm⟩
    obtain ⟨d', hd', h1, h2, h3, h4⟩ :=
      exists_move hq A.2 D.2 hab hbc hcd hda C.2 hac hbd hne
    have hAD' : (ffGraph M).Adj A (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h1.symm M
    have hCD' : (ffGraph M).Adj C (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h2.symm M
    have hDD' : (ffGraph M).Adj D (FFPt.mk M hd') := by
      rw [adj_mk_right]; exact h3.symm M
    have hq' : QN (ffGraph M) A B C (FFPt.mk M hd') := by
      refine hBB A B C (FFPt.mk M hd') hac ?_
      obtain ⟨c, hc, hcp⟩ := FFPt.mk_rep M hd'
      show bf M B.1.rep (FFPt.mk M hd').1.rep ≠ 0
      rw [hcp, bf_smul_right]
      exact mul_ne_zero hc h4
    exact QN.move_fourth hAD' hCD' hDD' hq'

theorem qn_all (hq : 7 ≤ M.q) (hBB : BBQuad M) (A B C D : FFPt M) : QN (ffGraph M) A B C D := by
  intro hab hbc hcd hda
  by_cases h1 : bf M A.1.rep C.1.rep = 0
  · by_cases h2 : bf M B.1.rep D.1.rep = 0
    · exact qn_DD hq hab hbc hda h1 h2 hab hbc hcd hda
    · have hca : bf M C.1.rep A.1.rep = 0 := by rw [bf_comm]; exact h1
      have := qn_BD hq hBB hbc hcd hda hab h2 hca
      exact this.rotate.rotate.rotate hab hbc hcd hda
  · by_cases h2 : bf M B.1.rep D.1.rep = 0
    · exact qn_BD hq hBB hab hbc hcd hda h1 h2 hab hbc hcd hda
    · exact hBB A B C D h1 h2 hab hbc hcd hda

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

theorem quadNull_of_BB {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q)
    (h : BBQuad M) : QuadNullStd M :=
  quadNull_iff.2 (qn_all hq h)

theorem quadNull_of_model {K : Type} [Field K] [Finite K] (M : Model K) (hq : 11 ≤ M.q) :
    QuadNullStd M :=
  quadNull_of_BB M (by omega) (bbQuad_of_apex hq)

theorem quadNull_of_hardWay {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q)
    (h : HardWay M) : QuadNullStd M :=
  quadNull_of_BB M hq (bbQuad_of_hardWay h)

theorem quadNull_of_model_mod4 {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q)
    (h4 : M.q % 4 = 3) (h7 : M.q = 7 → HardWay M) : QuadNullStd M := by
  by_cases h : M.q = 7
  · exact quadNull_of_hardWay M hq (h7 h)
  · exact quadNull_of_model M (by omega)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
