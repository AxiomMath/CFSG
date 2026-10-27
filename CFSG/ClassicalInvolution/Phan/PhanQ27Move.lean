module

public import CFSG.ClassicalInvolution.Phan.PhanQ27Alg

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Frame

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

structure QFrame (a b c d : V8 K) : Prop where
  ha : InW0 a
  hb : InW0 b
  haf : ffK D a
  hbf : ffK D b
  hcf : ffK D c
  hdf : ffK D d
  hab : ColK D a b
  hbc : ColK D b c
  hcd : ColK D c d
  hda : ColK D d a

@[expose] def Resolved (a b c d : V8 K) : Prop :=
  (∃ e : V8 K, ffK D e ∧ ColK D e a ∧ ColK D e b ∧ ColK D e c ∧ ColK D e d) ∨
  (∃ c' : V8 K, ffK D c' ∧ ColK D c' b ∧ ColK D c' c ∧ ColK D c' d ∧
    ∃ e : V8 K, ffK D e ∧ ColK D e a ∧ ColK D e b ∧ ColK D e c' ∧ ColK D e d) ∨
  (∃ d' : V8 K, ffK D d' ∧ ColK D d' a ∧ ColK D d' c ∧ ColK D d' d ∧
    ∃ e : V8 K, ffK D e ∧ ColK D e a ∧ ColK D e b ∧ ColK D e c ∧ ColK D e d')

variable {D}

theorem QFrame.mirror {a b c d : V8 K} (Fr : QFrame D a b c d) : QFrame D b a d c :=
  ⟨Fr.hb, Fr.ha, Fr.hbf, Fr.haf, Fr.hdf, Fr.hcf, Fr.hab.symm D, Fr.hda.symm D, Fr.hcd.symm D,
    Fr.hbc.symm D⟩

theorem Resolved.of_mirror {a b c d : V8 K} (h : Resolved D b a d c) : Resolved D a b c d := by
  rcases h with ⟨e, hf, h1, h2, h3, h4⟩ | ⟨c', hf, h1, h2, h3, e, hef, h5, h6, h7, h8⟩ |
    ⟨d', hf, h1, h2, h3, e, hef, h5, h6, h7, h8⟩
  · exact Or.inl ⟨e, hf, h2, h1, h4, h3⟩
  · exact Or.inr (Or.inr ⟨c', hf, h1, h3, h2, e, hef, h6, h5, h8, h7⟩)
  · exact Or.inr (Or.inl ⟨d', hf, h1, h3, h2, e, hef, h6, h5, h8, h7⟩)

end Frame

section Move

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
theorem gram_self_zero (v : V8 K) : gram D v v = 0 := by
  unfold gram
  ring

omit [Fintype K] [DecidableEq K] in
theorem not_colK_self (v : V8 K) : ¬ ColK D v v := fun h => h.2 (gram_self_zero D v)

theorem resolved_of_move (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d t : V8 K} (Fr : QFrame D a b c d)
    (hQt : Q8 t = 0) (hct : B8 c t = 0) (htb : B8 t b = 0) (htd : B8 t d = 0)
    (hG : gram D c t ≠ 0) (hw : ∀ μ : K, μ ≠ 0 → ∃ i j, wedge (c + μ • t) d i j ≠ 0) :
    Resolved D a b c d := by
  have hcc : B8 c c = 0 := B8_zero_self Fr.hcf.1
  have hcb : B8 c b = 0 := by
    rw [B8_comm]
    exact Fr.hbc.1
  have htc : B8 t c = 0 := by
    rw [B8_comm]
    exact hct
  have hm : (3 + 1) * (Nat.card F + 1) < Nat.card F ^ 2 := hq5
  obtain ⟨μ, hff, hcol⟩ := exists_good_pencil D hq2 (m := 3) hm Fr.hcf.1 hQt hct hG ![b, d, c]
    (fun i => by fin_cases i <;> simp [Fr.hbf, Fr.hdf, Fr.hcf])
    (fun i => by fin_cases i <;> simp [hcb, Fr.hcd.1, hcc])
    (fun i => by fin_cases i <;> simp [htb, htd, htc])
  have hcb' : ColK D (c + μ • t) b := hcol 0
  have hcd' : ColK D (c + μ • t) d := hcol 1
  have hcc' : ColK D (c + μ • t) c := hcol 2
  have hμ : μ ≠ 0 := by
    rintro rfl
    apply not_colK_self D c
    simpa using hcc'
  obtain ⟨e, hef, he1, he2, he3, he4⟩ := exists_common_nbr_of_wedge (D := D) h2 hq2 hq5 Fr.ha
    Fr.hb Fr.haf Fr.hbf hff Fr.hdf Fr.hab (hcb'.symm D) Fr.hda (hw μ hμ)
  exact Or.inr (Or.inl ⟨c + μ • t, hff, hcb', hcc', hcd', e, hef, he1, he2, he3, he4⟩)

omit [Fintype K] [DecidableEq K] in
theorem gram_c_add {b c T : V8 K} (hbT : her D b T = 0) (hTb : her D T b = 0)
    (hcT : her D c T = 0) (hTT : her D T T = 0) (hcb : gram D c b ≠ 0) :
    gram D c (b + T) ≠ 0 := by
  have hTc : her D T c = 0 := by
    rw [her_conj_symm D c T, hcT, map_zero]
  have e : gram D c (b + T) = gram D c b := by
    unfold gram
    simp only [her_add_left, her_add_right, hbT, hTb, hcT, hTc, hTT, add_zero]
  rw [e]
  exact hcb

omit [Fintype K] [DecidableEq K] in
theorem gram_c_T {c T : V8 K} (hTT : her D T T = 0) (hcT : her D c T ≠ 0) :
    gram D c T ≠ 0 := by
  have e : gram D c T = -(her D c T * D.τ (her D c T)) := by
    unfold gram
    rw [hTT, her_conj_symm D c T]
    ring
  rw [e]
  exact neg_ne_zero.2 (mul_ne_zero hcT fun h => hcT (by simpa [D.tau_tau] using congrArg D.τ h))

theorem resolved_of_bT (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d T : V8 K} (Fr : QFrame D a b c d)
    (hT : InW2 T) (hQT : Q8 T = 0) (hhT : her D T T = 0) (hcT : B8 c T = 0)
    (hdT : B8 T d = -B8 b d) (hcT' : her D c T = 0)
    (hw : ∀ μ : K, μ ≠ 0 → ∃ i j, wedge (c + μ • (b + T)) d i j ≠ 0) :
    Resolved D a b c d := by
  have hbT : B8 b T = 0 := B8_eq_zero_of_support Fr.hb hT
  have hTb : B8 T b = 0 := by
    rw [B8_comm]
    exact hbT
  have hQ : Q8 (b + T) = 0 := by
    rw [Q8_add', Fr.hbf.1, hQT, hbT]
    ring
  have hct : B8 c (b + T) = 0 := by
    rw [B8_add_right, hcT]
    have hcb : B8 c b = 0 := by
      rw [B8_comm]
      exact Fr.hbc.1
    rw [hcb]
    ring
  have htb : B8 (b + T) b = 0 := by
    rw [B8_add_left, hTb, B8_zero_self Fr.hbf.1]
    ring
  have htd : B8 (b + T) d = 0 := by
    rw [B8_add_left, hdT]
    ring
  have hG : gram D c (b + T) ≠ 0 :=
    gram_c_add D (her_zero_of_W0_W2 D Fr.hb hT) (her_zero_of_W2_W0 D hT Fr.hb) hcT' hhT
      ((Fr.hbc.symm D).2)
  exact resolved_of_move D h2 hq2 hq5 Fr hQ hct htb htd hG hw

theorem resolved_of_T (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d T : V8 K} (Fr : QFrame D a b c d)
    (hT : InW2 T) (hQT : Q8 T = 0) (hhT : her D T T = 0) (hcT : B8 c T = 0)
    (hdT : B8 T d = 0) (hcT' : her D c T ≠ 0)
    (hw : ∀ μ : K, μ ≠ 0 → ∃ i j, wedge (c + μ • T) d i j ≠ 0) : Resolved D a b c d := by
  have hTb : B8 T b = 0 := B8_zero_of_W2_W0 hT Fr.hb
  exact resolved_of_move D h2 hq2 hq5 Fr hQT hcT hTb hdT (gram_c_T D hhT hcT') hw

end Move

end CFSG.ClassicalInvolution.PhanQ
