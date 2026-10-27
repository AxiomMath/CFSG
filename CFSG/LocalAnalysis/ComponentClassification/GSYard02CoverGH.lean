module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Cover
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.GH74.E2.FactsK
public import CFSG.GH74.GLS.Stage1.Main.Gen4NoL34Proof

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint Assembly.LowTwoRank

@[expose] def CoverLeafL4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 1 → LieModel (Q ⧸ center Q) .PSL 4 p f → SylowFourJoined Q

@[expose] def CoverLeafU4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 7 → LieModel (Q ⧸ center Q) .PSU 4 p f → SylowFourJoined Q

@[expose] def CoverLeafSz8 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → LieModel (Q ⧸ center Q) .twistedB2 0 2 3 →
    SylowFourJoined Q

@[expose] def CoverLeafAlt : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ n : ℕ, 8 ≤ n → n ≤ 11 →
    Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin n)) → SylowFourJoined Q

@[expose] def CoverLeafM12 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → NativeSporadic.IsSporadic (Q ⧸ center Q) .M12 →
    SylowFourJoined Q

@[expose] def CoverLeafL4For (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 1 → LieModel (Q ⧸ center Q) .PSL 4 p f → P Q

@[expose] def CoverLeafU4For (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 7 → LieModel (Q ⧸ center Q) .PSU 4 p f → P Q

@[expose] def CoverLeafSz8For (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → LieModel (Q ⧸ center Q) .twistedB2 0 2 3 → P Q

@[expose] def CoverLeafAltFor (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → ∀ n : ℕ, 8 ≤ n → n ≤ 11 →
    Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin n)) → P Q

@[expose] def CoverLeafM12For (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → NativeSporadic.IsSporadic (Q ⧸ center Q) .M12 →
    P Q

section SympRank

open Matrix

variable {F : Type} [Field F]

private abbrev sympJ (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 0 1 (-1) 0

private def sympForm (x y : Fin 2 ⊕ Fin 2 → F) : F := dotProduct x (sympJ F *ᵥ y)

private lemma sympJ_mul_self : sympJ F * sympJ F = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sympJ, fromBlocks_multiply, Matrix.one_apply, Matrix.neg_apply]

private lemma sympForm_neg_comm (x y : Fin 2 ⊕ Fin 2 → F) : sympForm x y = -sympForm y x := by
  simp [sympForm, sympJ, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private lemma sympForm_self (h2 : (2 : F) ≠ 0) (x : Fin 2 ⊕ Fin 2 → F) : sympForm x x = 0 := by
  have h := sympForm_neg_comm x x
  have h' : (2 : F) * sympForm x x = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left h2

private lemma sympForm_add_left (a b w : Fin 2 ⊕ Fin 2 → F) :
    sympForm (a + b) w = sympForm a w + sympForm b w := by
  simp [sympForm, add_dotProduct]

private lemma sympForm_add_right (a b w : Fin 2 ⊕ Fin 2 → F) :
    sympForm w (a + b) = sympForm w a + sympForm w b := by
  simp [sympForm, mulVec_add, dotProduct_add]

private lemma sympForm_smul_left (c : F) (a w : Fin 2 ⊕ Fin 2 → F) :
    sympForm (c • a) w = c * sympForm a w := by
  simp [sympForm, smul_dotProduct, smul_eq_mul]

private lemma sympForm_smul_right (c : F) (w a : Fin 2 ⊕ Fin 2 → F) :
    sympForm w (c • a) = c * sympForm w a := by
  simp [sympForm, mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma sympForm_smul (c d : F) (x y : Fin 2 ⊕ Fin 2 → F) :
    sympForm (c • x) (d • y) = c * d * sympForm x y := by
  rw [sympForm_smul_left, sympForm_smul_right]
  ring

private lemma eq_zero_of_sympForm (x : Fin 2 ⊕ Fin 2 → F) (h : ∀ y, sympForm x y = 0) : x = 0 := by
  have hw : ∀ w : Fin 2 ⊕ Fin 2 → F, dotProduct x w = 0 := by
    intro w
    have h1 := h (sympJ F *ᵥ w)
    unfold sympForm at h1
    rw [mulVec_mulVec, sympJ_mul_self] at h1
    simpa [neg_mulVec, one_mulVec, dotProduct_neg] using h1
  funext i
  have h2 := hw (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using h2

private lemma sympForm_iso {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hM : Mᵀ * sympJ F * M = sympJ F)
    (x y : Fin 2 ⊕ Fin 2 → F) : sympForm (M *ᵥ x) (M *ᵥ y) = sympForm x y := by
  have key : ∀ w : Fin 2 ⊕ Fin 2 → F, dotProduct (M *ᵥ x) w = dotProduct x (Mᵀ *ᵥ w) := by
    intro w
    rw [mulVec_transpose, dotProduct_comm (M *ᵥ x) w, dotProduct_mulVec]
    exact dotProduct_comm _ _
  unfold sympForm
  rw [key, mulVec_mulVec, mulVec_mulVec, hM]

private lemma sympForm_cross {t g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (h2 : (2 : F) ≠ 0)
    (ht : tᵀ * sympJ F * t = sympJ F) (hg : gᵀ * sympJ F * g = sympJ F) {a b a' b' : F}
    {x y : Fin 2 ⊕ Fin 2 → F} (hx : t *ᵥ x = a • x ∧ g *ᵥ x = b • x)
    (hy : t *ᵥ y = a' • y ∧ g *ᵥ y = b' • y) (hne : a * a' = -1 ∨ b * b' = -1) :
    sympForm x y = 0 := by
  have e1 := sympForm_iso ht x y
  have e2 := sympForm_iso hg x y
  rw [hx.1, hy.1, sympForm_smul] at e1
  rw [hx.2, hy.2, sympForm_smul] at e2
  rcases hne with h | h
  · rw [h] at e1
    have h' : (2 : F) * sympForm x y = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp h').resolve_left h2
  · rw [h] at e2
    have h' : (2 : F) * sympForm x y = 0 := by linear_combination -e2
    exact (mul_eq_zero.mp h').resolve_left h2

end SympRank

section SympCells

open Matrix

variable {F : Type} [Field F]

private abbrev M4 (F : Type) [Field F] : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private def cellP (t g : M4 F) (a b : F) : M4 F := (1 + a • t) * (1 + b • g)

private def JointEig (t g : M4 F) (a b : F) (x : Fin 2 ⊕ Fin 2 → F) : Prop :=
  t *ᵥ x = a • x ∧ g *ᵥ x = b • x

private lemma four_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  intro h
  have h22 : (2 : F) * 2 = 0 := by linear_combination h
  exact (mul_eq_zero.mp h22).elim h2 h2

private lemma mul_self_of_pm {a : F} (h : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases h with rfl | rfl <;> ring

private lemma sympForm_zero_left (w : Fin 2 ⊕ Fin 2 → F) : sympForm 0 w = 0 := by
  simp [sympForm]

private lemma t_mul_cellP (t g : M4 F) (htt : t * t = 1) {a b : F} (ha : a * a = 1) :
    t * cellP t g a b = a • cellP t g a b := by
  have h1 : t * (1 + a • t) = a • (1 + a • t) := by
    calc t * (1 + a • t) = t + a • (t * t) := by rw [mul_add, mul_one, mul_smul_comm]
      _ = t + a • (1 : M4 F) := by rw [htt]
      _ = a • (1 : M4 F) + t := add_comm _ _
      _ = a • (1 : M4 F) + (a * a) • t := by rw [ha, one_smul]
      _ = a • (1 : M4 F) + a • (a • t) := by rw [smul_smul]
      _ = a • (1 + a • t) := by rw [smul_add]
  unfold cellP
  rw [← mul_assoc, h1, smul_mul_assoc]

private lemma g_mul_cellP (t g : M4 F) (hcomm : g * t = t * g) (hgg : g * g = 1) {a b : F}
    (hb : b * b = 1) : g * cellP t g a b = b • cellP t g a b := by
  have h2 : g * (1 + a • t) = (1 + a • t) * g := by
    rw [mul_add, mul_one, mul_smul_comm, add_mul, one_mul, smul_mul_assoc, hcomm]
  have h3 : g * (1 + b • g) = b • (1 + b • g) := by
    calc g * (1 + b • g) = g + b • (g * g) := by rw [mul_add, mul_one, mul_smul_comm]
      _ = g + b • (1 : M4 F) := by rw [hgg]
      _ = b • (1 : M4 F) + g := add_comm _ _
      _ = b • (1 : M4 F) + (b * b) • g := by rw [hb, one_smul]
      _ = b • (1 : M4 F) + b • (b • g) := by rw [smul_smul]
      _ = b • (1 + b • g) := by rw [smul_add]
  unfold cellP
  rw [← mul_assoc, h2, mul_assoc, h3, mul_smul_comm]

private lemma cellP_mem (t g : M4 F) (htt : t * t = 1) (hgg : g * g = 1) (hcomm : g * t = t * g)
    {a b : F} (ha : a * a = 1) (hb : b * b = 1) (z : Fin 2 ⊕ Fin 2 → F) :
    JointEig t g a b (cellP t g a b *ᵥ z) := by
  constructor
  · rw [mulVec_mulVec, t_mul_cellP t g htt ha, smul_mulVec]
  · rw [mulVec_mulVec, g_mul_cellP t g hcomm hgg hb, smul_mulVec]

private lemma sum_cellP (t g : M4 F) :
    cellP t g 1 1 + cellP t g 1 (-1) + cellP t g (-1) 1 + cellP t g (-1) (-1) =
      (4 : F) • (1 : M4 F) := by
  have h4 : (4 : F) • (1 : M4 F) = 1 + 1 + 1 + 1 := by module
  rw [h4]
  unfold cellP
  simp only [one_smul, neg_one_smul]
  noncomm_ring

private lemma sum_cellP_mulVec (t g : M4 F) (z : Fin 2 ⊕ Fin 2 → F) :
    cellP t g 1 1 *ᵥ z + cellP t g 1 (-1) *ᵥ z + cellP t g (-1) 1 *ᵥ z +
      cellP t g (-1) (-1) *ᵥ z = (4 : F) • z := by
  rw [← add_mulVec, ← add_mulVec, ← add_mulVec, sum_cellP, smul_mulVec, one_mulVec]

private lemma exists_mulVec_ne_zero {M : M4 F} (hM : M ≠ 0) : ∃ z : Fin 2 ⊕ Fin 2 → F, M *ᵥ z ≠ 0 := by
  by_contra h
  push_neg at h
  apply hM
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec, dotProduct, Pi.single_apply] using this

private lemma six_false {u1 v1 u2 v2 u3 v3 : Fin 2 ⊕ Fin 2 → F} (h2 : (2 : F) ≠ 0)
    (p1 : sympForm u1 v1 ≠ 0) (p2 : sympForm u2 v2 ≠ 0) (p3 : sympForm u3 v3 ≠ 0)
    (c12 : sympForm u1 u2 = 0) (c12' : sympForm u1 v2 = 0) (c12'' : sympForm v1 u2 = 0)
    (c12''' : sympForm v1 v2 = 0)
    (c13 : sympForm u1 u3 = 0) (c13' : sympForm u1 v3 = 0) (c13'' : sympForm v1 u3 = 0)
    (c13''' : sympForm v1 v3 = 0)
    (c23 : sympForm u2 u3 = 0) (c23' : sympForm u2 v3 = 0) (c23'' : sympForm v2 u3 = 0)
    (c23''' : sympForm v2 v3 = 0) : False := by
  have rev : ∀ {a b : Fin 2 ⊕ Fin 2 → F}, sympForm a b = 0 → sympForm b a = 0 := by
    intro a b h
    rw [sympForm_neg_comm, h, neg_zero]
  have p1' : sympForm v1 u1 ≠ 0 := fun h => p1 (rev h)
  have p2' : sympForm v2 u2 ≠ 0 := fun h => p2 (rev h)
  have p3' : sympForm v3 u3 ≠ 0 := fun h => p3 (rev h)
  have hli : LinearIndependent F ![u1, v1, u2, v2, u3, v3] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    have E : ∀ w : Fin 2 ⊕ Fin 2 → F, f 0 * sympForm u1 w + f 1 * sympForm v1 w +
        f 2 * sympForm u2 w + f 3 * sympForm v2 w + f 4 * sympForm u3 w +
        f 5 * sympForm v3 w = 0 := by
      intro w
      have hw := congrArg (fun y => sympForm y w) hf
      simpa [Fin.sum_univ_six, sympForm_add_left, sympForm_smul_left, sympForm_zero_left] using hw
    have g0 : f 0 = 0 := by
      have e := E v1
      simp only [sympForm_self h2, rev c12'', rev c12''', rev c13'', rev c13''', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p1
    have g1 : f 1 = 0 := by
      have e := E u1
      simp only [sympForm_self h2, rev c12, rev c12', rev c13, rev c13', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p1'
    have g2 : f 2 = 0 := by
      have e := E v2
      simp only [sympForm_self h2, c12', c12''', rev c23'', rev c23''', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p2
    have g3 : f 3 = 0 := by
      have e := E u2
      simp only [sympForm_self h2, c12, c12'', rev c23, rev c23', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p2'
    have g4 : f 4 = 0 := by
      have e := E v3
      simp only [sympForm_self h2, c13', c13''', c23', c23''', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p3
    have g5 : f 5 = 0 := by
      have e := E u3
      simp only [sympForm_self h2, c13, c13'', c23, c23'', mul_zero,
        add_zero, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_right p3'
    intro i
    fin_cases i <;> simp [g0, g1, g2, g3, g4, g5]
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  simp [Fintype.card_sum] at hcard

end SympCells

section SympK1

open Matrix

variable {F : Type} [Field F]

private lemma pair_core {x z y1 y2 y3 y4 : Fin 2 ⊕ Fin 2 → F} (h4 : (4 : F) ≠ 0)
    (hs : sympForm x z ≠ 0) (hdec : (4 : F) • z = y1 + y2 + y3 + y4)
    (h2 : sympForm x y2 = 0) (h3 : sympForm x y3 = 0) (h4' : sympForm x y4 = 0) :
    sympForm x y1 ≠ 0 := by
  intro h1
  apply hs
  have e := congrArg (sympForm x) hdec
  simp only [sympForm_smul_right, sympForm_add_right, h1, h2, h3, h4', add_zero, zero_add] at e
  exact (mul_eq_zero.mp e).resolve_left h4

private lemma exists_pair (t g : M4 F) (h2 : (2 : F) ≠ 0) (ht : tᵀ * sympJ F * t = sympJ F)
    (hg : gᵀ * sympJ F * g = sympJ F) (htt : t * t = 1) (hgg : g * g = 1) (hcomm : g * t = t * g)
    {a b : F} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) {x : Fin 2 ⊕ Fin 2 → F}
    (hx : JointEig t g a b x) (hx0 : x ≠ 0) :
    ∃ y, JointEig t g a b y ∧ sympForm x y ≠ 0 := by
  have h4 := four_ne_zero h2
  obtain ⟨z, hz⟩ : ∃ z, sympForm x z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (eq_zero_of_sympForm x hcon)
  have hdec11 : (4 : F) • z = cellP t g 1 1 *ᵥ z + cellP t g 1 (-1) *ᵥ z +
      cellP t g (-1) 1 *ᵥ z + cellP t g (-1) (-1) *ᵥ z := (sum_cellP_mulVec t g z).symm
  have hdec1m : (4 : F) • z = cellP t g 1 (-1) *ᵥ z + cellP t g 1 1 *ᵥ z +
      cellP t g (-1) 1 *ᵥ z + cellP t g (-1) (-1) *ᵥ z := by
    rw [hdec11]; abel
  have hdecm1 : (4 : F) • z = cellP t g (-1) 1 *ᵥ z + cellP t g 1 1 *ᵥ z +
      cellP t g 1 (-1) *ᵥ z + cellP t g (-1) (-1) *ᵥ z := by
    rw [hdec11]; abel
  have hdecmm : (4 : F) • z = cellP t g (-1) (-1) *ᵥ z + cellP t g 1 1 *ᵥ z +
      cellP t g 1 (-1) *ᵥ z + cellP t g (-1) 1 *ᵥ z := by
    rw [hdec11]; abel
  have cross : ∀ a' b' : F, a' * a' = 1 → b' * b' = 1 → (a * a' = -1 ∨ b * b' = -1) →
      sympForm x (cellP t g a' b' *ᵥ z) = 0 := fun a' b' ha' hb' hne =>
    sympForm_cross h2 ht hg hx (cellP_mem t g htt hgg hcomm ha' hb' z) hne
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨cellP t g 1 1 *ᵥ z, cellP_mem t g htt hgg hcomm (by norm_num) (by norm_num) z,
      pair_core h4 hz hdec11 (cross 1 (-1) (by norm_num) (by norm_num) (Or.inr (by norm_num)))
        (cross (-1) 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross (-1) (-1) (by norm_num) (by norm_num) (Or.inl (by norm_num)))⟩
  · exact ⟨cellP t g 1 (-1) *ᵥ z, cellP_mem t g htt hgg hcomm (by norm_num) (by norm_num) z,
      pair_core h4 hz hdec1m (cross 1 1 (by norm_num) (by norm_num) (Or.inr (by norm_num)))
        (cross (-1) 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross (-1) (-1) (by norm_num) (by norm_num) (Or.inl (by norm_num)))⟩
  · exact ⟨cellP t g (-1) 1 *ᵥ z, cellP_mem t g htt hgg hcomm (by norm_num) (by norm_num) z,
      pair_core h4 hz hdecm1 (cross 1 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross 1 (-1) (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross (-1) (-1) (by norm_num) (by norm_num) (Or.inr (by norm_num)))⟩
  · exact ⟨cellP t g (-1) (-1) *ᵥ z, cellP_mem t g htt hgg hcomm (by norm_num) (by norm_num) z,
      pair_core h4 hz hdecmm (cross 1 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross 1 (-1) (by norm_num) (by norm_num) (Or.inl (by norm_num)))
        (cross (-1) 1 (by norm_num) (by norm_num) (Or.inr (by norm_num)))⟩

private lemma three_cells (t g : M4 F) (h2 : (2 : F) ≠ 0) (ht : tᵀ * sympJ F * t = sympJ F)
    (hg : gᵀ * sympJ F * g = sympJ F) (htt : t * t = 1) (hgg : g * g = 1) (hcomm : g * t = t * g)
    {a1 b1 a2 b2 a3 b3 : F} (ha1 : a1 = 1 ∨ a1 = -1) (hb1 : b1 = 1 ∨ b1 = -1)
    (ha2 : a2 = 1 ∨ a2 = -1) (hb2 : b2 = 1 ∨ b2 = -1) (ha3 : a3 = 1 ∨ a3 = -1)
    (hb3 : b3 = 1 ∨ b3 = -1) (hd12 : a1 * a2 = -1 ∨ b1 * b2 = -1)
    (hd13 : a1 * a3 = -1 ∨ b1 * b3 = -1) (hd23 : a2 * a3 = -1 ∨ b2 * b3 = -1)
    (n1 : cellP t g a1 b1 ≠ 0) (n2 : cellP t g a2 b2 ≠ 0) (n3 : cellP t g a3 b3 ≠ 0) :
    False := by
  obtain ⟨z1, hz1⟩ := exists_mulVec_ne_zero n1
  obtain ⟨z2, hz2⟩ := exists_mulVec_ne_zero n2
  obtain ⟨z3, hz3⟩ := exists_mulVec_ne_zero n3
  have m1 := cellP_mem t g htt hgg hcomm (mul_self_of_pm ha1) (mul_self_of_pm hb1) z1
  have m2 := cellP_mem t g htt hgg hcomm (mul_self_of_pm ha2) (mul_self_of_pm hb2) z2
  have m3 := cellP_mem t g htt hgg hcomm (mul_self_of_pm ha3) (mul_self_of_pm hb3) z3
  obtain ⟨y1, my1, p1⟩ := exists_pair t g h2 ht hg htt hgg hcomm ha1 hb1 m1 hz1
  obtain ⟨y2, my2, p2⟩ := exists_pair t g h2 ht hg htt hgg hcomm ha2 hb2 m2 hz2
  obtain ⟨y3, my3, p3⟩ := exists_pair t g h2 ht hg htt hgg hcomm ha3 hb3 m3 hz3
  exact six_false h2 p1 p2 p3
    (sympForm_cross h2 ht hg m1 m2 hd12) (sympForm_cross h2 ht hg m1 my2 hd12)
    (sympForm_cross h2 ht hg my1 m2 hd12) (sympForm_cross h2 ht hg my1 my2 hd12)
    (sympForm_cross h2 ht hg m1 m3 hd13) (sympForm_cross h2 ht hg m1 my3 hd13)
    (sympForm_cross h2 ht hg my1 m3 hd13) (sympForm_cross h2 ht hg my1 my3 hd13)
    (sympForm_cross h2 ht hg m2 m3 hd23) (sympForm_cross h2 ht hg m2 my3 hd23)
    (sympForm_cross h2 ht hg my2 m3 hd23) (sympForm_cross h2 ht hg my2 my3 hd23)

private lemma final_two {t g P R : M4 F} (h4 : (4 : F) ≠ 0) {γ δ : F} (hγ : γ = 1 ∨ γ = -1)
    (hδ : δ = 1 ∨ δ = -1) (hsum : P + R = (4 : F) • (1 : M4 F)) (htP : t * P = P)
    (htR : t * R = -R) (hgP : g * P = γ • P) (hgR : g * R = δ • R) :
    g = 1 ∨ g = -1 ∨ g = t ∨ g = -t := by
  have h1 : t * (P + R) = P - R := by rw [mul_add, htP, htR, sub_eq_add_neg]
  rw [hsum, mul_smul_comm, mul_one] at h1
  have h2 : g * (P + R) = γ • P + δ • R := by rw [mul_add, hgP, hgR]
  rw [hsum, mul_smul_comm, mul_one] at h2
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
  · left
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • g = (4 : F) • (1 : M4 F)
    rw [h2, one_smul, one_smul, hsum]
  · right; right; left
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • g = (4 : F) • t
    rw [h2, h1, one_smul, neg_one_smul, sub_eq_add_neg]
  · right; right; right
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • g = (4 : F) • (-t)
    rw [h2, smul_neg, h1]
    simp only [neg_one_smul, one_smul]
    abel
  · right; left
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • g = (4 : F) • (-1 : M4 F)
    rw [h2, neg_one_smul, neg_one_smul, ← neg_add, hsum, smul_neg]

private theorem sp4_comm_involution (t g : M4 F) (h2 : (2 : F) ≠ 0) (ht : tᵀ * sympJ F * t = sympJ F)
    (hg : gᵀ * sympJ F * g = sympJ F) (htt : t * t = 1) (hgg : g * g = 1)
    (hcomm : g * t = t * g) (ht1 : t ≠ 1) (ht2 : t ≠ -1) :
    g = 1 ∨ g = -1 ∨ g = t ∨ g = -t := by
  have h4 := four_ne_zero h2
  have hsum := sum_cellP t g
  have eA : t * cellP t g 1 1 = cellP t g 1 1 := by
    rw [t_mul_cellP t g htt (by norm_num), one_smul]
  have eB : t * cellP t g 1 (-1) = cellP t g 1 (-1) := by
    rw [t_mul_cellP t g htt (by norm_num), one_smul]
  have eC : t * cellP t g (-1) 1 = -cellP t g (-1) 1 := by
    rw [t_mul_cellP t g htt (by norm_num), neg_one_smul]
  have eD : t * cellP t g (-1) (-1) = -cellP t g (-1) (-1) := by
    rw [t_mul_cellP t g htt (by norm_num), neg_one_smul]
  have hnoPlus : ¬ (cellP t g 1 1 = 0 ∧ cellP t g 1 (-1) = 0) := by
    rintro ⟨hA, hB⟩
    apply ht2
    have hCD : cellP t g (-1) 1 + cellP t g (-1) (-1) = (4 : F) • (1 : M4 F) := by
      rw [hA, hB] at hsum
      simpa only [zero_add, add_zero] using hsum
    have hT : t * (cellP t g (-1) 1 + cellP t g (-1) (-1)) =
        -(cellP t g (-1) 1 + cellP t g (-1) (-1)) := by
      rw [mul_add, eC, eD, neg_add]
    rw [hCD, mul_smul_comm, mul_one] at hT
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • t = (4 : F) • (-1 : M4 F)
    rw [hT, smul_neg]
  have hnoMinus : ¬ (cellP t g (-1) 1 = 0 ∧ cellP t g (-1) (-1) = 0) := by
    rintro ⟨hC, hD⟩
    apply ht1
    have hAB : cellP t g 1 1 + cellP t g 1 (-1) = (4 : F) • (1 : M4 F) := by
      rw [hC, hD] at hsum
      simpa only [zero_add, add_zero] using hsum
    have hT : t * (cellP t g 1 1 + cellP t g 1 (-1)) = cellP t g 1 1 + cellP t g 1 (-1) := by
      rw [mul_add, eA, eB]
    rw [hAB, mul_smul_comm, mul_one] at hT
    refine smul_right_injective (M := M4 F) h4 ?_
    show (4 : F) • t = (4 : F) • (1 : M4 F)
    exact hT
  have hno_plus2 : ¬ (cellP t g 1 1 ≠ 0 ∧ cellP t g 1 (-1) ≠ 0) := by
    rintro ⟨hA, hB⟩
    by_cases hC : cellP t g (-1) 1 = 0
    · have hD : cellP t g (-1) (-1) ≠ 0 := fun hD => hnoMinus ⟨hC, hD⟩
      exact three_cells t g h2 ht hg htt hgg hcomm (a1 := 1) (b1 := 1) (a2 := 1) (b2 := -1)
        (a3 := -1) (b3 := -1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
        (Or.inr rfl) (Or.inr rfl) (Or.inr (by norm_num)) (Or.inl (by norm_num))
        (Or.inl (by norm_num)) hA hB hD
    · exact three_cells t g h2 ht hg htt hgg hcomm (a1 := 1) (b1 := 1) (a2 := 1) (b2 := -1)
        (a3 := -1) (b3 := 1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
        (Or.inr rfl) (Or.inl rfl) (Or.inr (by norm_num)) (Or.inl (by norm_num))
        (Or.inl (by norm_num)) hA hB hC
  have hno_minus2 : ¬ (cellP t g (-1) 1 ≠ 0 ∧ cellP t g (-1) (-1) ≠ 0) := by
    rintro ⟨hC, hD⟩
    by_cases hA : cellP t g 1 1 = 0
    · have hB : cellP t g 1 (-1) ≠ 0 := fun hB => hnoPlus ⟨hA, hB⟩
      exact three_cells t g h2 ht hg htt hgg hcomm (a1 := -1) (b1 := 1) (a2 := -1) (b2 := -1)
        (a3 := 1) (b3 := -1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
        (Or.inl rfl) (Or.inr rfl) (Or.inr (by norm_num)) (Or.inl (by norm_num))
        (Or.inl (by norm_num)) hC hD hB
    ·
      exact three_cells t g h2 ht hg htt hgg hcomm (a1 := -1) (b1 := 1) (a2 := -1) (b2 := -1)
        (a3 := 1) (b3 := 1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
        (Or.inl rfl) (Or.inl rfl) (Or.inr (by norm_num)) (Or.inl (by norm_num))
        (Or.inl (by norm_num)) hC hD hA
  have hplus : (cellP t g 1 1 = 0 ∧ cellP t g 1 (-1) ≠ 0) ∨
      (cellP t g 1 1 ≠ 0 ∧ cellP t g 1 (-1) = 0) := by
    by_cases hA : cellP t g 1 1 = 0 <;> by_cases hB : cellP t g 1 (-1) = 0
    · exact absurd ⟨hA, hB⟩ hnoPlus
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd ⟨hA, hB⟩ hno_plus2
  have hminus : (cellP t g (-1) 1 = 0 ∧ cellP t g (-1) (-1) ≠ 0) ∨
      (cellP t g (-1) 1 ≠ 0 ∧ cellP t g (-1) (-1) = 0) := by
    by_cases hC : cellP t g (-1) 1 = 0 <;> by_cases hD : cellP t g (-1) (-1) = 0
    · exact absurd ⟨hC, hD⟩ hnoMinus
    · exact Or.inl ⟨hC, hD⟩
    · exact Or.inr ⟨hC, hD⟩
    · exact absurd ⟨hC, hD⟩ hno_minus2
  rcases hplus with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> rcases hminus with ⟨hC, hD⟩ | ⟨hC, hD⟩
  ·
    refine final_two h4 (Or.inr rfl) (Or.inr rfl) ?_ eB eD ?_ ?_
    · rw [hA, hC] at hsum
      simpa only [zero_add, add_zero] using hsum
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := 1)
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := -1)
  ·
    refine final_two h4 (Or.inr rfl) (Or.inl rfl) ?_ eB eC ?_ ?_
    · rw [hA, hD] at hsum
      simpa only [zero_add, add_zero] using hsum
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := 1)
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := -1)
  ·
    refine final_two h4 (Or.inl rfl) (Or.inr rfl) ?_ eA eD ?_ ?_
    · rw [hB, hC] at hsum
      simpa only [zero_add, add_zero] using hsum
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := 1)
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := -1)
  ·
    refine final_two h4 (Or.inl rfl) (Or.inl rfl) ?_ eA eC ?_ ?_
    · rw [hB, hD] at hsum
      simpa only [zero_add, add_zero] using hsum
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := 1)
    · exact g_mul_cellP t g hcomm hgg (by norm_num) (a := -1)

end SympK1

section SympGroup

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

private lemma two_ne_zero_of_odd_card [Finite F] (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have h1 : (2 : ℕ) • (1 : F) = 0 := by
    rw [nsmul_eq_mul]
    simpa using h2
  have hord : addOrderOf (1 : F) = 2 := addOrderOf_eq_prime h1 one_ne_zero
  have hdvd := addOrderOf_dvd_natCard (1 : F)
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hF) (even_iff_two_dvd.mpr hdvd)

private lemma neg_one_mem_statedSp2 : (-1 : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  simp

private abbrev spMat (x : StatedSp 2 F) : M4 F := ((x : GL (Fin 2 ⊕ Fin 2) F) : M4 F)

private lemma spMat_mul (x y : StatedSp 2 F) : spMat (x * y) = spMat x * spMat y := by
  simp [spMat]

private lemma spMat_one : spMat (1 : StatedSp 2 F) = 1 := by
  simp [spMat]

private lemma spMat_inj {x y : StatedSp 2 F} (h : spMat x = spMat y) : x = y := by
  apply Subtype.ext
  apply Units.ext
  exact h

private lemma spMat_form (x : StatedSp 2 F) : (spMat x)ᵀ * sympJ F * spMat x = sympJ F :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mp x.2

private lemma card_le_four_of_elemAbelian (h2 : (2 : F) ≠ 0) (A : Subgroup (StatedSp 2 F))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  classical
  set c : StatedSp 2 F := ⟨-1, neg_one_mem_statedSp2⟩ with hc_def
  have hc : spMat c = -1 := by simp [spMat, hc_def]
  have hsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
    simpa [sq] using h
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h := congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using h
  by_cases hex : ∃ t ∈ A, (t : GL (Fin 2 ⊕ Fin 2) F) ≠ 1 ∧ (t : GL (Fin 2 ⊕ Fin 2) F) ≠ -1
  · obtain ⟨t, htA, ht1, ht2⟩ := hex
    have hmem : ∀ x ∈ A, x = 1 ∨ x = c ∨ x = t ∨ x = c * t := by
      intro x hx
      have key := sp4_comm_involution (spMat t) (spMat x) h2 (spMat_form t) (spMat_form x)
        (by rw [← spMat_mul, hsq t htA, spMat_one])
        (by rw [← spMat_mul, hsq x hx, spMat_one])
        (by rw [← spMat_mul, ← spMat_mul, hcomm x hx t htA])
        (fun h => ht1 (Units.ext (by simpa using h)))
        (fun h => ht2 (Units.ext (by simpa using h)))
      rcases key with h | h | h | h
      · exact Or.inl (spMat_inj (by rw [h, spMat_one]))
      · exact Or.inr (Or.inl (spMat_inj (by rw [h, hc])))
      · exact Or.inr (Or.inr (Or.inl (spMat_inj h)))
      · exact Or.inr (Or.inr (Or.inr (spMat_inj (by rw [h, spMat_mul, hc, neg_one_mul]))))
    have hsub : ∀ x ∈ A, x ∈ ({1, c, t, c * t} : Finset (StatedSp 2 F)) := by
      intro x hx
      rcases hmem x hx with h | h | h | h <;> simp [h]
    have hinj : Function.Injective (fun x : A =>
        (⟨x.1, Finset.mem_coe.mpr (hsub x.1 x.2)⟩ :
          ↥((({1, c, t, c * t} : Finset (StatedSp 2 F))) : Set (StatedSp 2 F)))) := by
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
    have h4 := Nat.card_le_card_of_injective _ hinj
    refine h4.trans ?_
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact Finset.card_le_four
  · push_neg at hex
    have hmem : ∀ x ∈ A, x ∈ ({1, c} : Finset (StatedSp 2 F)) := by
      intro x hx
      by_cases h1 : (x : GL (Fin 2 ⊕ Fin 2) F) = 1
      · have hx1 : x = 1 := Subtype.ext h1
        simp [hx1]
      · have hxc : x = c := Subtype.ext (hex x hx h1)
        simp [hxc]
    have hinj : Function.Injective (fun x : A =>
        (⟨x.1, Finset.mem_coe.mpr (hmem x.1 x.2)⟩ :
          ↥((({1, c} : Finset (StatedSp 2 F))) : Set (StatedSp 2 F)))) := by
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
    have h4 := Nat.card_le_card_of_injective _ hinj
    refine h4.trans ?_
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact Finset.card_le_two.trans (by norm_num)

end SympGroup

private theorem pRank_le_two_of_statedSp2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {Q : Type} [Group Q] (e : Q ≃* StatedSp 2 F) : CFSG.pRank 2 Q ≤ 2 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hB : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hcardB : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective e.injective
  have hle := card_le_four_of_elemAbelian h2 (A.map e.toMonoidHom)
  rw [hcardB, hcard] at hle
  by_contra hr
  push_neg at hr
  have h8 : 8 ≤ 2 ^ r := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem coverGH_of_leaves_for
        (P : ∀ (Q : Type) [Group Q] [Finite Q], Prop)
    (hL4 : CoverLeafL4For P) (hU4 : CoverLeafU4For P) (hSz : CoverLeafSz8For P)
    (hA : CoverLeafAltFor P) (hM : CoverLeafM12For P) :
    ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → GH74.GH74Conclusion (Q ⧸ center Q) → P Q := by
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hG := CFSG.GH74.Generic.genericKnownFacts_of_griess hGA
  have hE := CFSG.GH74.E2.e2ComponentFacts
  intro Q _ _ hQ hC
  have hquasi := hQ.1
  have hz : center Q ≠ ⊥ := hQ.2.1
  have h2z := hQ.2.2.1
  have hr : 3 ≤ CFSG.pRank 2 Q := hQ.2.2.2.2.1
  have hgen : GH74.Gen4 Q := hQ.2.2.2.2.2
  rcases hC with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | (h | h | h | h) | ⟨n, hn, hn', h⟩ |
      (h | h | h | h | h | h | h | h)
  · exact absurd (hG.noTwoCover_g2 p f hp hp2 _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd (hG.noTwoCover_3D4 p f hp hp2 _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · rcases hG.psp4_cover p f hp hp2 Q hquasi h2z h with h0 | ⟨F, hFf, hFfin, hcard, ⟨e⟩⟩
    · exact absurd h0 hz
    · have hodd : Odd (Nat.card F) := by
        rw [hcard]
        exact Odd.pow (hp.odd_of_ne_two hp2)
      have hle := pRank_le_two_of_statedSp2 hodd e
      omega
  · exact absurd (hG.noTwoCover_ree f _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact hL4 Q hQ p f hp hp2 hf hq h
  · exact hU4 Q hQ p f hp hp2 hf hq h
  · exact absurd (hG.noTwoCover_psl5 p f hp hq _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd (hG.noTwoCover_psu5 p f hp hq _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd (hE.noTwoCover_even _ (Or.inl h) Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd (hE.noTwoCover_even _ (Or.inr (Or.inl h)) Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd hgen (CFSG.GH74.GLS.Stage1.Main.l34_cover_any Q hquasi h2z h hz)
  · exact hSz Q hQ h
  · exact hA Q hQ n hn hn' h
  · exact hM Q hQ h
  · exact absurd hgen (hE.cover_not_gen4 Q hquasi h2z (Or.inl h) hz)
  · exact absurd hgen (hE.cover_not_gen4_M23_J3 Q hquasi h2z (Or.inl h) hz)
  · exact absurd (hG.noTwoCover_J1 _ h Q hquasi h2z ⟨MulEquiv.refl _⟩) hz
  · exact absurd hgen (hE.cover_not_gen4 Q hquasi h2z (Or.inr h) hz)
  · exact absurd hgen (hE.cover_not_gen4_M23_J3 Q hquasi h2z (Or.inr h) hz)
  · exact absurd (hG.noTwoCover_McL _ h Q hquasi h2z hgen ⟨MulEquiv.refl _⟩) hz
  · exact absurd (hG.noTwoCover_Ly _ h Q hquasi h2z hgen ⟨MulEquiv.refl _⟩) hz

theorem coverGH_of_leaves
        (hL4 : CoverLeafL4) (hU4 : CoverLeafU4) (hSz : CoverLeafSz8)
    (hA : CoverLeafAlt) (hM : CoverLeafM12) : CoverGH :=
  coverGH_of_leaves_for (fun Q _ _ => SylowFourJoined Q) hL4 hU4 hSz hA hM

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
