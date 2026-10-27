module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Small

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.LieType.Steinberg
  CFSG.GH74.Generic.BProg.B2.GenLocU3NF CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

namespace GenLocU3Seven

open GenLocU3Good GenLocU3Small

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem frameForm_mul (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {C : GL (Fin 3) F} {x y : MulAut J}
    (hx : FrameForm h θ C x) (hy : FrameForm h θ C y) : FrameForm h θ C (x * y) := by
  obtain ⟨A', Δ, ψ, hl, hψ, hA'u, hΔd, hAC⟩ := hx
  obtain ⟨B', Δ', χ, hl', hχ, hB'u, hΔ'd, hBC⟩ := hy
  refine ⟨A' * glAut ψ B', Δ * glAut ψ Δ', ψ * χ, hl.mul hl', ?_, ?_, ?_, ?_⟩
  · rcases hψ with rfl | hψ
    · rcases hχ with rfl | hχ
      · exact Or.inl (mul_one 1)
      · exact Or.inr fun c => by rw [one_mul]; exact hχ c
    · rcases hχ with rfl | hχ
      · exact Or.inr fun c => by rw [mul_one]; exact hψ c
      · refine Or.inl (RingEquiv.ext fun c => ?_)
        change ψ (χ c) = c
        rw [hχ, hψ, h.bar_bar]
  · exact (mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hA'u)
      (glAut_mem_unitaryIsom3 ψ ((mem_unitaryIsom3 (h := h)).2 hB'u)))
  · rw [Units.val_mul, coe_glAut]
    exact isDiag_mul' hΔd (hΔ'd.map (map_zero ψ))
  · calc A' * glAut ψ B' * glAut (ψ * χ) C = A' * glAut ψ (B' * glAut χ C) := by
          rw [map_mul]
          simp only [MulAut.mul_apply, map_mul, mul_assoc]
      _ = A' * glAut ψ (C * Δ') := by rw [hBC]
      _ = (A' * glAut ψ C) * glAut ψ Δ' := by rw [map_mul, mul_assoc]
      _ = C * (Δ * glAut ψ Δ') := by rw [hAC, mul_assoc]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem exists_sq_add_sq' {R : Type} [Field R] [Fintype R] (hR : Fintype.card R % 2 = 1) (z : R) :
    ∃ a b : R, a * a + b * b = z := by
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := R) (f := Polynomial.X ^ 2)
    (g := Polynomial.X ^ 2 - Polynomial.C z) (by rw [Polynomial.degree_X_pow]; rfl)
    (by rw [Polynomial.degree_sub_C (by rw [Polynomial.degree_X_pow]; decide),
      Polynomial.degree_X_pow]; rfl) hR
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem exists_real_sq_add_sq (h : UnitaryFieldData p f F) (hq : p ^ f = 7) (z : F) (hz : h.bar z = z) :
    ∃ a b : F, h.bar a = a ∧ h.bar b = b ∧ a * a + b * b = z := by
  have hmem : ∀ c : F, c ∈ fixedSubfield F p f ↔ h.bar c = c := fun c => by
    rw [mem_fixedSubfield, unitaryInvolution_apply, h.bar_apply]
  have : Fintype (fixedSubfield F p f) := Fintype.ofFinite _
  have hcard : Nat.card (fixedSubfield F p f) = 7 := (card_fixedSubfield h.card_eq_sq).trans hq
  have hodd : Fintype.card (fixedSubfield F p f) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq' (R := fixedSubfield F p f) hodd ⟨z, (hmem z).2 hz⟩
  refine ⟨a, b, (hmem _).1 a.2, (hmem _).1 b.2, ?_⟩
  have := congrArg Subtype.val hab
  simpa using this

omit [Fact p.Prime] [CharP F p] in
theorem exists_nonsq_mu (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) (hq : p ^ f = 7) :
    ∃ μ : F, μ ≠ 0 ∧ ¬ SqU h (h.bar μ * μ⁻¹) := by
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card F = 49 := by rw [h.card_eq_sq, hq]; norm_num
  have hord : orderOf g = 48 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have h24 : (g : F) ^ 24 = -1 := by
    have hsq : ((g : F) ^ 24) * ((g : F) ^ 24) = 1 := by
      have : (g ^ 48 : Fˣ) = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
      have := congrArg (fun w : Fˣ => (w : F)) this
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      rw [← pow_add]
      exact this
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exfalso
      have : (g ^ 24 : Fˣ) = 1 := by
        apply Units.ext
        simpa using h1
      have hd := orderOf_dvd_of_pow_eq_one this
      rw [hord] at hd
      omega
    · exact h1
  refine ⟨(g : F), g.ne_zero, ?_⟩
  rintro ⟨n, hn, hnn⟩
  have hbar : h.bar (g : F) = (g : F) ^ 7 := by rw [h.bar_apply, hq]
  have hn8 : n ^ 8 = 1 := by
    have : h.bar n = n ^ 7 := by rw [h.bar_apply, hq]
    rw [this] at hn
    calc n ^ 8 = n ^ 7 * n := by ring
      _ = 1 := hn
  have hnn6 : n * n = (g : F) ^ 6 := by
    rw [hnn, hbar]
    have := g.ne_zero
    field_simp
  have : n ^ 8 = (g : F) ^ 24 := by
    calc n ^ 8 = (n * n) ^ 4 := by ring
      _ = ((g : F) ^ 6) ^ 4 := by rw [hnn6]
      _ = (g : F) ^ 24 := by ring
  rw [hn8, h24] at this
  exact h2 (by linear_combination this)

@[expose] def dgl3 (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0) : GL (Fin 3) F :=
  ⟨Matrix.diagonal u, Matrix.diagonal fun i => (u i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i
       exact mul_inv_cancel₀ (hu i),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i
       exact inv_mul_cancel₀ (hu i)⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_dgl3 (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0) :
    ((dgl3 u hu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal u := rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isDiag_dgl3 (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0) :
    ((dgl3 u hu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag :=
  Matrix.isDiag_diagonal u

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dgl3_du (h : UnitaryFieldData p f F) (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0)
    (hn : ∀ i, h.bar (u i) * u i = 1) : DU h (dgl3 u hu) := by
  refine ⟨?_, isDiag_dgl3 u hu⟩
  rw [coe_dgl3, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i
  exact hn i

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem dgl3_comm {u v : Fin 3 → F} (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) :
    dgl3 u hu * dgl3 v hv = dgl3 v hv * dgl3 u hu := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dgl3, coe_dgl3, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; ext i
  exact mul_comm _ _

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_glAut_dgl3 (ψ : F ≃+* F) (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0) :
    ((glAut ψ (dgl3 u hu) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal fun i => ψ (u i) := by
  rw [coe_glAut, coe_dgl3, Matrix.diagonal_map (map_zero _)]

@[expose] def m0 (μ a b : F) : Matrix (Fin 3) (Fin 3) F :=
  !![μ * a, 0, -(μ * b); 0, 1, 0; μ * b, 0, μ * a]

@[expose] def m0inv (μ' a b : F) : Matrix (Fin 3) (Fin 3) F :=
  !![μ' * a, 0, μ' * b; 0, 1, 0; -(μ' * b), 0, μ' * a]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem m0_mul_m0inv {μ μ' a b : F} (hN : μ' * μ * (a * a + b * b) = 1) :
    m0 μ a b * m0inv μ' a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m0, m0inv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hN

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem m0inv_mul_m0 {μ μ' a b : F} (hN : μ' * μ * (a * a + b * b) = 1) :
    m0inv μ' a b * m0 μ a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m0, m0inv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hN

@[expose] def m0gl (μ μ' a b : F) (hN : μ' * μ * (a * a + b * b) = 1) : GL (Fin 3) F :=
  ⟨m0 μ a b, m0inv μ' a b, m0_mul_m0inv hN, m0inv_mul_m0 hN⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_m0gl (μ μ' a b : F) (hN : μ' * μ * (a * a + b * b) = 1) :
    ((m0gl μ μ' a b hN : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = m0 μ a b := rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem m0gl_unitary (h : UnitaryFieldData p f F) {μ a b : F} (ha : h.bar a = a) (hb : h.bar b = b)
    (hN : h.bar μ * μ * (a * a + b * b) = 1) :
    (((m0gl μ (h.bar μ) a b hN : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((m0gl μ (h.bar μ) a b hN : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [coe_m0gl]
  have : ((m0 μ a b).map h.bar)ᵀ = m0inv (h.bar μ) a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [m0, m0inv, Matrix.map_apply, Matrix.transpose_apply, ha, hb]
  rw [this]
  exact m0inv_mul_m0 hN

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem glAut_m0gl (h : UnitaryFieldData p f F) {ψ : F ≃+* F} (hψ : ∀ c, ψ c = h.bar c) {μ a b : F}
    (ha : h.bar a = a) (hb : h.bar b = b) (hN : h.bar μ * μ * (a * a + b * b) = 1) (hμ : μ ≠ 0)
    (hD : ∀ i, (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) i ≠ 0) :
    glAut ψ (m0gl μ (h.bar μ) a b hN) =
      m0gl μ (h.bar μ) a b hN * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD := by
  apply Units.ext
  rw [coe_glAut, Units.val_mul, coe_dgl3, coe_m0gl]
  have hbm : h.bar μ ≠ 0 := by
    intro h0
    have := hN
    rw [h0] at this
    simp at this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m0, Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, hψ, ha, hb] <;> field_simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diagonal_const_comm (c : F) (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix.diagonal (fun _ : Fin 3 => c) * M = M * Matrix.diagonal (fun _ : Fin 3 => c) := by
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diag_pm_comm (e μ a b : F) :
    Matrix.diagonal ![e, -e, e] * m0 μ a b = m0 μ a b * Matrix.diagonal ![e, -e, e] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m0, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_dgl3_inv (u : Fin 3 → F) (hu : ∀ i, u i ≠ 0) :
    (((dgl3 u hu)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun i => (u i)⁻¹ := rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem x2_identity (h : UnitaryFieldData p f F) {ψ : F ≃+* F} (hψ : ∀ c, ψ c = h.bar c)
    {ys d : Fin 3 → F} (hys0 : ∀ u, ys u ≠ 0) (hysn : ∀ u, h.bar (ys u) * ys u = 1)
    (hd0 : ∀ u, d u ≠ 0) (hyd : ∀ u, ys u * ys u = d 0 * d u) {Δ₂ : GL (Fin 3) F}
    (hΔ : (Δ₂ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) {μ a b : F} (ha : h.bar a = a)
    (hb : h.bar b = b) (hN : h.bar μ * μ * (a * a + b * b) = 1) (hμ : μ ≠ 0)
    (hD : ∀ i, (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) i ≠ 0) :
    Δ₂ * glAut ψ (dgl3 ys hys0 * m0gl μ (h.bar μ) a b hN) =
      (dgl3 ys hys0 * m0gl μ (h.bar μ) a b hN) *
        (dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) *
          dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD) := by
  have I1 : Δ₂ * (dgl3 ys hys0)⁻¹ =
      dgl3 ys hys0 * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) := by
    apply Units.ext
    simp only [Units.val_mul, coe_dgl3, coe_dgl3_inv, hΔ, Matrix.diagonal_mul_diagonal]
    congr 1; ext u
    have h1 := hys0 u
    have h2 := hd0 0
    field_simp
    linear_combination (-1 : F) * hyd u
  have I2 : glAut ψ (dgl3 ys hys0) = (dgl3 ys hys0)⁻¹ := by
    apply Units.ext
    rw [coe_glAut_dgl3, coe_dgl3_inv]
    congr 1; ext u
    rw [hψ]
    exact eq_inv_of_mul_eq_one_left (hysn u)
  have I3 := glAut_m0gl h hψ ha hb hN hμ hD
  have I4 : dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) * m0gl μ (h.bar μ) a b hN =
      m0gl μ (h.bar μ) a b hN * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_dgl3, coe_m0gl]
    exact diagonal_const_comm _ _
  calc Δ₂ * glAut ψ (dgl3 ys hys0 * m0gl μ (h.bar μ) a b hN)
      = Δ₂ * ((dgl3 ys hys0)⁻¹ * (m0gl μ (h.bar μ) a b hN * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD)) := by
        rw [map_mul, I2, I3]
    _ = (Δ₂ * (dgl3 ys hys0)⁻¹) * (m0gl μ (h.bar μ) a b hN * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD) := by
        rw [mul_assoc]
    _ = (dgl3 ys hys0 * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0))) *
          (m0gl μ (h.bar μ) a b hN * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD) := by rw [I1]
    _ = dgl3 ys hys0 * (dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) *
          m0gl μ (h.bar μ) a b hN) * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD := by
        simp only [mul_assoc]
    _ = dgl3 ys hys0 * (m0gl μ (h.bar μ) a b hN *
          dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0))) * dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD := by
        rw [I4]
    _ = (dgl3 ys hys0 * m0gl μ (h.bar μ) a b hN) *
          (dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) *
            dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD) := by
        simp only [mul_assoc]

theorem block_entries_frame (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {A : Type} [Group A] (α : A →* MulAut J) (i : Fin 2) (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ C hCu i y) = frameBlock h θ C hCu i (β a y))
    {a : A} {A' Δ : GL (Fin 3) F} {ψ : F ≃+* F} (hl : IsLift θ A' ψ (α a))
    (hA'u : ((A' : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A' : Matrix (Fin 3) (Fin 3) F) = 1)
    (hΔd : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) (hAC : A' * glAut ψ C = C * Δ)
    (y : Su F p f 2) (u v : Fin 2) :
    ym (β a y) u v =
      ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i u) (idx3 i u) * ψ (ym y u v) *
        (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i v) (idx3 i v))⁻¹ := by
  obtain ⟨y', hy1, hy2⟩ := frameBlock_apply h hCu hl hA'u hΔd hAC i y
  have : β a y = y' := frameBlock_injective h hθ hCu i (by rw [← hβ, hy2])
  rw [this]
  exact hy1 u v

theorem beta_congr (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {A : Type} [Group A] (α : A →* MulAut J) (i : Fin 2) (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ C hCu i y) = frameBlock h θ C hCu i (β a y))
    {a a' : A} (hα : α a = α a') : β a = β a' :=
  MulEquiv.ext fun y => frameBlock_injective h hθ hCu i (by rw [← hβ, ← hβ, hα])

theorem card_le_four_of_four {A B : Type} [Group A] [Group B] (β : A →* B) (b₁ b₂ : B)
    (hs : ∀ a, β a = 1 ∨ β a = b₁ ∨ β a = b₂ ∨ β a = b₁ * b₂) : Nat.card β.range ≤ 4 := by
  classical
  have hsub : (β.range : Set B) ⊆ {1, b₁, b₂, b₁ * b₂} := by
    rintro _ ⟨a, rfl⟩
    rcases hs a with h | h | h | h <;> simp [h]
  calc Nat.card β.range = (β.range : Set B).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, b₁, b₂, b₁ * b₂} : Set B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      simp

theorem gammaAct_eq_top_classC_mid (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (hq : p ^ f = 7) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (α : A →* MulAut J)
    (a₁ a₂ : A) (hall : ∀ a, α a = 1 ∨ α a = α a₁ ∨ α a = α a₂ ∨ α a = α a₁ * α a₂)
    {Δ₁ : GL (Fin 3) F} (hl₁ : IsLift θ Δ₁ 1 (α a₁)) (hD₁ : DU h Δ₁) {e : F}
    (e0 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) 0 0 = e) (e1 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) 1 1 = -e)
    (e2 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) 2 2 = e) {Δ₂ : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl₂ : IsLift θ Δ₂ ψ (α a₂)) (hψ : ∀ c, ψ c = h.bar c) (hD₂ : DU h Δ₂)
    (s01 : SqU h ((Δ₂ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ₂ : Matrix (Fin 3) (Fin 3) F) 1 1))
    (s02 : SqU h ((Δ₂ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ₂ : Matrix (Fin 3) (Fin 3) F) 2 2)) :
    gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := GenLocU3Desc.two_ne_zero' h hp2
  have hq2 : p ^ f ≠ 2 := by rw [hq]; norm_num
  have h5 : 5 ≤ p ^ f := by rw [hq]; norm_num
  set d : Fin 3 → F := fun u => (Δ₂ : Matrix (Fin 3) (Fin 3) F) u u with hd
  have hd0 : ∀ u, d u ≠ 0 := fun u => hD₂.entry_ne_zero u
  have hdn : ∀ u, h.bar (d u) * d u = 1 := fun u => hD₂.entry_norm u
  have hΔ₂ : (Δ₂ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d := hD₂.2.diagonal_diag.symm
  obtain ⟨n1, hn1, hn1sq⟩ := s01
  obtain ⟨n2, hn2, hn2sq⟩ := s02
  have hne : ∀ n : F, h.bar n * n = 1 → n ≠ 0 := fun n hn h0 => by
    rw [h0] at hn; simp at hn
  set ys : Fin 3 → F := ![d 0, n1, n2] with hys
  have hys0 : ∀ u, ys u ≠ 0 := by
    intro u; fin_cases u
    · exact hd0 0
    · exact hne n1 hn1
    · exact hne n2 hn2
  have hysn : ∀ u, h.bar (ys u) * ys u = 1 := by
    intro u; fin_cases u
    · exact hdn 0
    · exact hn1
    · exact hn2
  have hyd : ∀ u, ys u * ys u = d 0 * d u := by
    intro u; fin_cases u
    · rfl
    · exact hn1sq
    · exact hn2sq
  obtain ⟨μ, hμ0, hμ⟩ := exists_nonsq_mu h h2 hq
  have hbμ : h.bar μ ≠ 0 := by
    intro h0
    apply hμ0
    have := h.bar_bar μ
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨a, b, ha, hb, hab⟩ := exists_real_sq_add_sq h hq ((h.bar μ * μ)⁻¹) (by
    rw [map_inv₀, map_mul, h.bar_bar, mul_comm])
  have hN : h.bar μ * μ * (a * a + b * b) = 1 := by
    rw [hab]; field_simp
  have hD : ∀ i, (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) i ≠ 0 := by
    intro i; fin_cases i
    · exact div_ne_zero hbμ hμ0
    · exact one_ne_zero
    · exact div_ne_zero hbμ hμ0
  have hyU : DU h (dgl3 ys hys0) := dgl3_du h ys hys0 hysn
  set M : GL (Fin 3) F := m0gl μ (h.bar μ) a b hN with hM
  set C : GL (Fin 3) F := dgl3 ys hys0 * M with hC
  have hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1 :=
    (mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hyU.1)
      ((mem_unitaryIsom3 (h := h)).2 (m0gl_unitary h ha hb hN)))
  set S : GL (Fin 3) F := dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) with hS
  set D3 : GL (Fin 3) F := dgl3 ![h.bar μ / μ, 1, h.bar μ / μ] hD with hD3
  have hFF2 : FrameForm h θ C (α a₂) := by
    refine ⟨Δ₂, S * D3, ψ, hl₂, Or.inr hψ, hD₂.1, ?_, ?_⟩
    · rw [Units.val_mul]
      exact isDiag_mul' (isDiag_dgl3 _ _) (isDiag_dgl3 _ _)
    · exact x2_identity h hψ hys0 hysn hd0 hyd hΔ₂ ha hb hN hμ0 hD
  have hFF1 : FrameForm h θ C (α a₁) := by
    refine ⟨Δ₁, Δ₁, 1, hl₁, Or.inl rfl, hD₁.1, hD₁.2, ?_⟩
    rw [glAut_one_apply]
    have hd1 : ∀ u, (Δ₁ : Matrix (Fin 3) (Fin 3) F) u u ≠ 0 := fun u => hD₁.entry_ne_zero u
    have hΔ₁ : Δ₁ = dgl3 (fun u => (Δ₁ : Matrix (Fin 3) (Fin 3) F) u u) hd1 :=
      Units.ext hD₁.2.diagonal_diag.symm
    have hΔ₁' : (Δ₁ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![e, -e, e] := by
      rw [← hD₁.2.diagonal_diag]
      congr 1; ext u
      fin_cases u
      · exact e0
      · exact e1
      · exact e2
    have hcM : Δ₁ * M = M * Δ₁ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hΔ₁', hM, coe_m0gl]
      exact diag_pm_comm e μ a b
    calc Δ₁ * C = Δ₁ * dgl3 ys hys0 * M := by rw [hC, mul_assoc]
      _ = dgl3 ys hys0 * Δ₁ * M := by rw [hΔ₁, dgl3_comm hd1 hys0, ← hΔ₁]
      _ = dgl3 ys hys0 * (Δ₁ * M) := by rw [mul_assoc]
      _ = dgl3 ys hys0 * (M * Δ₁) := by rw [hcM]
      _ = C * Δ₁ := by rw [hC, mul_assoc]
  have hFF0 : FrameForm h θ C (1 : MulAut J) :=
    ⟨1, 1, 1, isLift_one, Or.inl rfl, (DU.one h).1, (DU.one h).2, by rw [glAut_one_apply, one_mul, mul_one]⟩
  have hFF : ∀ a, FrameForm h θ C (α a) := by
    intro a
    rcases hall a with h0 | h1 | h2' | h3
    · rw [h0]; exact hFF0
    · rw [h1]; exact hFF1
    · rw [h2']; exact hFF2
    · rw [h3]; exact frameForm_mul h hFF1 hFF2
  refine gammaAct_eq_top_of_blocks_frame h hq2 hθ hCu α hFF fun i β hβ => ?_
  have hcard : Nat.card β.range ≤ 4 := by
    refine card_le_four_of_four β (β a₁) (β a₂) fun a => ?_
    rcases hall a with h0 | h1 | h2' | h3
    · left
      rw [beta_congr h hθ hCu α i β hβ (a' := 1) (by rw [h0, map_one]), map_one]
    · right; left
      exact beta_congr h hθ hCu α i β hβ h1
    · right; right; left
      exact beta_congr h hθ hCu α i β hβ h2'
    · right; right; right
      rw [beta_congr h hθ hCu α i β hβ (a' := a₁ * a₂) (by rw [h3, map_mul]), map_mul]
  have hid : Δ₂ * glAut ψ C = C * (S * D3) :=
    x2_identity h hψ hys0 hysn hd0 hyd hΔ₂ ha hb hN hμ0 hD
  have hdiagSD : ((S * D3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
    rw [Units.val_mul]
    exact isDiag_mul' (isDiag_dgl3 _ _) (isDiag_dgl3 _ _)
  have hent : ∀ u, ((S * D3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) u u =
      (d 0)⁻¹ * (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u := by
    intro u
    rw [Units.val_mul, hS, hD3, coe_dgl3, coe_dgl3, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq]
  have hc0 : h.bar (h.bar μ / μ) * (h.bar μ / μ) = 1 := by
    rw [map_div₀, h.bar_bar]
    field_simp
  have hd0inv : h.bar ((d 0)⁻¹) * (d 0)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hdn 0, inv_one]
  have hnormc : ∀ u : Fin 3, h.bar ((d 0)⁻¹ * (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) *
      ((d 0)⁻¹ * (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) = 1 := by
    intro u
    rw [map_mul]
    have : h.bar ((![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) *
        (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u = 1 := by
      fin_cases u
      · exact hc0
      · simp
      · exact hc0
    calc h.bar ((d 0)⁻¹) * h.bar ((![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) *
          ((d 0)⁻¹ * (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u)
        = (h.bar ((d 0)⁻¹) * (d 0)⁻¹) * (h.bar ((![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) *
          (![h.bar μ / μ, 1, h.bar μ / μ] : Fin 3 → F) u) := by ring
      _ = 1 := by rw [hd0inv, this, one_mul]
  have hidx : ∀ i : Fin 2, (idx3 i 0 = 0 ∧ idx3 i 1 = 1) ∨ (idx3 i 0 = 1 ∧ idx3 i 1 = 2) := by
    intro i; fin_cases i
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  have hni : ¬ β.range ≤ (MulAut.conj : Su F p f 2 →* MulAut (Su F p f 2)).range := by
    intro hle
    refine not_inner_of_entries h (by omega)
      (fun u => ((S * D3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i u) (idx3 i u))
      (fun u => by rw [hent]; exact hnormc _) (Or.inr hψ)
      (fun y u v => block_entries_frame h hθ hCu α i β hβ hl₂ hD₂.1 hdiagSD hid y u v) ?_
      (hle ⟨a₂, rfl⟩)
    rintro ⟨n, hn, hnn⟩
    apply hμ
    have hz : ((d 0)⁻¹ * (d 0)⁻¹) * (h.bar μ * μ⁻¹) = n * n := by
      rw [hnn]
      show _ = ((S * D3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i 0) (idx3 i 0) *
        ((S * D3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i 1) (idx3 i 1)
      rw [hent, hent]
      rcases hidx i with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;>
        simp [div_eq_mul_inv] <;> ring
    refine ⟨n * d 0, ?_, ?_⟩
    · rw [map_mul]
      calc h.bar n * h.bar (d 0) * (n * d 0) = (h.bar n * n) * (h.bar (d 0) * d 0) := by ring
        _ = 1 := by rw [hn, hdn 0, one_mul]
    · have := hd0 0
      calc n * d 0 * (n * d 0) = (n * n) * (d 0 * d 0) := by ring
        _ = ((d 0)⁻¹ * (d 0)⁻¹) * (h.bar μ * μ⁻¹) * (d 0 * d 0) := by rw [hz]
        _ = h.bar μ * μ⁻¹ := by field_simp
  exact gammaAct_su2_of_not_inner_small h hp2 h5 hA β hni hcard

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isLift_conj_cover (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {x : MulAut J} {A' Δ : GL (Fin 3) F} {ψ : F ≃+* F} (hl : IsLift θ A' ψ x)
    (hAC : A' * glAut ψ C = C * Δ) :
    IsLift (θ.comp (KFU.conjSU h ⟨C, mem_pfu_of_unitary h hCu⟩).toMonoidHom) Δ ψ x := by
  have hC := mem_pfu_of_unitary h hCu
  have hΔeq : Δ = C⁻¹ * (A' * glAut ψ C) := by rw [hAC]; group
  intro g
  obtain ⟨g1, hg1, hg2⟩ := hl (KFU.conjSU h ⟨C, hC⟩ g)
  refine ⟨(KFU.conjSU h ⟨C, hC⟩).symm g1, ?_, ?_⟩
  · change C⁻¹ * (g1 : GL (Fin 3) F) * C = Δ * glAut ψ (g : GL (Fin 3) F) * Δ⁻¹
    rw [hg1, hΔeq]
    change C⁻¹ * (A' * glAut ψ (C * (g : GL (Fin 3) F) * C⁻¹) * A'⁻¹) * C = _
    simp only [map_mul, map_inv]
    group
  · change θ (KFU.conjSU h ⟨C, hC⟩ ((KFU.conjSU h ⟨C, hC⟩).symm g1)) =
      x (θ (KFU.conjSU h ⟨C, hC⟩ g))
    rw [MulEquiv.apply_symm_apply, hg2]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem sqU_pair {h : UnitaryFieldData p f F} {d : Fin 3 → F}
    (hs : SqU h (d 0 * d 1) ∧ SqU h (d 0 * d 2) ∧ SqU h (d 1 * d 2)) {u v : Fin 3} (huv : u ≠ v) :
    SqU h (d u * d v) := by
  obtain ⟨h01, h02, h12⟩ := hs
  fin_cases u <;> fin_cases v
  all_goals first | exact absurd rfl huv | skip
  · exact h01
  · exact h02
  · rw [mul_comm]; exact h01
  · exact h12
  · rw [mul_comm]; exact h02
  · rw [mul_comm]; exact h12

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem odd_perm {d : Fin 3 → F}
    (hc : (d 1 = d 2 ∧ d 0 = -d 1) ∨ (d 0 = d 2 ∧ d 1 = -d 0) ∨ (d 0 = d 1 ∧ d 2 = -d 0)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (e : F), d (σ 0) = e ∧ d (σ 1) = -e ∧ d (σ 2) = e := by
  rcases hc with ⟨h12, h0⟩ | ⟨h02, h1⟩ | ⟨h01, h2⟩
  · exact ⟨Equiv.swap 0 1, d 1, rfl, by simpa using h0,
      by rw [show (Equiv.swap (0 : Fin 3) 1) 2 = 2 by decide]; exact h12.symm⟩
  · exact ⟨1, d 0, rfl, h1, h02.symm⟩
  · exact ⟨Equiv.swap 1 2, d 0, rfl, by simpa using h2, by simpa using h01.symm⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem conj_pgl_du {h : UnitaryFieldData p f F} {Δ : GL (Fin 3) F} (hΔ : DU h Δ)
    (σ : Equiv.Perm (Fin 3)) : DU h ((pgl σ)⁻¹ * Δ * pgl σ) := by
  refine ⟨(mem_unitaryIsom3 (h := h)).1 (mul_mem (mul_mem (inv_mem ?_) ((mem_unitaryIsom3 (h := h)).2 hΔ.1)) ?_),
    isDiag_conj_pgl σ hΔ.2⟩
  · exact (mem_unitaryIsom3 (h := h)).2 (by
      rw [coe_pgl, pmat_map σ _ (map_zero h.bar) (map_one h.bar)]
      exact pmatT_mul_pmat σ)
  · exact (mem_unitaryIsom3 (h := h)).2 (by
      rw [coe_pgl, pmat_map σ _ (map_zero h.bar) (map_one h.bar)]
      exact pmatT_mul_pmat σ)

theorem gammaAct_eq_top_classC (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (hq : p ^ f = 7) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (α : A →* MulAut J)
    (a₁ a₂ : A) (hall : ∀ a, α a = 1 ∨ α a = α a₁ ∨ α a = α a₂ ∨ α a = α a₁ * α a₂)
    {Δ₁ : GL (Fin 3) F} (hl₁ : IsLift θ Δ₁ 1 (α a₁)) (hD₁ : DU h Δ₁) (σ : Equiv.Perm (Fin 3)) {e : F}
    (e0 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) (σ 0) (σ 0) = e)
    (e1 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) (σ 1) (σ 1) = -e)
    (e2 : (Δ₁ : Matrix (Fin 3) (Fin 3) F) (σ 2) (σ 2) = e) {Δ₂ : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl₂ : IsLift θ Δ₂ ψ (α a₂)) (hψ : ∀ c, ψ c = h.bar c) (hD₂ : DU h Δ₂)
    (hs : SqU h ((Δ₂ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ₂ : Matrix (Fin 3) (Fin 3) F) 1 1) ∧
      SqU h ((Δ₂ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ₂ : Matrix (Fin 3) (Fin 3) F) 2 2) ∧
      SqU h ((Δ₂ : Matrix (Fin 3) (Fin 3) F) 1 1 * (Δ₂ : Matrix (Fin 3) (Fin 3) F) 2 2)) :
    gammaAct α = ⊤ := by
  have hCu := pgl_unitary h σ
  have hθ' := isCover_comp_conj h hθ hCu
  refine gammaAct_eq_top_classC_mid h hp2 hq hθ' hA α a₁ a₂ hall
    (Δ₁ := (pgl σ)⁻¹ * Δ₁ * pgl σ) (isLift_conj_cover h hCu hl₁ (by rw [glAut_one_apply]; group))
    (conj_pgl_du hD₁ σ) (e := e) (by rw [coe_conj_pgl]; exact e0) (by rw [coe_conj_pgl]; exact e1)
    (by rw [coe_conj_pgl]; exact e2) (Δ₂ := (pgl σ)⁻¹ * Δ₂ * pgl σ) (ψ := ψ)
    (isLift_conj_cover h hCu hl₂ (by rw [glAut_pgl]; group)) hψ (conj_pgl_du hD₂ σ) ?_ ?_
  · rw [coe_conj_pgl, coe_conj_pgl]
    exact sqU_pair (d := fun u => (Δ₂ : Matrix (Fin 3) (Fin 3) F) u u) hs
      (fun e => absurd (σ.injective e) (by decide))
  · rw [coe_conj_pgl, coe_conj_pgl]
    exact sqU_pair (d := fun u => (Δ₂ : Matrix (Fin 3) (Fin 3) F) u u) hs
      (fun e => absurd (σ.injective e) (by decide))

@[expose] def Exc7E8 (h : UnitaryFieldData p f F) {J : Type} [Group J] (θ : ↥(unitarySU p f F 3) →* J)
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1) : Prop :=
  ∃ a₁ ∈ A0 h θ α hsq, ∃ a₃ ∈ A0 h θ α hsq, α a₁ ≠ 1 ∧ α a₃ ≠ 1 ∧ α a₁ ≠ α a₃ ∧
    ∃ a ∉ A0 h θ α hsq, ∃ (Δ : GL (Fin 3) F) (ψ : F ≃+* F), IsLift θ Δ ψ (α a) ∧
      (∀ c, ψ c = h.bar c) ∧ DU h Δ ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ : Matrix (Fin 3) (Fin 3) F) 1 1) ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ : Matrix (Fin 3) (Fin 3) F) 2 2) ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 1 1 * (Δ : Matrix (Fin 3) (Fin 3) F) 2 2)

theorem exc7_of_exc7E8 (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hq : p ^ f = 7) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ)
    {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (α : A →* MulAut J)
    (hα : ∀ a, DiagLift h θ (α a)) (hsq : ∀ a : A, a * a = 1)
    (hE8 : Exc7E8 h θ α hsq → gammaAct α = ⊤) : Exc7 h θ α hsq → gammaAct α = ⊤ := by
  rintro ⟨⟨a₁, ha₁, hne₁⟩, a₂, ha₂, Δ₂, ψ, hl₂, hψ, hD₂, s01, s02, s12⟩
  by_cases hc : ∀ a ∈ A0 h θ α hsq, α a = 1 ∨ α a = α a₁
  · have h2 : (2 : F) ≠ 0 := GenLocU3Desc.two_ne_zero' h hp2
    have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
      rw [hθ.ker]; exact unitaryScalars_le_center h 3
    have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
      (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
    have hall : ∀ a, α a = 1 ∨ α a = α a₁ ∨ α a = α a₂ ∨ α a = α a₁ * α a₂ := by
      intro a
      have hsq' : ∀ b : A, α b * α b = 1 := fun b => by rw [← map_mul, hsq b, map_one]
      by_cases ha : a ∈ A0 h θ α hsq
      · rcases hc a ha with h0 | h1
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
      · have hm := mul_mem_A0 h α hsq hα ha ha₂
        rcases hc _ hm with h0 | h1
        · right; right; left
          rw [map_mul] at h0
          calc α a = α a * (α a₂ * α a₂) := by rw [hsq' a₂, mul_one]
            _ = (α a * α a₂) * α a₂ := by rw [mul_assoc]
            _ = α a₂ := by rw [h0, one_mul]
        · right; right; right
          rw [map_mul] at h1
          calc α a = α a * (α a₂ * α a₂) := by rw [hsq' a₂, mul_one]
            _ = (α a * α a₂) * α a₂ := by rw [mul_assoc]
            _ = α a₁ * α a₂ := by rw [h1]
    obtain ⟨Δ₁, hl₁, hD₁⟩ := ha₁
    obtain ⟨c, hc'⟩ := sq_scalar_of_isLift h h2 hPerf hker (by rw [← map_mul, hsq a₁, map_one]) hl₁
    have hd1sq := diag_sq_eq hD₁.2 hc'
    have hnotscalar : ¬ ((Δ₁ : Matrix (Fin 3) (Fin 3) F) 0 0 = (Δ₁ : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
        (Δ₁ : Matrix (Fin 3) (Fin 3) F) 1 1 = (Δ₁ : Matrix (Fin 3) (Fin 3) F) 2 2) := fun hs =>
      hne₁ (eq_one_of_scalar_lift hθ hl₁ hD₁.2 hs)
    obtain ⟨σ, e, e0, e1, e2⟩ := odd_perm (d := fun u => (Δ₁ : Matrix (Fin 3) (Fin 3) F) u u)
      (odd_index (d := fun u => (Δ₁ : Matrix (Fin 3) (Fin 3) F) u u) hd1sq hnotscalar)
    exact gammaAct_eq_top_classC h hp2 hq hθ hA α a₁ a₂ hall hl₁ hD₁ σ e0 e1 e2 hl₂ hψ hD₂
      ⟨s01, s02, s12⟩
  · push Not at hc
    obtain ⟨a₃, ha₃, h3a, h3b⟩ := hc
    exact hE8 ⟨a₁, ha₁, a₃, ha₃, hne₁, h3a, fun e => h3b e.symm, a₂, ha₂, Δ₂, ψ, hl₂, hψ, hD₂,
      s01, s02, s12⟩

@[expose] def Exc7E8Hyp (J : Type) [Group J] (p f : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F p] [Fact p.Prime] (h : UnitaryFieldData p f F)
    (θ : ↥(unitarySU p f F 3) →* J), IsCover h θ → ∀ (A : Type) [Group A] [Finite A], IsRank23 A →
      ∀ (α : A →* MulAut J), (∀ a, DiagLift h θ (α a)) → ∀ hsq : (∀ a : A, a * a = 1),
        Exc7E8 h θ α hsq → gammaAct α = ⊤

theorem genProp_psu3_seven_of_exc8 {J : Type} [Group J] {p f : ℕ}
    (hq : p ^ f = 7) (hJ : LieModel J .PSU 3 p f) (hexc : Exc7E8Hyp J p f) : GenProp J :=
  genProp_psu3_seven_of_exc hq hJ fun F _ _ _ _ h θ hθ A _ _ hA α hα hsq =>
    exc7_of_exc7E8 h (ne_two_of_pow h.one_le (Or.inr (Or.inl hq))) hq hθ hA α hα hsq
      (hexc F h θ hθ A hA α hα hsq)

end GenLocU3Seven

end CFSG.GH74.Generic.BProg.B2
