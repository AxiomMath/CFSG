module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2TorusFive
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups

section SignWeyl

variable {τ : Tag} {K : Type} [Field K]

@[expose] def SignWeyl (τ : Tag) (K : Type) [Field K] (g : ModGL τ K) (w : WeylGroup τ) : Prop :=
  ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
    g * pinnedX τ K γ c * g⁻¹ = pinnedX τ K (w • γ) (ε * c)

theorem SignWeyl.mul {g h : ModGL τ K} {w w' : WeylGroup τ} (hg : SignWeyl τ K g w)
    (hh : SignWeyl τ K h w') : SignWeyl τ K (g * h) (w * w') := by
  intro γ hγ
  obtain ⟨ε₂, hε₂, h2⟩ := hh γ hγ
  obtain ⟨ε₁, hε₁, h1⟩ := hg (w' • γ) (IsRoot.smul hγ w')
  refine ⟨ε₁ * ε₂, ?_, fun c => ?_⟩
  · calc ε₁ * ε₂ * (ε₁ * ε₂) = (ε₁ * ε₁) * (ε₂ * ε₂) := by ring
      _ = 1 := by rw [hε₁, hε₂, one_mul]
  · calc g * h * pinnedX τ K γ c * (g * h)⁻¹ = g * (h * pinnedX τ K γ c * h⁻¹) * g⁻¹ := by group
      _ = g * pinnedX τ K (w' • γ) (ε₂ * c) * g⁻¹ := by rw [h2]
      _ = pinnedX τ K (w • w' • γ) (ε₁ * (ε₂ * c)) := h1 _
      _ = pinnedX τ K ((w * w') • γ) (ε₁ * ε₂ * c) := by rw [mul_smul, mul_assoc]

theorem SignWeyl.inv {g : ModGL τ K} {w : WeylGroup τ} (hg : SignWeyl τ K g w) :
    SignWeyl τ K g⁻¹ w⁻¹ := by
  intro γ hγ
  have hγ' : IsRoot τ (w⁻¹ • γ) := IsRoot.smul hγ w⁻¹
  obtain ⟨ε, hε, h⟩ := hg (w⁻¹ • γ) hγ'
  refine ⟨ε, hε, fun c => ?_⟩
  have h1 := h (ε * c)
  rw [← mul_assoc, hε, one_mul, smul_inv_smul] at h1
  have h2 : g⁻¹ * pinnedX τ K γ c * g⁻¹⁻¹ = pinnedX τ K (w⁻¹ • γ) (ε * c) := by
    calc g⁻¹ * pinnedX τ K γ c * g⁻¹⁻¹
        = g⁻¹ * (g * pinnedX τ K (w⁻¹ • γ) (ε * c) * g⁻¹) * g⁻¹⁻¹ := by rw [h1]
      _ = pinnedX τ K (w⁻¹ • γ) (ε * c) := by group
  exact h2

theorem signWeyl_canonicalRep (w : WeylGroup τ) :
    SignWeyl τ K (canonicalRep (coxeterSystem τ) K w) w := fun _ hγ =>
  exists_canonicalRep_mul_pinnedX_mul_inv K w hγ

theorem signWeyl_rootChart_WSL (w : WeylGroup τ) (i : Fin τ.rank) :
    SignWeyl τ K (rootChart τ K w i WSL) (w * simple τ i * w⁻¹) := by
  rw [rootChart_WSL_apply, ← canonicalRep_simple (coxeterSystem τ) K i]
  exact ((signWeyl_canonicalRep w).mul (signWeyl_canonicalRep (simple τ i))).mul
    (signWeyl_canonicalRep w).inv

end SignWeyl

section M0

variable {F : Type} [Field F]

theorem g2_w0_smul (v : Fin Tag.G2.rank → ℤ) :
    (simple Tag.G2 g2i1 * g2OmegaBeta) • v = -v := by
  have h := g2_w0_inv_smul ((simple Tag.G2 g2i1 * g2OmegaBeta) • v)
  rw [inv_smul_smul] at h
  exact (neg_eq_iff_eq_neg.mp h.symm)

theorem signWeyl_m0 :
    SignWeyl Tag.G2 F (g2ChartA F WSL * g2ChartB F WSL) (simple Tag.G2 g2i1 * g2OmegaBeta) := by
  have h := (signWeyl_rootChart_WSL (τ := Tag.G2) (K := F) 1 g2i1).mul
    (signWeyl_rootChart_WSL (τ := Tag.G2) (K := F) g2WeylU g2i0)
  have e : (1 * simple Tag.G2 g2i1 * (1 : WeylGroup Tag.G2)⁻¹) *
      (g2WeylU * simple Tag.G2 g2i0 * g2WeylU⁻¹) = simple Tag.G2 g2i1 * g2OmegaBeta := by
    rw [inv_one, one_mul, mul_one]
    rfl
  rw [e] at h
  exact h

theorem m0_conj_chart (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) :
    ∃ η η' : F, η * η = 1 ∧ η' * η' = 1 ∧
      (∀ c : F, (g2ChartA F WSL * g2ChartB F WSL) * rootChart Tag.G2 F w i (uSL c) *
        (g2ChartA F WSL * g2ChartB F WSL)⁻¹ = rootChart Tag.G2 F w i (vSL (η * c))) ∧
      (∀ c : F, (g2ChartA F WSL * g2ChartB F WSL) * rootChart Tag.G2 F w i (vSL c) *
        (g2ChartA F WSL * g2ChartB F WSL)⁻¹ = rootChart Tag.G2 F w i (uSL (η' * c))) := by
  have hγ : IsRoot Tag.G2 (w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) :=
    IsRoot.smul (isRoot_single Tag.G2 i) w
  obtain ⟨ε₀, hε₀, hu⟩ := rootChart_uSL (K := F) (τ := Tag.G2) w i
  obtain ⟨ε₀', hε₀', hv⟩ := rootChart_vSL (K := F) (τ := Tag.G2) w i
  obtain ⟨ε₁, hε₁, h1⟩ := signWeyl_m0 (F := F) _ hγ
  obtain ⟨ε₂, hε₂, h2⟩ := signWeyl_m0 (F := F) _ (IsRoot.neg hγ)
  refine ⟨ε₀' * ε₁ * ε₀, ε₀ * ε₂ * ε₀', ?_, ?_, fun c => ?_, fun c => ?_⟩
  · calc ε₀' * ε₁ * ε₀ * (ε₀' * ε₁ * ε₀) = (ε₀' * ε₀') * (ε₁ * ε₁) * (ε₀ * ε₀) := by ring
      _ = 1 := by rw [hε₀, hε₀', hε₁]; ring
  · calc ε₀ * ε₂ * ε₀' * (ε₀ * ε₂ * ε₀') = (ε₀ * ε₀) * (ε₂ * ε₂) * (ε₀' * ε₀') := by ring
      _ = 1 := by rw [hε₀, hε₀', hε₂]; ring
  · rw [hu, h1, g2_w0_smul, hv]
    congr 1
    linear_combination (-(ε₁ * ε₀ * c)) * hε₀'
  · rw [hv, h2, g2_w0_smul, neg_neg, hu]
    congr 1
    linear_combination (-(ε₂ * ε₀' * c)) * hε₀

theorem torus_m0_conj_chart (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank)
    (b : Fin Tag.G2.rank → Fˣ) :
    ∃ η' : F, η' * η' = 1 ∧ ∀ c : F,
      (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * rootChart Tag.G2 F w i (vSL c) *
        (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL))⁻¹ =
        rootChart Tag.G2 F w i (uSL
          ((rootChar b (w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) : F) * (η' * c))) := by
  obtain ⟨η, η', hη, hη', -, hv⟩ := m0_conj_chart (F := F) w i
  refine ⟨η', hη', fun c => ?_⟩
  calc (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) *
        rootChart Tag.G2 F w i (vSL c) *
        (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL))⁻¹
      = rootDiagUnit Tag.G2 b * ((g2ChartA F WSL * g2ChartB F WSL) *
          rootChart Tag.G2 F w i (vSL c) *
          (g2ChartA F WSL * g2ChartB F WSL)⁻¹) * (rootDiagUnit Tag.G2 b)⁻¹ := by group
    _ = rootDiagUnit Tag.G2 b * rootChart Tag.G2 F w i (uSL (η' * c)) *
          (rootDiagUnit Tag.G2 b)⁻¹ := by rw [hv]
    _ = _ := by
        rw [rootDiagUnit_conj_rootChart, glConjSL_diag_uSL]

end M0

section Gen

variable {F : Type} [Field F] [Finite F]

@[expose] def NormTorusGen (F : Type) [Field F] (κ : Fˣ) : Prop :=
  ∀ H : Subgroup (SL2 F), (∀ t : Fˣ, HSL t ∈ H) →
    (∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ H) → H = ⊤

theorem normTorusGen_of_seven (h7 : 7 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (κ : Fˣ) :
    NormTorusGen F κ := fun _ hA hB => eq_top_of_normTorus_seven h7 h2 κ hA hB

theorem normTorusGen_of_five (h5 : Nat.card F = 5) (κ : Fˣ) (hκ : ∀ r : F, (κ : F) ≠ r * r) :
    NormTorusGen F κ := fun _ hA hB => eq_top_of_normTorus_five h5 κ hκ hA hB

theorem antidiag_of_inverting {Φ : SL2 F →* ModGL Tag.G2 F} (hΦinj : Function.Injective Φ)
    (hΦtor : ∀ t : Fˣ, Φ (HSL t) ∈ torusGroup Tag.G2 F) (h4 : 4 ≤ Nat.card F)
    {y : ModGL Tag.G2 F} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * Φ A * y⁻¹ = Φ (glConjSL D A))
    (hinv : ∀ t ∈ torusGroup Tag.G2 F, y * t * y⁻¹ = t⁻¹) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one_fin h4
  have h1 := hinv _ (hΦtor t)
  rw [hD, ← map_inv] at h1
  have h2 := hΦinj h1
  have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) h2
  simp only [glConjSL_coe] at h3
  have h4' : (D : Matrix (Fin 2) (Fin 2) F) * (HSL t : Matrix (Fin 2) (Fin 2) F) =
      (((HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    rw [← h3, Matrix.mul_assoc, Matrix.mul_assoc, gl_inv_mul D, Matrix.mul_one]
  have e00 := congrFun (congrFun h4' 0) 0
  have e11 := congrFun (congrFun h4' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_HSL, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two] at e00 e11
  have htne : (t : F) - (t : F)⁻¹ ≠ 0 := by
    intro h
    apply ht
    apply Units.ext
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    field_simp at h
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination h
  refine ⟨?_, ?_⟩
  · have : (D : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right htne
  · have : (D : Matrix (Fin 2) (Fin 2) F) 1 1 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right htne

omit [Finite F] in
theorem antidiag_entries {D : GL (Fin 2) F} (h00 : (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0)
    (h11 : (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∧ (D : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∧
      (D : Matrix (Fin 2) (Fin 2) F) =
        !![0, (D : Matrix (Fin 2) (Fin 2) F) 0 1; (D : Matrix (Fin 2) (Fin 2) F) 1 0, 0] := by
  have hdet : (D : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (D : Matrix (Fin 2) (Fin 2) F)).mp D.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two, h00, h11] at hdet
  refine ⟨fun h => hdet (by rw [h]; ring), fun h => hdet (by rw [h]; ring), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11]

omit [Finite F] in
theorem ratio_of_antidiag {Φ : SL2 F →* ModGL Tag.G2 F} (hΦinj : Function.Injective Φ)
    {y : ModGL Tag.G2 F} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * Φ A * y⁻¹ = Φ (glConjSL D A))
    (h00 : (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (h11 : (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    {θ : F} (hθ : y * Φ (vSL 1) * y⁻¹ = Φ (uSL θ)) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 1 = θ * (D : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  obtain ⟨-, -, hDe⟩ := antidiag_entries h00 h11
  have h1 : glConjSL D (vSL 1) = uSL θ := hΦinj (by rw [← hD, hθ])
  have h2 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) h1
  simp only [glConjSL_coe] at h2
  have h3 : (D : Matrix (Fin 2) (Fin 2) F) * ((vSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((uSL θ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    rw [← h2, Matrix.mul_assoc, Matrix.mul_assoc, gl_inv_mul D, Matrix.mul_one]
  have e := congrFun (congrFun h3 0) 0
  rw [hDe] at e
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_vSL, coe_uSL] at e
  linear_combination e

omit [Finite F] in
theorem chart_le_sup_of_antidiag {Φ : SL2 F →* ModGL Tag.G2 F}
    {P : Subgroup (ModGL Tag.G2 F)} (hTP : torusGroup Tag.G2 F ≤ P)
    (hΦmem : ∀ A, Φ A ∈ adjointGroup Tag.G2 F)
    (hΦtor : ∀ t : Fˣ, Φ (HSL t) ∈ torusGroup Tag.G2 F)
    (hΦconj : ∀ s' : Fˣ, ∃ b : Fin Tag.G2.rank → Fˣ, ∀ A : SL2 F,
      rootDiagUnit Tag.G2 b * Φ A * (rootDiagUnit Tag.G2 b)⁻¹ = Φ (glConjSL (diagGL s') A))
    {y : ModGL Tag.G2 F} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * Φ A * y⁻¹ = Φ (glConjSL D A))
    (h00 : (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (h11 : (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (hNT : ∀ κ : Fˣ, (κ : F) = (D : Matrix (Fin 2) (Fin 2) F) 0 1 *
      (D : Matrix (Fin 2) (Fin 2) F) 1 0 → NormTorusGen F κ) (A : SL2 F) :
    Φ A ∈ P ⊔ (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) := by
  set M := P ⊔ (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F)))
    with hM
  have hPM : P ≤ M := le_sup_left
  have hQM : (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) ≤ M :=
    le_sup_right
  have hTM : torusGroup Tag.G2 F ≤ M := hTP.trans hPM
  obtain ⟨hq, hr, hDeta⟩ := antidiag_entries h00 h11
  set q := (D : Matrix (Fin 2) (Fin 2) F) 0 1 with hqdef
  set r := (D : Matrix (Fin 2) (Fin 2) F) 1 0 with hrdef
  set κ : Fˣ := Units.mk0 (q * r) (mul_ne_zero hq hr) with hκ
  have hA : ∀ t : Fˣ, HSL t ∈ M.comap Φ := fun t => hTM (hΦtor t)
  have hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ M.comap Φ := by
    intro s u v h
    rw [Subgroup.mem_comap]
    have hu₀ : u * u - (q * v) * (r * v) = 1 := by
      have hk : (κ : F) = q * r := rfl
      rw [hk] at h
      linear_combination h
    let B₀ : SL2 F := ⟨!![u, q * v; r * v, u], by
      rw [det_fin_two]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      linear_combination hu₀⟩
    set s' : Fˣ := s * (Units.mk0 q hq)⁻¹ with hs'
    have hconj : normTorusSL (κ : F) s u v h = glConjSL (diagGL s') B₀ := by
      have hq0 : q ≠ 0 := hq
      have hs0 : (s : F) ≠ 0 := s.ne_zero
      have hκv : (κ : F) = q * r := rfl
      refine SL2_ext ?_ ?_ ?_ ?_
      · rw [glConjSL_diagGL_apply_00]
        simp [coe_normTorusSL, B₀]
      · rw [glConjSL_diagGL_apply_01]
        simp [coe_normTorusSL, B₀, hs']
        field_simp
      · rw [glConjSL_diagGL_apply_10]
        simp [coe_normTorusSL, B₀, hs', hκv]
        field_simp
      · rw [glConjSL_diagGL_apply_11]
        simp [coe_normTorusSL, B₀]
    have hcomm : (D : Matrix (Fin 2) (Fin 2) F) * (B₀ : Matrix (Fin 2) (Fin 2) F) =
        (B₀ : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
      rw [hDeta]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hglB : glConjSL D B₀ = B₀ :=
      Subtype.ext (by rw [glConjSL_coe, hcomm, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one])
    have hyB : y * Φ B₀ = Φ B₀ * y := by
      have := hD B₀
      rw [hglB] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have hP : Φ B₀ ∈ adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F)) :=
      ⟨hΦmem B₀, Subgroup.mem_centralizer_singleton_iff.mpr hyB.symm⟩
    obtain ⟨b, hb⟩ := hΦconj s'
    rw [hconj, ← hb B₀]
    exact mul_mem (mul_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)) (hQM hP))
      (inv_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)))
  have htop := hNT κ rfl _ hA hB
  have : A ∈ M.comap Φ := by rw [htop]; trivial
  exact this

end Gen

section Charts

variable {F : Type} [Field F]

theorem rootChart_mem_adjointGroup (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) (A : SL2 F) :
    rootChart Tag.G2 F w i A ∈ adjointGroup Tag.G2 F := by
  rw [rootChart_apply]
  exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ F w) (simpleRootSL2_mem_adjointGroup i A))
    (inv_mem (canonicalRep_mem_adjointGroup _ F w))

theorem rootChart_HSL_mem_torusGroup (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) (t : Fˣ) :
    rootChart Tag.G2 F w i (HSL t) ∈ torusGroup Tag.G2 F := by
  rw [rootChart_apply, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  exact g2_rootDiagUnit_mem_torusGroup _

theorem rootChart_conj_exists (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) {x : ℤ}
    (hγ : w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = g2vec 1 x) (s' : Fˣ) :
    ∃ b : Fin Tag.G2.rank → Fˣ, ∀ A : SL2 F,
      rootDiagUnit Tag.G2 b * rootChart Tag.G2 F w i A * (rootDiagUnit Tag.G2 b)⁻¹ =
        rootChart Tag.G2 F w i (glConjSL (diagGL s') A) := by
  refine ⟨g2tup s' 1, fun A => ?_⟩
  rw [rootDiagUnit_conj_rootChart, hγ, rootChar_g2vec]
  congr 3
  simp [g2tup_0, g2tup_1]

end Charts

section TM0

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem g2_torusGroup_commute {t s : ModGL Tag.G2 F} (ht : t ∈ torusGroup Tag.G2 F)
    (hs : s ∈ torusGroup Tag.G2 F) : t * s = s * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

omit [Finite F] in
theorem t_m0_inverts {t : ModGL Tag.G2 F} (ht : t ∈ torusGroup Tag.G2 F) {s : ModGL Tag.G2 F}
    (hs : s ∈ torusGroup Tag.G2 F) :
    (t * (g2ChartA F WSL * g2ChartB F WSL)) * s * (t * (g2ChartA F WSL * g2ChartB F WSL))⁻¹ =
      s⁻¹ := by
  have hs' : s⁻¹ ∈ torusGroup Tag.G2 F := inv_mem hs
  have hm := g2_m0_inverts (F := F) hs
  calc (t * (g2ChartA F WSL * g2ChartB F WSL)) * s * (t * (g2ChartA F WSL * g2ChartB F WSL))⁻¹
      = t * ((g2ChartA F WSL * g2ChartB F WSL) * s * (g2ChartA F WSL * g2ChartB F WSL)⁻¹) *
          t⁻¹ := by group
    _ = t * s⁻¹ * t⁻¹ := by rw [hm]
    _ = s⁻¹ := by rw [g2_torusGroup_commute ht hs']; group

theorem chart_le_sup_t_m0 (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (b : Fin Tag.G2.rank → Fˣ) (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) {x : ℤ}
    (hγ : w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = g2vec 1 x)
    {a : Fin Tag.G2.rank → Fˣ} (ha : ∀ j, a j = 1 ∨ a j = -1) (hne : a ≠ 1)
    (hker : g2vec 1 x ∈ rootCharKernel a) {P : Subgroup (ModGL Tag.G2 F)}
    (hTP : torusGroup Tag.G2 F ≤ P)
    (hNT : ∀ (κ : Fˣ) (η' : F), η' * η' = 1 →
      (∃ r : F, r ≠ 0 ∧ (κ : F) = r ^ 2 * ((rootChar b (g2vec 1 x) : F) * η')) →
        NormTorusGen F κ) (A : SL2 F) :
    rootChart Tag.G2 F w i A ∈ P ⊔ (adjointGroup Tag.G2 F ⊓
      Subgroup.centralizer ({rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)} :
        Set (ModGL Tag.G2 F))) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  set y : ModGL Tag.G2 F := rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL) with hy
  have hbT : rootDiagUnit Tag.G2 b ∈ torusGroup Tag.G2 F := g2_rootDiagUnit_mem_torusGroup b
  have hbK : rootDiagUnit Tag.G2 b ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a hbT)).1
  have hm₀K : g2ChartA F WSL * g2ChartB F WSL ∈ adjointGroup Tag.G2 F :=
    mul_mem (g2ChartA_mem WSL) (g2ChartB_mem WSL)
  have hyK : y ∈ adjointGroup Tag.G2 F := mul_mem hbK hm₀K
  have hinv : ∀ s ∈ torusGroup Tag.G2 F, y * s * y⁻¹ = s⁻¹ := fun s hs =>
    t_m0_inverts hbT hs
  have hy_a : y ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hyK, ?_⟩
    have hd := hinv _ (g2_rootDiagUnit_mem_torusGroup (K := F) a)
    have hdinv : (rootDiagUnit Tag.G2 a)⁻¹ = rootDiagUnit Tag.G2 a := by
      rw [rootDiagUnit_inv]
      congr 1
      funext j
      rcases ha j with h | h <;> simp [h]
    rw [hdinv, mul_inv_eq_iff_eq_mul] at hd
    rw [mul_inv_eq_iff_eq_mul]
    exact hd.symm
  have hΦinj := rootChart_injective hK2 (τ := Tag.G2) (K := F) w i
  have hlin : LinAct (rootChart Tag.G2 F w i) y :=
    toralCentralizer_le_linActSubgroup hodd ha hne hker hγ hy_a
  obtain ⟨D, hD⟩ := hlin
  obtain ⟨hD00, hD11⟩ := antidiag_of_inverting hΦinj (rootChart_HSL_mem_torusGroup w i) h4 hD hinv
  obtain ⟨η', hη', hv⟩ := torus_m0_conj_chart (F := F) w i b
  rw [hγ] at hv
  have hratio := ratio_of_antidiag hΦinj hD hD00 hD11 (θ := (rootChar b (g2vec 1 x) : F) * (η' * 1))
    (by rw [hy]; exact hv 1)
  obtain ⟨-, hr, -⟩ := antidiag_entries hD00 hD11
  refine chart_le_sup_of_antidiag hTP (rootChart_mem_adjointGroup w i)
    (rootChart_HSL_mem_torusGroup w i) (fun s' => rootChart_conj_exists w i hγ s') hD hD00 hD11
    (fun κ hκ => hNT κ η' hη' ⟨(D : Matrix (Fin 2) (Fin 2) F) 1 0, hr, ?_⟩) A
  rw [hκ, hratio]
  ring

end TM0

end CFSG.ClassicalInvolution.G2D4Models
