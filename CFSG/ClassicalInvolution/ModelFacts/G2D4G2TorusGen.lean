module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Gen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_conj_rootChart (w : WeylGroup τ) (i : Fin τ.rank) (b : Fin τ.rank → Kˣ)
    (A : SL2 K) :
    rootDiagUnit τ b * rootChart τ K w i A * (rootDiagUnit τ b)⁻¹ =
      rootChart τ K w i
        (glConjSL (diagGL (rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ)))) A) := by
  obtain ⟨ε, hε, hu⟩ := rootChart_uSL (K := K) w i
  obtain ⟨ε', hε', hv⟩ := rootChart_vSL (K := K) w i
  have hγ : IsRoot τ (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ i) w
  refine conj_eq_of_generators (Φ := rootChart τ K w i)
    (glConjSL (diagGL (rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ))))) (fun c => ?_)
    (fun c => ?_) A
  · rw [hu, glConjSL_diag_uSL, hu, rootDiagUnit_conj_pinnedX b hγ]
    congr 1
    ring
  · rw [hv, glConjSL_diag_vSL, hv, rootDiagUnit_conj_pinnedX b (IsRoot.neg hγ), rootChar_neg_inv]
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    ring

theorem rootChart_one (i : Fin τ.rank) : rootChart τ K 1 i = simpleRootSL2 τ K i :=
  MonoidHom.ext fun A => by simp [rootChart, canonicalRep_one]

end Torus

section G2Torus

variable {K : Type} [Field K]

theorem g2_rootDiagUnit_mem_torusGroup (b : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit Tag.G2 b ∈ torusGroup Tag.G2 K := by
  have c00 : Tag.G2.cartan g2i0 g2i0 = 2 := by decide
  have c01 : Tag.G2.cartan g2i0 g2i1 = -1 := by decide
  have c10 : Tag.G2.cartan g2i1 g2i0 = -3 := by decide
  have c11 : Tag.G2.cartan g2i1 g2i1 = 2 := by decide
  have h : rootDiagUnit Tag.G2 b = torusElt Tag.G2 K g2i0 (b g2i0 ^ 2 * b g2i1 ^ 3) *
      torusElt Tag.G2 K g2i1 (b g2i0 * b g2i1 ^ 2) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    fin_cases j
    · show b g2i0 = (b g2i0 ^ 2 * b g2i1 ^ 3) ^ Tag.G2.cartan g2i0 g2i0 *
        (b g2i0 * b g2i1 ^ 2) ^ Tag.G2.cartan g2i1 g2i0
      rw [c00, c10]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := (b g2i0).ne_zero
      have := (b g2i1).ne_zero
      field_simp
    · show b g2i1 = (b g2i0 ^ 2 * b g2i1 ^ 3) ^ Tag.G2.cartan g2i0 g2i1 *
        (b g2i0 * b g2i1 ^ 2) ^ Tag.G2.cartan g2i1 g2i1
      rw [c01, c11]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := (b g2i0).ne_zero
      have := (b g2i1).ne_zero
      field_simp
  rw [h]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

end G2Torus

section Diag

variable {F : Type} [Field F]

theorem exists_unit_sq_ne_one_fin [Finite F] (h4 : 4 ≤ Nat.card F) : ∃ t : Fˣ, t ^ 2 ≠ 1 := by
  let f : Polynomial F := Polynomial.X * (Polynomial.X ^ 2 - 1)
  have hf : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 3) h
    simp [f, Polynomial.coeff_X_mul, Polynomial.coeff_X_pow, Polynomial.coeff_one] at this
  have hdeg : f.natDegree < Nat.card F := by
    have : f.natDegree ≤ 3 := by simp only [f]; compute_degree
    omega
  obtain ⟨m, hm⟩ := exists_eval_ne_zero_fin f hf hdeg
  have hm' : m * (m ^ 2 - 1) ≠ 0 := by simpa [f] using hm
  refine ⟨Units.mk0 m (left_ne_zero_of_mul hm'), fun h => ?_⟩
  have := congrArg Units.val h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
  exact (right_ne_zero_of_mul hm') (by rw [this]; ring)

theorem coe_diagGL_two (s : Fˣ) : ((diagGL s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![(s : F), 0; 0, 1] := rfl

theorem coe_diagGL_inv_two (s : Fˣ) :
    (((diagGL s)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((s⁻¹ : Fˣ) : F), 0; 0, 1] := rfl

theorem glConjSL_diagGL_apply (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (s : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1;
        ((s⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0,
        (A : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  rw [glConjSL_coe, coe_diagGL_two, coe_diagGL_inv_two,
    Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
  simp only [Matrix.mul_fin_two]
  have hs : (s : F) ≠ 0 := s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem glConjSL_diagGL_apply_00 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 0) 0
  simpa using this

theorem glConjSL_diagGL_apply_01 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (s : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 0) 1
  simpa using this

theorem glConjSL_diagGL_apply_10 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      ((s⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 1) 0
  simpa using this

theorem glConjSL_diagGL_apply_11 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 1) 1
  simpa using this

end Diag

section Gen

variable {F : Type} [Field F] [Finite F]

theorem chart_matrix_antidiag (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {y : ModGL Tag.G2 F} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * rootChart Tag.G2 F 1 g2i0 A * y⁻¹ =
      rootChart Tag.G2 F 1 g2i0 (glConjSL D A))
    (hinv : ∀ t ∈ torusGroup Tag.G2 F, y * t * y⁻¹ = t⁻¹) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one_fin h4
  have hΦinj : Function.Injective (rootChart Tag.G2 F 1 g2i0) := rootChart_injective hK2 1 g2i0
  have hmem : rootChart Tag.G2 F 1 g2i0 (HSL t) ∈ torusGroup Tag.G2 F := by
    rw [rootChart_one, simpleRootSL2_HSL]
    exact torusElt_mem_torusGroup _ _
  have h1 := hinv _ hmem
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

theorem adjointGroup_le_toralCentralizer_sup (hodd : Odd (Nat.card F)) (h11 : 11 ≤ Nat.card F)
    {y : ModGL Tag.G2 F} (hy : y ∈ adjointGroup Tag.G2 F)
    (hinv : ∀ t ∈ torusGroup Tag.G2 F, y * t * y⁻¹ = t⁻¹) :
    adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
  set M := toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) with hM
  have hXM : toralCentralizer Tag.G2 F ![-1, 1] ≤ M := le_sup_left
  have hPM : (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) ≤ M :=
    le_sup_right
  have hTM : torusGroup Tag.G2 F ≤ M := (torusGroup_le_toralCentralizer _).trans hXM
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : Fin Tag.G2.rank → Fˣ, a₂ = ![1, -1] := ⟨_, rfl⟩
  have ha₂0 : a₂ g2i0 = 1 := by rw [ha₂]; rfl
  have ha₂1 : a₂ g2i1 = -1 := by rw [ha₂]; rfl
  have ha₂sq : ∀ i, a₂ i = 1 ∨ a₂ i = -1 := by
    intro i; fin_cases i
    · exact Or.inl ha₂0
    · exact Or.inr ha₂1
  have ha₂ne : a₂ ≠ 1 := by
    intro h
    have := congrFun h g2i1
    rw [ha₂1] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val this)
  have hy₂ : y ∈ toralCentralizer Tag.G2 F a₂ := by
    rw [mem_toralCentralizer]
    refine ⟨hy, ?_⟩
    have hd := hinv _ (g2_rootDiagUnit_mem_torusGroup (K := F) a₂)
    have hdinv : (rootDiagUnit Tag.G2 a₂)⁻¹ = rootDiagUnit Tag.G2 a₂ := by
      rw [rootDiagUnit_inv]
      congr 1
      funext i
      rcases ha₂sq i with h | h <;> simp [h]
    rw [hdinv, mul_inv_eq_iff_eq_mul] at hd
    rw [mul_inv_eq_iff_eq_mul]
    exact hd.symm
  have hΦinj := rootChart_injective hK2 (τ := Tag.G2) (K := F) 1 g2i0
  have hΦlin : LinAct (rootChart Tag.G2 F 1 g2i0) y := by
    refine toralCentralizer_le_linActSubgroup hodd ha₂sq ha₂ne (γ := Pi.single g2i0 1)
      ⟨isRoot_single _ _, ?_⟩ (w := 1) (i := g2i0) (one_smul _ _) hy₂
    rw [rootChar_single_g2, ha₂0]
  obtain ⟨D, hD⟩ := hΦlin
  obtain ⟨hD00, hD11⟩ := chart_matrix_antidiag hodd (by omega) hD hinv
  have hdet : (D : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (D : Matrix (Fin 2) (Fin 2) F)).mp D.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two, hD00, hD11] at hdet
  have hq : (D : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hr : (D : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  set q := (D : Matrix (Fin 2) (Fin 2) F) 0 1 with hqdef
  set r := (D : Matrix (Fin 2) (Fin 2) F) 1 0 with hrdef
  have hDeta : (D : Matrix (Fin 2) (Fin 2) F) = !![0, q; r, 0] := by
    rw [Matrix.eta_fin_two (D : Matrix (Fin 2) (Fin 2) F), hD00, hD11]
  set κ : Fˣ := Units.mk0 (q * r) (mul_ne_zero hq hr) with hκ
  have hΦmem : ∀ A : SL2 F, rootChart Tag.G2 F 1 g2i0 A ∈ adjointGroup Tag.G2 F := fun A => by
    rw [rootChart_one]; exact simpleRootSL2_mem_adjointGroup g2i0 A
  have hA : ∀ t : Fˣ, HSL t ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by
    intro t
    rw [Subgroup.mem_comap, rootChart_one, simpleRootSL2_HSL]
    exact hTM (torusElt_mem_torusGroup _ _)
  have hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by
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
    have hyB : y * rootChart Tag.G2 F 1 g2i0 B₀ = rootChart Tag.G2 F 1 g2i0 B₀ * y := by
      have := hD B₀
      rw [hglB] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have hP : rootChart Tag.G2 F 1 g2i0 B₀ ∈
        adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F)) :=
      ⟨hΦmem B₀, Subgroup.mem_centralizer_singleton_iff.mpr hyB.symm⟩
    have hd := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i0 (fun _ => s') B₀
    rw [one_smul, rootChar_single_g2] at hd
    rw [hconj, ← show (fun _ : Fin Tag.G2.rank => s') g2i0 = s' from rfl]
    rw [← hd]
    exact mul_mem (mul_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)) (hPM hP))
      (inv_mem (hTM (g2_rootDiagUnit_mem_torusGroup _)))
  have htop := eq_top_of_normTorus h11 h2 κ hA hB
  have hall : ∀ A : SL2 F, rootChart Tag.G2 F 1 g2i0 A ∈ M := fun A => by
    have : A ∈ M.comap (rootChart Tag.G2 F 1 g2i0) := by rw [htop]; trivial
    exact this
  rw [adjointGroup_eq_iSup_rootPair_single]
  refine iSup_le fun i => ?_
  fin_cases i
  · rw [← range_simpleRootSL2_eq_rootPair, ← rootChart_one (K := F) (τ := Tag.G2)]
    rintro _ ⟨A, rfl⟩
    exact hall A
  · have hker : (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ) ∈
        rootCharKernel (τ := Tag.G2) (K := F) ![-1, 1] :=
      ⟨isRoot_single _ _, (rootChar_single_g2 _ _).trans rfl⟩
    exact (rootPair_le_toralCentralizer hker).trans hXM

end Gen

section Model

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem map_centralizer_g2_eq_inf (y : ↥(adjointGroup Tag.G2 F)) :
    (Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F))).map
        (adjointGroup Tag.G2 F).subtype =
      adjointGroup Tag.G2 F ⊓
        Subgroup.centralizer ({(y : ModGL Tag.G2 F)} : Set (ModGL Tag.G2 F)) := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact Subtype.ext hc

theorem centralizer_sup_eq_top_of_inverting (hodd : Odd (Nat.card F)) (h11 : 11 ≤ Nat.card F)
    {c₁ y : ↥(adjointGroup Tag.G2 F)} (h₁ : (c₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1])
    (hinv : ∀ t ∈ torusGroup Tag.G2 F,
      (y : ModGL Tag.G2 F) * t * (y : ModGL Tag.G2 F)⁻¹ = t⁻¹) :
    Subgroup.centralizer ({c₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  apply Subgroup.map_injective (adjointGroup Tag.G2 F).subtype_injective
  rw [Subgroup.map_sup, map_centralizer_g2_eq_toralCentralizer h₁, map_centralizer_g2_eq_inf,
    Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (sup_le (fun x hx => (mem_toralCentralizer.mp hx).1) inf_le_left) ?_
  exact adjointGroup_le_toralCentralizer_sup hodd h11 y.2 hinv

end Model

end CFSG.ClassicalInvolution.G2D4Models
