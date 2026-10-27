module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsInvCommute
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts
open CatalogueSchreierLinearTwo (semilinearAction semilinearAction_inl semilinearAction_inr
  toPGL_pglAction)
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F]

@[expose] def subPSL (K₀ : Subfield F) : Subgroup (PGammaL2 F) :=
  ((incl F).comp (psl2Sub K₀)).range

theorem ringAut_mul_comm (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  have := isCyclic_ringAut F
  exact IsCyclic.commGroup.mul_comm σ τ

theorem perfect_le_range_inl {T : Subgroup (PGammaL2 F)} (hT : ⁅T, T⁆ = T) :
    T ≤ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
  rw [← hT, commutator_le]
  intro x _ y _
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_def, SemidirectProduct.rightHom_eq_right,
    ringAut_mul_comm x.right y.right]
  group

omit [Finite F] in
theorem traceless_of_involution {T : GL (Fin 2) F}
    (ht : Matrix.ProjGenLinGroup.mk T * Matrix.ProjGenLinGroup.mk T = 1)
    (ht1 : Matrix.ProjGenLinGroup.mk T ≠ 1) :
    (T : Matrix (Fin 2) (Fin 2) F) 1 1 = -(T : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      ((T : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∨ (T : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∨
        (T : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0) := by
  have hTT : Matrix.ProjGenLinGroup.mk (T * T) = 1 := by rw [map_mul]; exact ht
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hTT
  obtain ⟨l, hl⟩ := hTT
  set t' : Matrix (Fin 2) (Fin 2) F := (T : Matrix (Fin 2) (Fin 2) F)
  have hl' : t' * t' = (l : F) • 1 := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hl
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_mul] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have e : ∀ i j, (t' * t') i j = ((l : F) • (1 : Matrix (Fin 2) (Fin 2) F)) i j :=
    fun i j => by rw [hl']
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero] at e00 e01 e10 e11
  have hns : ¬ (t' 0 1 = 0 ∧ t' 1 0 = 0 ∧ t' 0 0 = t' 1 1) := by
    rintro ⟨h01, h10, h00⟩
    apply ht1
    rw [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨t' 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00, t']
  have htr : t' 1 1 = -t' 0 0 := by
    by_contra hne
    have hs : t' 0 0 + t' 1 1 ≠ 0 := fun h => hne (by linear_combination h)
    have h01 : t' 0 1 = 0 := by
      have : t' 0 1 * (t' 0 0 + t' 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have h10 : t' 1 0 = 0 := by
      have : t' 1 0 * (t' 0 0 + t' 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have h00 : t' 0 0 = t' 1 1 := by
      have : (t' 0 0 - t' 1 1) * (t' 0 0 + t' 1 1) = 0 := by
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
    exact hns ⟨h01, h10, h00⟩
  refine ⟨htr, ?_⟩
  by_contra hall
  push Not at hall
  obtain ⟨h01, h10, h00⟩ := hall
  exact hns ⟨h01, h10, by rw [htr, h00, neg_zero]⟩

omit [Finite F] in
theorem exists_unit_of_commute {T X : GL (Fin 2) F}
    (h : Matrix.ProjGenLinGroup.mk X * Matrix.ProjGenLinGroup.mk T =
      Matrix.ProjGenLinGroup.mk T * Matrix.ProjGenLinGroup.mk X) :
    ∃ μ : Fˣ, (μ : F) • ((X : Matrix (Fin 2) (Fin 2) F) * T) =
      (T : Matrix (Fin 2) (Fin 2) F) * X := by
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ, ?_⟩
  have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hμ
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
  rw [← this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

omit [Finite F] in
theorem commutator_commute_of_units {x y t xi yi : Matrix (Fin 2) (Fin 2) F}
    (hx : x * xi = 1) (hxi : xi * x = 1) (hy : y * yi = 1) (hyi : yi * y = 1) {μ ν : F}
    (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) (hxt : μ • (x * t) = t * x) (hyt : ν • (y * t) = t * y) :
    x * y * xi * yi * t = t * (x * y * xi * yi) := by
  have hxit : xi * t = μ • (t * xi) := by
    calc xi * t = xi * (t * x) * xi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hx,
          Matrix.mul_one]
      _ = xi * (μ • (x * t)) * xi := by rw [hxt]
      _ = μ • (t * xi) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hxi, Matrix.one_mul]
  have hyit : yi * t = ν • (t * yi) := by
    calc yi * t = yi * (t * y) * yi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hy,
          Matrix.mul_one]
      _ = yi * (ν • (y * t)) * yi := by rw [hyt]
      _ = ν • (t * yi) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hyi, Matrix.one_mul]
  have hyt' : y * t = ν⁻¹ • (t * y) := by
    rw [← hyt, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hxt' : x * t = μ⁻¹ • (t * x) := by
    rw [← hxt, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have h1 : x * y * xi * yi * t = ν • (x * y * (xi * t) * yi) := by
    rw [Matrix.mul_assoc _ yi t, hyit, Matrix.mul_smul]
    simp only [Matrix.mul_assoc]
  have h2 : x * y * (xi * t) * yi = μ • (x * (y * t) * xi * yi) := by
    rw [hxit, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have h3 : x * (y * t) * xi * yi = ν⁻¹ • (x * t * y * xi * yi) := by
    rw [hyt', Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have h4 : x * t * y * xi * yi = μ⁻¹ • (t * (x * y * xi * yi)) := by
    rw [hxt', Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, h2, h3, h4, smul_smul, smul_smul, smul_smul,
    show ν * μ * ν⁻¹ * μ⁻¹ = (1 : F) by field_simp, one_smul]

omit [Finite F] in
theorem perfect_centralizer_pgl_eq_bot (h2 : (2 : F) ≠ 0) {t : PGL2 F} (ht : t * t = 1)
    (ht1 : t ≠ 1) {T : Subgroup (PGL2 F)} (hTt : ∀ x ∈ T, x * t = t * x) (hT : ⁅T, T⁆ = T) :
    T = ⊥ := by
  obtain ⟨T₀, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  obtain ⟨htr, hns⟩ := traceless_of_involution ht ht1
  set A : Subgroup (PGL2 F) :=
    (Subgroup.centralizer {T₀} : Subgroup (GL (Fin 2) F)).map Matrix.ProjGenLinGroup.mk
  have hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    have hX' : (X : Matrix (Fin 2) (Fin 2) F) * T₀ = T₀ * X :=
      congrArg Units.val (mem_centralizer_singleton_iff.mp hX)
    have hY' : (Y : Matrix (Fin 2) (Fin 2) F) * T₀ = T₀ * Y :=
      congrArg Units.val (mem_centralizer_singleton_iff.mp hY)
    exact matrix_commute_of_commute_traceless h2 htr hns hX' hY'
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ A := by
    intro x hx y hy
    obtain ⟨X, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    obtain ⟨Y, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    obtain ⟨μ, hμ⟩ := exists_unit_of_commute (hTt _ hx)
    obtain ⟨ν, hν⟩ := exists_unit_of_commute (hTt _ hy)
    refine ⟨⁅X, Y⁆, ?_, map_commutatorElement _ _ _⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply Units.ext
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    exact commutator_commute_of_units X.mul_inv X.inv_mul Y.mul_inv Y.inv_mul μ.ne_zero
      ν.ne_zero hμ hν
  have hTA : T ≤ A := by
    rw [← hT, commutator_le]
    exact hcomm
  rw [← hT, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact hA _ (hTA hy) _ (hTA hx)

theorem perfect_comap_inl {T : Subgroup (PGammaL2 F)} (hT : ⁅T, T⁆ = T) :
    (T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)).map SemidirectProduct.inl = T ∧
      ⁅T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F),
        T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)⁆ =
          T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) := by
  have hmap := map_comap_eq_self (perfect_le_range_inl hT)
  refine ⟨hmap, ?_⟩
  apply Subgroup.map_injective (SemidirectProduct.inl_injective (φ := pgl2FieldAut F))
  rw [Subgroup.map_commutator, hmap, hT]

theorem perfect_centralizer_inl_eq_bot (h2 : (2 : F) ≠ 0) {t : PGL2 F} (ht : t * t = 1)
    (ht1 : t ≠ 1) {T : Subgroup (PGammaL2 F)}
    (hTt : ∀ x ∈ T, x * SemidirectProduct.inl t = SemidirectProduct.inl t * x)
    (hT : ⁅T, T⁆ = T) : T = ⊥ := by
  obtain ⟨hmap, hT₁⟩ := perfect_comap_inl hT
  have hT₁t : ∀ x ∈ T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F),
      x * t = t * x := by
    intro x hx
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    rw [map_mul, map_mul]
    exact hTt _ hx
  rw [← hmap, perfect_centralizer_pgl_eq_bot h2 ht ht1 hT₁t hT₁, Subgroup.map_bot]

omit [Finite F] in
theorem inl_commute_inr_iff (s : PGL2 F) (σ : F ≃+* F) :
    SemidirectProduct.inl s * SemidirectProduct.inr σ =
        SemidirectProduct.inr σ * (SemidirectProduct.inl s : PGammaL2 F) ↔
      pgl2FieldAut F σ s = s := by
  rw [SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    map_one, mul_one, one_mul, and_true]
  exact eq_comm

theorem commutator_mem_range_toPGL {K₀ : Type} [Field K₀] (a b : PGL2 K₀) :
    ⁅a, b⁆ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K₀)).range := by
  obtain ⟨X, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  obtain ⟨Y, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
  rw [← map_commutatorElement, pgl2_mk_mem_psl2_range_iff_det_isSquare]
  refine ⟨1, ?_⟩
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, mul_one]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 := (Matrix.GeneralLinearGroup.det X).ne_zero
  have h2 := (Matrix.GeneralLinearGroup.det Y).ne_zero
  field_simp

theorem perfect_centralizer_inr_le {σ : F ≃+* F} {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c)
    (hσσ : ∀ x, σ (σ x) = x) {T : Subgroup (PGammaL2 F)}
    (hTσ : ∀ x ∈ T, x * SemidirectProduct.inr σ = SemidirectProduct.inr σ * x)
    (hT : ⁅T, T⁆ = T) : T ≤ subPSL K₀ := by
  obtain ⟨hmap, hT₁⟩ := perfect_comap_inl hT
  set T₁ := T.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  set R₀ := (CFSG.Glauberman.Dickson.h826_pglMap K₀.subtype).range
  have hfix : T₁ ≤ R₀ := fun s hs =>
    mem_range_of_pgl2FieldAut_fixed hK₀ h90 hσσ ((inl_commute_inr_iff s σ).mp (hTσ _ hs))
  have hR₀ : ⁅R₀, R₀⁆ ≤ ((psl2Sub K₀).range).map
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
    rw [commutator_le]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_commutatorElement]
    obtain ⟨z, hz⟩ := commutator_mem_range_toPGL a b
    rw [← hz, ← toPGL_psl2Sub]
    exact mem_map_of_mem _ ⟨z, rfl⟩
  have hT₁le : T₁ ≤ ((psl2Sub K₀).range).map
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
    rw [← hT₁]
    exact (commutator_mono hfix hfix).trans hR₀
  rw [← hmap]
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hT₁le hs
  exact ⟨z, rfl⟩

theorem ringEquiv_eq_one_or_of_fixes {σ τ : F ≃+* F} (hσ1 : σ ≠ 1) {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card F = Nat.card K₀ ^ 2)
    (hτ : ∀ x ∈ K₀, τ x = x) : τ = 1 ∨ τ = σ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hK₀2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have hfr : Module.finrank K₀ F = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := K₀) (V := F)
    rw [hcard] at h1
    exact (Nat.pow_right_injective hK₀2 h1).symm
  have hG : Nat.card (F ≃ₐ[K₀] F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hfr]
  let σA : F ≃ₐ[K₀] F := AlgEquiv.ofRingEquiv (f := σ) (fun x => (hK₀ _).mp x.2)
  let τA : F ≃ₐ[K₀] F := AlgEquiv.ofRingEquiv (f := τ) (fun x => hτ _ x.2)
  have hσA : σA ≠ 1 := by
    intro h
    apply hσ1
    ext x
    exact DFunLike.congr_fun h x
  obtain ⟨u, v, huv, huniv⟩ := Nat.card_eq_two_iff.mp hG
  have hmem : ∀ w : F ≃ₐ[K₀] F, w = u ∨ w = v := fun w => by
    have : w ∈ ({u, v} : Set (F ≃ₐ[K₀] F)) := by rw [huniv]; trivial
    simpa using this
  have hτA : τA = 1 ∨ τA = σA := by
    by_contra hne
    push Not at hne
    rcases hmem 1 with h1 | h1 <;> rcases hmem σA with h2 | h2 <;>
      rcases hmem τA with h3 | h3 <;>
      first
      | exact hσA (h2.trans h1.symm)
      | exact hne.1 (h3.trans h1.symm)
      | exact hne.2 (h3.trans h2.symm)
  rcases hτA with h | h
  · left
    ext x
    exact DFunLike.congr_fun h x
  · right
    ext x
    exact DFunLike.congr_fun h x

@[expose] def unipU {R : Type} [CommRing R] (a : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def unipL {R : Type} [CommRing R] (a : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem map_unipU (K₀ : Subfield F) (a : K₀) :
    Matrix.SpecialLinearGroup.map K₀.subtype (unipU a) = unipU (a : F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite F] in
theorem map_unipL (K₀ : Subfield F) (a : K₀) :
    Matrix.SpecialLinearGroup.map K₀.subtype (unipL a) = unipL (a : F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite F] in
theorem toPGL_psl2Sub_mk (K₀ : Subfield F) (A : Matrix.SpecialLinearGroup (Fin 2) K₀) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ (QuotientGroup.mk A)) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map K₀.subtype A)) := by
  rw [show psl2Sub K₀ (QuotientGroup.mk A) =
    QuotientGroup.mk (Matrix.SpecialLinearGroup.map K₀.subtype A) from rfl,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]

omit [Finite F] in
theorem coe_unipU (a : F) : ((unipU a : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

omit [Finite F] in
theorem coe_unipL (a : F) : ((unipL a : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![1, 0; a, 1] := rfl

omit [Finite F] in
theorem coe_toGL_unipU (a : F) : ((Matrix.SpecialLinearGroup.toGL (unipU a) : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

omit [Finite F] in
theorem coe_toGL_unipL (a : F) : ((Matrix.SpecialLinearGroup.toGL (unipL a) : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![1, 0; a, 1] := rfl

omit [Finite F] in
theorem map_toGL_unipU (τ : F ≃+* F) (a : F) :
    Matrix.GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (unipU a)) =
      Matrix.SpecialLinearGroup.toGL (unipU (τ a)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, coe_unipU]

omit [Finite F] in
theorem map_toGL_unipL (τ : F ≃+* F) (a : F) :
    Matrix.GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (unipL a)) =
      Matrix.SpecialLinearGroup.toGL (unipL (τ a)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, coe_unipL]

omit [Finite F] in
theorem eq_one_of_smul_conj (h2 : (2 : F) ≠ 0) {S : GL (Fin 2) F}
    {U : Matrix (Fin 2) (Fin 2) F} (hU : U.trace = 2) {μ : F}
    (h : μ • ((S : Matrix (Fin 2) (Fin 2) F) * U) = U * S) : μ = 1 := by
  have h1 : μ • ((S : Matrix (Fin 2) (Fin 2) F) * U * ((S⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) = U := by
    rw [← Matrix.smul_mul, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2' := congrArg Matrix.trace h1
  rw [Matrix.trace_smul, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, hU,
    smul_eq_mul] at h2'
  have : (μ - 1) * 2 = 0 := by linear_combination h2'
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)

omit [Finite F] in
theorem pgl_eq_one_of_commute_unip (h2 : (2 : F) ≠ 0) {s : PGL2 F}
    (hU : s * Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU (1 : F))) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU (1 : F))) * s)
    (hL : s * Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipL (1 : F))) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipL (1 : F))) * s) :
    s = 1 := by
  obtain ⟨S, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective s
  have htr : ∀ a : F, (Matrix.SpecialLinearGroup.toGL (unipU a) :
      Matrix (Fin 2) (Fin 2) F).trace = 2 ∧ (Matrix.SpecialLinearGroup.toGL (unipL a) :
        Matrix (Fin 2) (Fin 2) F).trace = 2 := fun a => by
    rw [coe_toGL_unipU, coe_toGL_unipL]
    constructor <;> simp [Matrix.trace, Fin.sum_univ_two] <;> norm_num
  obtain ⟨μ, hμ⟩ := exists_unit_of_commute hU
  obtain ⟨ν, hν⟩ := exists_unit_of_commute hL
  rw [eq_one_of_smul_conj h2 (htr 1).1 hμ, one_smul, coe_toGL_unipU] at hμ
  rw [eq_one_of_smul_conj h2 (htr 1).2 hν, one_smul, coe_toGL_unipL] at hν
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  set m := (S : Matrix (Fin 2) (Fin 2) F)
  have eU := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => (X 0 0, X 0 1)) hμ
  have eL := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 0) hν
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Prod.mk.injEq] at eU eL
  obtain ⟨u00, u01⟩ := eU
  refine ⟨m 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;>
    first
    | linear_combination u00 | linear_combination -u00 | linear_combination u01
    | linear_combination -u01 | linear_combination eL | linear_combination -eL

omit [Finite F] in
theorem toPGL_psl2Sub_unipU (K₀ : Subfield F) (a : K₀) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ (QuotientGroup.mk (unipU a))) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU (a : F))) := by
  rw [toPGL_psl2Sub_mk, map_unipU]

omit [Finite F] in
theorem toPGL_psl2Sub_unipL (K₀ : Subfield F) (a : K₀) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ (QuotientGroup.mk (unipL a))) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipL (a : F))) := by
  rw [toPGL_psl2Sub_mk, map_unipL]

omit [Finite F] in
theorem toPGL_semilinearAction (y : PGammaL2 F) (x : PSL2 F) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (semilinearAction F y x) =
      y.left * pgl2FieldAut F y.right (Matrix.ProjectiveSpecialLinearGroup.toPGL x) *
        y.left⁻¹ := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right y]
  rw [map_mul, semilinearAction_inl, semilinearAction_inr, MulAut.mul_apply, toPGL_pglAction,
    psl2FieldAut_toPGL]

omit [Finite F] in
theorem eq_of_mk_unipU_eq {a b : F}
    (h : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU b)) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU a))) : b = a := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hm := congrArg Units.val hu
  rw [Units.val_mul, coe_toGL_unipU, coe_toGL_unipU, Matrix.GeneralLinearGroup.coe_scalar] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h00 h01
  rw [h00, Units.val_one, mul_one] at h01
  exact h01

theorem eq_one_or_inr_of_centralizes (h2 : (2 : F) ≠ 0) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    {K₀ : Subfield F} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card F = Nat.card K₀ ^ 2)
    {y : PGammaL2 F} (hy : ∀ l ∈ subPSL K₀, y * l = l * y) :
    y = 1 ∨ y = SemidirectProduct.inr σ := by
  have hfix : ∀ s : PSL2 K₀, semilinearAction F y (psl2Sub K₀ s) = psl2Sub K₀ s := fun s =>
    (commute_incl_iff y _).mp (hy _ ⟨s, rfl⟩)
  have hfix' : ∀ s : PSL2 K₀, y.left * pgl2FieldAut F y.right
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ s)) * y.left⁻¹ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ s) := fun s => by
    rw [← toPGL_semilinearAction, hfix]
  have hτU : ∀ a : F, pgl2FieldAut F y.right
      (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU a))) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipU (y.right a))) :=
    fun a => by rw [pgl2FieldAut_mk, map_toGL_unipU]
  have hτL : ∀ a : F, pgl2FieldAut F y.right
      (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipL a))) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (unipL (y.right a))) :=
    fun a => by rw [pgl2FieldAut_mk, map_toGL_unipL]
  have hleft : y.left = 1 := by
    apply pgl_eq_one_of_commute_unip h2
    · have := hfix' (QuotientGroup.mk (unipU 1))
      rw [toPGL_psl2Sub_unipU, hτU, OneMemClass.coe_one, map_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    · have := hfix' (QuotientGroup.mk (unipL 1))
      rw [toPGL_psl2Sub_unipL, hτL, OneMemClass.coe_one, map_one, mul_inv_eq_iff_eq_mul] at this
      exact this
  have hτ : ∀ x ∈ K₀, y.right x = x := by
    intro x hx
    have := hfix' (QuotientGroup.mk (unipU ⟨x, hx⟩))
    rw [hleft, one_mul, inv_one, mul_one, toPGL_psl2Sub_unipU, hτU] at this
    exact eq_of_mk_unipU_eq this
  have hy' : y = SemidirectProduct.inr y.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right y, hleft, map_one, one_mul]
  rcases ringEquiv_eq_one_or_of_fixes hσ1 hK₀ hcard hτ with h | h
  · left
    rw [hy', h, map_one]
  · right
    rw [hy', h]

@[expose] def L2InvConcl {G : Type*} [Group G] (q : ℕ) (g : G) : Prop :=
  ∃ L : Subgroup G, L ≤ centralizer {g} ∧
    (∀ T : Subgroup G, T ≤ centralizer {g} → ⁅T, T⁆ = T → T ≤ L) ∧
    Nat.card L ≤ q * (q ^ 2 - 1) / 2 ∧
    (∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal → Odd (Nat.card N) → N = ⊥) ∧
    (Nat.card L = q * (q ^ 2 - 1) / 2 → ∀ y ∈ centralizer {g}, (∀ l ∈ L, y * l = l * y) →
      y = 1 ∨ y = g)

theorem L2InvConcl.map {G G' : Type*} [Group G] [Group G'] (Φ : G ≃* G') {q : ℕ} {g : G}
    (h : L2InvConcl q g) : L2InvConcl q (Φ g) := by
  obtain ⟨L, hLC, hperf, hcard, hodd, hcent⟩ := h
  have hC : ∀ x : G, x ∈ centralizer {g} ↔ Φ x ∈ centralizer {Φ g} := fun x => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Φ.injective.eq_iff]
  refine ⟨L.map Φ.toMonoidHom, ?_, fun T hT hTp => ?_, ?_, fun N hN hNn hNo => ?_,
    fun hc y hy hyL => ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact (hC l).mp (hLC hl)
  · have h1 : T.map Φ.symm.toMonoidHom ≤ L := by
      apply hperf
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC]
        simpa using hT hx
      · rw [← Subgroup.map_commutator, hTp]
    intro x hx
    refine ⟨Φ.symm x, h1 ⟨x, hx, rfl⟩, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective Φ.injective]
    exact hcard
  · have hN' : N.map Φ.symm.toMonoidHom ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := hN hx
      simpa using hl
    have hNn' : ((N.map Φ.symm.toMonoidHom).subgroupOf L).Normal := by
      rw [normal_subgroupOf_iff hN']
      rintro _ k ⟨n, hn, rfl⟩ hk
      refine ⟨Φ k * n * (Φ k)⁻¹, ?_, by simp⟩
      exact (normal_subgroupOf_iff hN).mp hNn n (Φ k) hn ⟨k, hk, rfl⟩
    have hNo' : Odd (Nat.card (N.map Φ.symm.toMonoidHom)) := by
      rwa [Subgroup.card_map_of_injective Φ.symm.injective]
    have := hodd _ hN' hNn' hNo'
    rw [eq_bot_iff]
    intro x hx
    have hx' : Φ.symm x ∈ N.map Φ.symm.toMonoidHom := ⟨x, hx, rfl⟩
    rw [this, mem_bot] at hx'
    rw [mem_bot, ← Φ.apply_symm_apply x, hx', map_one]
  · rw [Subgroup.card_map_of_injective Φ.injective] at hc
    have hy' : Φ.symm y ∈ centralizer {g} := by
      rw [hC]
      simpa using hy
    have hyL' : ∀ l ∈ L, Φ.symm y * l = l * Φ.symm y := by
      intro l hl
      apply Φ.injective
      rw [map_mul, map_mul, Φ.apply_symm_apply]
      exact hyL _ ⟨l, hl, rfl⟩
    rcases hcent hc _ hy' hyL' with h1 | h1
    · left
      rw [← Φ.apply_symm_apply y, h1, map_one]
    · right
      rw [← Φ.apply_symm_apply y, h1]

theorem ordL2_ge {q : ℕ} (hq : 5 ≤ q) : 60 ≤ q * (q ^ 2 - 1) / 2 := by
  have h1 : 25 ≤ q ^ 2 := by nlinarith
  have h2 : 120 ≤ q * (q ^ 2 - 1) := by
    have : 24 ≤ q ^ 2 - 1 := by omega
    nlinarith
  omega

theorem l2InvConcl_inl (h2 : (2 : F) ≠ 0) {q : ℕ} (hq : 5 ≤ q) {t : PGL2 F} (ht : t * t = 1)
    (ht1 : t ≠ 1) : L2InvConcl q (SemidirectProduct.inl t : PGammaL2 F) := by
  refine ⟨⊥, bot_le, fun T hT hTp => ?_, ?_, fun N hN _ _ => le_bot_iff.mp hN, fun hc => ?_⟩
  · rw [perfect_centralizer_inl_eq_bot h2 ht ht1 (fun x hx => mem_centralizer_singleton_iff.mp
      (hT hx)) hTp]
  · rw [Subgroup.card_bot]
    have := ordL2_ge hq
    omega
  · rw [Subgroup.card_bot] at hc
    have := ordL2_ge hq
    omega

theorem l2InvConcl_inr (h2 : (2 : F) ≠ 0) {q : ℕ} (hq : 5 ≤ q) (hF : Nat.card F = q ^ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    L2InvConcl q (SemidirectProduct.inr σ : PGammaL2 F) := by
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    have := congrArg (fun τ : F ≃+* F => τ x) h1
    simpa using this
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    norm_num at hσ
  have hK₀q : Nat.card K₀ = q := by
    rw [hF] at hcard
    exact (Nat.pow_left_injective two_ne_zero hcard).symm
  have hqodd : Odd q := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    apply h2
    have : Fintype F := Fintype.ofFinite F
    have hc2 : ringChar F = 2 := (FiniteField.even_card_iff_char_two (F := F)).mpr (by
      rw [← Nat.card_eq_fintype_card, hF]
      exact Nat.even_iff.mp (hev.pow_of_ne_zero two_ne_zero))
    have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [hc2])
    exact_mod_cast h3
  have hpp : IsOddPrimePower (Nat.card K₀) := isOddPrimePower_of_odd_card K₀ (hK₀q ▸ hqodd)
  have hinj : Function.Injective ((incl F).comp (psl2Sub K₀)) :=
    (incl_injective F).comp (psl2Sub_injective K₀)
  have hLcard : Nat.card (subPSL K₀) = q * (q ^ 2 - 1) / 2 := by
    rw [subPSL, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, psl2_card_formula _ hpp,
      hK₀q]
  refine ⟨subPSL K₀, ?_, fun T hT hTp => ?_, hLcard.le, fun N hN hNn hNo => ?_,
    fun _ y _ hyL => eq_one_or_inr_of_centralizes h2 hσ1 hK₀ hcard hyL⟩
  · rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff]
    symm
    rw [MonoidHom.comp_apply, commute_incl_iff, semilinearAction_inr]
    exact psl2Sub_mem_fieldCent hK₀ s
  · exact perfect_centralizer_inr_le hK₀ h90 hσσ (fun x hx => mem_centralizer_singleton_iff.mp
      (hT hx)) hTp
  · have : IsSimpleGroup (subPSL K₀) :=
      (MonoidHom.ofInjective hinj).isSimpleGroup_congr.mp
        (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
    rcases hNn.eq_bot_or_eq_top with h | h
    · rw [subgroupOf_eq_bot] at h
      exact le_bot_iff.mp (h le_rfl hN)
    · exfalso
      rw [subgroupOf_eq_top] at h
      have hNL : N = subPSL K₀ := le_antisymm hN h
      rw [hNL, hLcard, ← hK₀q, ← psl2_card_formula _ hpp] at hNo
      exact Nat.not_even_iff_odd.mpr hNo (even_psl2_card hpp)

theorem l2InvConcl_pGammaL2 (h2 : (2 : F) ≠ 0) (hpp : IsOddPrimePower (Nat.card F)) {q : ℕ}
    (hq : 5 ≤ q) (hF : Nat.card F = q ^ 2) {g : PGammaL2 F} (hg : g * g = 1) (hg1 : g ≠ 1) :
    L2InvConcl q g := by
  by_cases hr : g.right = 1
  · have hgt : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hr
    have ht2 : g.left * g.left = 1 := by
      have := congrArg SemidirectProduct.left hg
      simpa [hr] using this
    have ht1 : g.left ≠ 1 := by
      intro h
      apply hg1
      rw [hgt, h, map_one]
    rw [hgt]
    exact l2InvConcl_inl h2 hq ht2 ht1
  · have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg) hg1
    obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hpp g hgo hr
    have hσσ : g.right * g.right = 1 := by
      have := congrArg SemidirectProduct.right hg
      simpa using this
    have hσ : orderOf g.right = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hr
    have h1 := (l2InvConcl_inr h2 hq hF hσ).map (MulAut.conj (SemidirectProduct.inl C))
    have hg' : MulAut.conj (SemidirectProduct.inl C) (SemidirectProduct.inr g.right) = g := by
      rw [MulAut.conj_apply, ← hC]
      group
    rwa [hg'] at h1

end CFSG.ComponentClassification.CatFactsSp4
