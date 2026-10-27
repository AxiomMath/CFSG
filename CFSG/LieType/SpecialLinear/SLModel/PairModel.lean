module

public import CFSG.LieType.SpecialLinear.SLModel.Models
public import CFSG.LieType.SpecialLinear.SLModel.MatrixModel
public import CFSG.LieType.SpecialLinear.PairedTensor.Rank
public import CFSG.LieType.SpecialLinear.PairedTensor.Quadratic
public import CFSG.LieType.SpecialLinear.PairedTensor.FixedField
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.NaturalPair
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Module _root_.Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.HardMathSupport.GuralnickMalle
open CFSG.LieType.SpecialLinear
open CFSG.Semidihedral.FixedFieldData
open scoped Kronecker

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

private noncomputable def minorMatrixHom (j : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F →*
      Matrix (Set.powersetCard (Fin (m + 1)) j)
        (Set.powersetCard (Fin (m + 1)) j) F where
  toFun g := minorMatrix j g
  map_one' := minorMatrix_one j
  map_mul' g h := minorMatrix_mul j g h

private noncomputable def pairN {j : ℕ}
    (e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j) (τ : F ≃+* F) :
    Matrix (Set.powersetCard (Fin (m + 1)) j)
        (Set.powersetCard (Fin (m + 1)) j) F →*
      Matrix (Fin (m + 1)) (Fin (m + 1)) F where
  toFun M := (M.submatrix e e).map τ
  map_one' := by
    rw [Matrix.submatrix_one_equiv (α := F) e,
      Matrix.map_one (⇑τ) (map_zero τ) (map_one τ)]
  map_mul' M N := by
    rw [← Matrix.submatrix_mul_equiv (e₂ := e), Matrix.map_mul]

private noncomputable def pairMat {j : ℕ}
    (e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j) (τ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  pairN e τ (minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F))

private noncomputable def pairGL {j : ℕ}
    (e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j) (τ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Matrix.GeneralLinearGroup (Fin (m + 1)) F :=
  (Units.map (pairN e τ)).comp
    ((Units.map (minorMatrixHom (m := m) (F := F) j)).comp
      (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := F)))

omit [Fintype F] [CharP F 2] in
private lemma pairGL_coe {j : ℕ}
    (e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j) (τ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ((pairGL e τ g : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = pairMat e τ g := by
  rw [pairGL, MonoidHom.comp_apply, Units.coe_map, MonoidHom.comp_apply, Units.coe_map,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

omit [Fintype F] in
private lemma exists_submatrix_minorMatrix (hm : 1 ≤ m) {j : ℕ} (hj : j = 1 ∨ j = m) :
    ∃ e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j,
      (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
        (minorMatrix j g).submatrix e e = g) ∨
      (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F, g.det = 1 →
        (minorMatrix j g).submatrix e e = Matrix.transpose (g⁻¹)) := by
  rcases hj with hj1 | hjm
  · rw [hj1]
    exact ⟨powersetCardOneEquiv.symm, Or.inl fun g => minorMatrix_one_submatrix g⟩
  · rw [hjm]
    exact ⟨powersetCardOneEquiv.symm.trans (complEquiv (by omega : 1 ≤ m + 1)),
      Or.inr fun g hg => by
        simpa using minorMatrix_sub_one_submatrix (k := F) (by omega : 1 ≤ m + 1) (g := g) hg⟩

omit [Fintype F] [CharP F 2] in
private lemma pairMat_eq_one {j : ℕ}
    {e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j} {τ : F ≃+* F}
    (hcase : (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
        (minorMatrix j g).submatrix e e = g) ∨
      (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F, g.det = 1 →
        (minorMatrix j g).submatrix e e = Matrix.transpose (g⁻¹)))
    {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (h : pairMat e τ g = 1) : g = 1 := by
  have h1 : (minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).submatrix e e = 1 := by
    have h' : ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).submatrix e e).map
        (⇑τ) = 1 := by
      simpa [pairMat, pairN] using h
    have h'' : ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).submatrix e e).map
        (⇑τ) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (⇑τ) := by
      rw [show (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (⇑τ) = 1 from
        Matrix.map_one (⇑τ) (map_zero τ) (map_one τ)]
      exact h'
    exact Matrix.map_injective τ.injective h''
  rcases hcase with hcase | hcase
  · have hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← hcase (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)]
      exact h1
    exact Matrix.SpecialLinearGroup.toGL_injective (by
      apply Units.ext
      simpa using hg)
  · have hg : Matrix.transpose (((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F))⁻¹) = 1 := by
      rw [← hcase (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        (Matrix.SpecialLinearGroup.det_coe g)]
      exact h1
    have hg' : ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F))⁻¹ = 1 := by
      have := congrArg Matrix.transpose hg
      simpa [Matrix.transpose_transpose] using this
    have hg'' : ((g : Matrix.GeneralLinearGroup (Fin (m + 1)) F))⁻¹ = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hg']
      rfl
    have hgl : (g : Matrix.GeneralLinearGroup (Fin (m + 1)) F) = 1 := inv_eq_one.mp hg''
    exact Matrix.SpecialLinearGroup.toGL_injective (by simpa using hgl)

omit [Fintype F] [CharP F 2] in
private lemma pairGL_injective {j : ℕ}
    {e : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j} {τ : F ≃+* F}
    (hcase : (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
        (minorMatrix j g).submatrix e e = g) ∨
      (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) F, g.det = 1 →
        (minorMatrix j g).submatrix e e = Matrix.transpose (g⁻¹))) :
    Function.Injective (pairGL (m := m) (F := F) (j := j) e τ) := by
  intro g h hgh
  have h1 : pairGL (m := m) (F := F) (j := j) e τ (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  have hmat : pairMat (m := m) (F := F) (j := j) e τ (g * h⁻¹) = 1 := by
    rw [← pairGL_coe, h1]
    rfl
  have h2 : g * h⁻¹ = 1 := pairMat_eq_one hcase hmat
  calc g = g * h⁻¹ * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = 1 * h := by rw [h2]
    _ = h := one_mul h


private noncomputable def pairM {j : ℕ}
    (_ee : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j)
    (τ₁ τ₂ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j)
      (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j) F :=
  (minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map τ₁ ⊗ₖ
    (minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map τ₂

omit [Fintype F] [CharP F 2] in
private lemma pairM_submatrix {j : ℕ}
    (ee : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j)
    {τ₁ τ₂ σ : F ≃+* F} (hσ : τ₁.trans σ = τ₂)
    (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    (pairM ee τ₁ τ₂ g).submatrix (ee.prodCongr ee) (ee.prodCongr ee) =
      pairMat ee τ₁ g ⊗ₖ (pairMat ee τ₁ g).map σ := by
  have hkron : (pairM ee τ₁ τ₂ g).submatrix (ee.prodCongr ee) (ee.prodCongr ee) =
      ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map τ₁).submatrix ee ee ⊗ₖ
        ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map τ₂).submatrix ee ee := by
    rw [pairM]
    exact (Matrix.kroneckerMap_submatrix_submatrix (· * ·) _ _ ee ee ee ee).symm
  rw [hkron, Matrix.submatrix_map, Matrix.submatrix_map]
  rw [show ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).submatrix ee ee).map τ₁ =
      pairMat ee τ₁ g from rfl]
  congr 1
  rw [show pairMat ee τ₁ g =
      ((minorMatrix j (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).submatrix ee ee).map τ₁ from rfl]
  rw [Matrix.map_map]
  congr 1
  funext x
  rw [← hσ]
  rfl

omit [Fintype F] [CharP F 2] in
private lemma pairM_submatrix_sub_one {j : ℕ}
    (ee : Fin (m + 1) ≃ Set.powersetCard (Fin (m + 1)) j)
    {τ₁ τ₂ σ : F ≃+* F} (hσ : τ₁.trans σ = τ₂)
    (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ((pairM ee τ₁ τ₂ g - 1).submatrix (ee.prodCongr ee) (ee.prodCongr ee)) =
      pairMat ee τ₁ g ⊗ₖ (pairMat ee τ₁ g).map σ - 1 := by
  have h1 : (pairM ee τ₁ τ₂ g - 1).submatrix (ee.prodCongr ee) (ee.prodCongr ee) =
      (pairM ee τ₁ τ₂ g).submatrix (ee.prodCongr ee) (ee.prodCongr ee) - 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : ¬ (Prod.map (⇑ee) (⇑ee) i = Prod.map (⇑ee) (⇑ee) j) := by
        intro h
        apply hij
        exact Prod.ext (ee.injective (congrArg Prod.fst h)) (ee.injective (congrArg Prod.snd h))
      simp [hij, hne]
  rw [h1, pairM_submatrix ee hσ g]

theorem two_mul_le_finrank_range_slModelRep_pair (hm : 1 ≤ m)
    (ε : Fin f → Finset (Fin (m + 1))) {r₁ r₂ : Fin f} (hr : r₁ ≠ r₂) {j : Fin (m + 1)}
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) = m) (h₁ : ε r₁ = {j}) (h₂ : ε r₂ = {j})
    (hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅)
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    2 * m ≤ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  classical
  obtain ⟨ee, hcase⟩ := exists_submatrix_minorMatrix (F := F) hm hj
  let τ₁ : F ≃+* F := iterateFrobeniusEquiv F 2 r₁
  let τ₂ : F ≃+* F := iterateFrobeniusEquiv F 2 r₂
  let σ : F ≃+* F := τ₁.symm.trans τ₂
  have hσ : τ₁.trans σ = τ₂ := by
    ext x
    simp [σ, RingEquiv.trans_apply]
  obtain ⟨β, hβ⟩ := exists_equiv_pair (F := F) (k := k) (m := m) (f := f) ε hr h₁ h₂ hrest
  have hMβ : ∀ g v, β (slModelRep (F := F) (k := k) ε g v) =
      Matrix.mulVec ((pairM ee τ₁ τ₂ g).map (algebraMap F k)) (β v) := hβ
  have hrank := finrank_range_sub_one_eq_rank (σ := slModelRep (F := F) (k := k) ε)
    β (pairM ee τ₁ τ₂) hMβ u
  have hMr : Matrix.rank (pairM ee τ₁ τ₂ u - 1) =
      Matrix.rank (pairMat ee τ₁ u ⊗ₖ (pairMat ee τ₁ u).map σ - 1) := by
    calc Matrix.rank (pairM ee τ₁ τ₂ u - 1)
        = Matrix.rank ((pairM ee τ₁ τ₂ u - 1).submatrix
            (ee.prodCongr ee) (ee.prodCongr ee)) :=
          (Matrix.rank_submatrix _ (ee.prodCongr ee) (ee.prodCongr ee)).symm
      _ = Matrix.rank (pairMat ee τ₁ u ⊗ₖ (pairMat ee τ₁ u).map σ - 1) := by
          rw [pairM_submatrix_sub_one ee hσ u]
  let a : Matrix.GeneralLinearGroup (Fin (m + 1)) F := pairGL ee τ₁ u
  have ha_coe : ((a : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = pairMat ee τ₁ u := pairGL_coe ee τ₁ u
  have ha : a * a = 1 := by
    rw [show a * a = pairGL ee τ₁ (u * u) from (map_mul (pairGL ee τ₁) u u).symm, hu,
      map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hu1
    have hN : pairMat (m := m) (F := F) (j := (j : ℕ)) ee τ₁ u = 1 := by
      rw [← pairGL_coe (m := m) (F := F) (j := (j : ℕ)) ee τ₁ u]
      change ((a : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1
      rw [h]
      rfl
    exact pairMat_eq_one hcase hN
  have hbound := two_mul_sub_two_le_rank_kronecker_map_sub_one σ a ha ha1
  rw [ha_coe] at hbound
  rw [hrank, hMr]
  omega

theorem sixteen_lt_pow_finrank_range_slModelRep_pair (hm : 3 ≤ m)
    (ε : Fin f → Finset (Fin (m + 1))) {r₁ r₂ : Fin f} (hr : r₁ ≠ r₂) {j : Fin (m + 1)}
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) = m) (h₁ : ε r₁ = {j}) (h₂ : ε r₂ = {j})
    (hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) {N : ℕ} (hN : 2 ≤ N)
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    16 < N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  have hrank := two_mul_le_finrank_range_slModelRep_pair (m := m) (f := f) (k := k) (by omega)
    ε hr hj h₁ h₂ hrest hu hu1
  have h6 : 6 ≤ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
    omega
  calc 16 < 2 ^ 6 := by norm_num
    _ ≤ 2 ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_right (by norm_num) h6
    _ ≤ N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_left hN _


theorem card_le_of_slModelRep_pair (hm : 1 ≤ m) (hF : Fintype.card F = 2 ^ f) {e : ℕ}
    (hfe : f = 2 * e) (ε : Fin f → Finset (Fin (m + 1))) {r₁ r₂ : Fin f}
    (hr₂ : (r₂ : ℕ) = (r₁ + e) % f) {j : Fin (m + 1)} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = m)
    (h₁ : ε r₁ = {j}) (h₂ : ε r₂ = {j}) (hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)}
    (hP : ∀ a ∈ P, a * a = 1)
    (hquad : ∀ a ∈ P, ∀ b ∈ P,
      (slModelRep (F := F) (k := k) ε a - 1) * (slModelRep (F := F) (k := k) ε b - 1) = 0) :
    Nat.card P ≤ 2 ^ e := by
  classical
  have hfpos : 0 < f := r₁.pos
  have hepos : 0 < e := by omega
  have hr : r₁ ≠ r₂ := by
    rintro rfl
    have hmod : (r₁ : ℕ) = ((r₁ : ℕ) + e) % f := hr₂
    have hdiv := Nat.div_add_mod ((r₁ : ℕ) + e) f
    rw [show ((r₁ : ℕ) + e) % f = (r₁ : ℕ) from hmod.symm] at hdiv
    have hdiv' : f * (((r₁ : ℕ) + e) / f) + (r₁ : ℕ) = e + (r₁ : ℕ) := by
      rw [hdiv, Nat.add_comm (r₁ : ℕ) e]
    have hk : f * (((r₁ : ℕ) + e) / f) = e := Nat.add_right_cancel hdiv'
    have hdvd : f ∣ e := ⟨_, hk.symm⟩
    have hle := Nat.le_of_dvd hepos hdvd
    omega
  obtain ⟨ee, hcase⟩ := exists_submatrix_minorMatrix (F := F) hm hj
  let τ₁ : F ≃+* F := iterateFrobeniusEquiv F 2 r₁
  let τ₂ : F ≃+* F := iterateFrobeniusEquiv F 2 r₂
  let σ : F ≃+* F := τ₁.symm.trans τ₂
  have hσ : τ₁.trans σ = τ₂ := by
    ext x
    simp [σ, RingEquiv.trans_apply]
  obtain ⟨β, hβ⟩ := exists_equiv_pair (F := F) (k := k) (m := m) (f := f) ε hr h₁ h₂ hrest
  have hMβ : ∀ g v, β (slModelRep (F := F) (k := k) ε g v) =
      Matrix.mulVec ((pairM ee τ₁ τ₂ g).map (algebraMap F k)) (β v) := hβ
  let ρ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →*
      Matrix.GeneralLinearGroup (Fin (m + 1)) F := pairGL ee τ₁
  let A : Subgroup (Matrix.GeneralLinearGroup (Fin (m + 1)) F) := P.map ρ
  have hρ_inj : Function.Injective ρ := pairGL_injective hcase
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    rintro a ⟨g, hg, rfl⟩
    rw [← map_mul, show g * g = 1 from hP g hg, map_one]
  have hqA : ∀ a ∈ A, ∀ b ∈ A,
      ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ⊗ₖ
          ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ) - 1) *
        ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ⊗ₖ
          ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ) - 1) = 0 := by
    rintro a ⟨g, hg, rfl⟩ b ⟨h, hh, rfl⟩
    have hpq : (pairM ee τ₁ τ₂ g - 1) * (pairM ee τ₁ τ₂ h - 1) = 0 :=
      sub_one_mul_sub_one_eq_zero_of_model (σ := slModelRep (F := F) (k := k) ε)
        β (pairM ee τ₁ τ₂) hMβ (hquad g hg h hh)
    have hpq' : ((pairM ee τ₁ τ₂ g - 1).submatrix (ee.prodCongr ee) (ee.prodCongr ee)) *
        ((pairM ee τ₁ τ₂ h - 1).submatrix (ee.prodCongr ee) (ee.prodCongr ee)) = 0 := by
      have h := congrArg (fun X => X.submatrix (ee.prodCongr ee) (ee.prodCongr ee)) hpq
      rw [← Matrix.submatrix_mul_equiv (e₂ := ee.prodCongr ee)] at h
      simpa using h
    rw [pairM_submatrix_sub_one ee hσ g, pairM_submatrix_sub_one ee hσ h] at hpq'
    rw [pairGL_coe ee τ₁ g, pairGL_coe ee τ₁ h]
    exact hpq'
  have hbound := nat_card_le_fixed_field_of_mixed_quadratic' (σ := σ) A hA2 hqA
  let φ : F ≃+* F := frobeniusAut 2 F
  have hφord : orderOf φ = f :=
    frobeniusAut_order 2 f F (by simpa [Nat.card_eq_fintype_card] using hF)
  have hφf : φ ^ f = 1 := by
    rw [← hφord]
    exact pow_orderOf_eq_one φ
  have hpow : ∀ n : ℕ, ∀ x : F, (φ ^ n) x = x ^ 2 ^ n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        calc (φ ^ (n + 1)) x = φ ((φ ^ n) x) := by rw [pow_succ', RingAut.mul_apply]
          _ = φ (x ^ 2 ^ n) := by rw [ih]
          _ = (x ^ 2 ^ n) ^ 2 := frobeniusAut_apply 2 F _
          _ = x ^ (2 ^ n * 2) := by rw [pow_mul]
          _ = x ^ 2 ^ (n + 1) := by rw [pow_succ]
  have hτ₁ : τ₁ = φ ^ (r₁ : ℕ) := by
    ext x
    rw [iterateFrobeniusEquiv_def, hpow]
  have hτ₂ : τ₂ = φ ^ (r₂ : ℕ) := by
    ext x
    rw [iterateFrobeniusEquiv_def, hpow]
  have hsinv : (φ ^ (r₁ : ℕ))⁻¹ = φ ^ (f - r₁) := by
    have h1 : (φ ^ (r₁ : ℕ)) * φ ^ (f - r₁) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt r₁.isLt), hφf]
    exact mul_eq_one_iff_inv_eq.mp h1
  have hσexpr : σ = φ ^ (r₂ : ℕ) * φ ^ (f - r₁) := by
    change τ₁.symm.trans τ₂ = φ ^ (r₂ : ℕ) * φ ^ (f - r₁)
    rw [hτ₁, hτ₂]
    ext x
    rw [RingEquiv.trans_apply, RingAut.mul_apply]
    congr 1
    rw [← RingAut.inv_apply, hsinv]
  have hae : (r₁ : ℕ) + e ≡ (r₂ : ℕ) [MOD f] := by
    rw [hr₂]
    exact (Nat.mod_modEq ((r₁ : ℕ) + e) f).symm
  have hf0 : f ≡ 0 [MOD f] := Nat.modulus_modEq_zero
  have hmod : (r₂ : ℕ) + (f - r₁) ≡ e [MOD f] := by
    apply Nat.ModEq.add_right_cancel' (r₁ : ℕ)
    have h1 : (r₂ : ℕ) + (f - r₁) + r₁ = (r₂ : ℕ) + f := by
      rw [Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt r₁.isLt)]
    rw [h1]
    have h2 : (r₂ : ℕ) + f ≡ (r₂ : ℕ) + 0 [MOD f] :=
      Nat.ModEq.add (Nat.ModEq.refl _) hf0
    have h3 : (r₂ : ℕ) + 0 ≡ e + r₁ [MOD f] := by
      simpa [Nat.add_comm] using hae.symm
    exact h2.trans h3
  have hσe : σ = φ ^ e := by
    rw [hσexpr, ← pow_add]
    exact pow_eq_pow_of_modEq hmod hφf
  have hσ2 : σ.trans σ = RingEquiv.refl F := by
    have hmul : σ * σ = σ.trans σ := by ext x; simp [RingAut.mul_apply]
    rw [← hmul, hσe, ← pow_add, show e + e = f by omega, hφf]
    rfl
  have hσ1 : σ ≠ RingEquiv.refl F := by
    intro h
    have hpe : φ ^ e = 1 := by rw [← hσe]; simpa [RingAut.one_eq_refl] using h
    have hdvd : f ∣ e := by
      rw [← hφord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpe
    have hle := Nat.le_of_dvd hepos hdvd
    omega
  have hfixed : Nat.card {c : F // σ c = c} = 2 ^ (f / 2) :=
    nat_card_fixed_eq_pow_half_of_order_two (f := f)
      (by simpa [Nat.card_eq_fintype_card] using hF) σ hσ2 hσ1
  calc Nat.card P = Nat.card A := (Subgroup.card_map_of_injective hρ_inj).symm
    _ ≤ Nat.card {c : F // σ c = c} := hbound
    _ = 2 ^ (f / 2) := hfixed
    _ = 2 ^ e := by rw [show f / 2 = e by omega]


theorem two_mul_card_lt_pow_codim_slModelRep_pair (hm : 4 ≤ m) (hF : Fintype.card F = 2 ^ f)
    {e : ℕ} (hfe : f = 2 * e) (ε : Fin f → Finset (Fin (m + 1))) {r₁ r₂ : Fin f}
    (hr₂ : (r₂ : ℕ) = (r₁ + e) % f) {j : Fin (m + 1)} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = m)
    (h₁ : ε r₁ = {j}) (h₂ : ε r₂ = {j}) (hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅)
    {N : ℕ} (hN : 2 ^ e ≤ N)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)} (hP1 : P ≠ ⊥)
    (hP : ∀ a ∈ P, a * a = 1)
    (hquad : ∀ a ∈ P, ∀ b ∈ P,
      (slModelRep (F := F) (k := k) ε a - 1) * (slModelRep (F := F) (k := k) ε b - 1) = 0) :
    2 * Nat.card P < N ^ (finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) := by
  classical
  have hfpos : 0 < f := r₁.pos
  have hepos : 0 < e := by omega
  have hr : r₁ ≠ r₂ := by
    rintro rfl
    have hmod : (r₁ : ℕ) = ((r₁ : ℕ) + e) % f := hr₂
    have hdiv := Nat.div_add_mod ((r₁ : ℕ) + e) f
    rw [show ((r₁ : ℕ) + e) % f = (r₁ : ℕ) from hmod.symm] at hdiv
    have hdiv' : f * (((r₁ : ℕ) + e) / f) + (r₁ : ℕ) = e + (r₁ : ℕ) := by
      rw [hdiv, Nat.add_comm (r₁ : ℕ) e]
    have hk : f * (((r₁ : ℕ) + e) / f) = e := Nat.add_right_cancel hdiv'
    have hdvd : f ∣ e := ⟨_, hk.symm⟩
    have hle := Nat.le_of_dvd hepos hdvd
    omega
  have hcard := card_le_of_slModelRep_pair (m := m) (f := f) (k := k) (by omega) hF hfe
    ε hr₂ hj h₁ h₂ hrest hP hquad
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have hu1' : (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) ≠ 1 := fun h =>
    hu1 (Subtype.ext h)
  have huu : (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) * u = 1 := hP u u.2
  have hrank := two_mul_le_finrank_range_slModelRep_pair (m := m) (f := f) (k := k) (by omega)
    ε hr hj h₁ h₂ hrest huu hu1'
  have hfix : fixSub (slModelRep (F := F) (k := k) ε) P =
      fixSubGen (slModelRep (F := F) (k := k) ε) P := rfl
  have hle := finrank_range_sub_one_le (slModelRep (F := F) (k := k) ε) P u.2
  have hcodim : 2 * m ≤ finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P) := by
    rw [hfix]
    omega
  have h8 : 8 ≤ finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P) := by omega
  have hNd : 2 ^ (8 * e) ≤ N ^ (finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) := by
    calc 2 ^ (8 * e) = 2 ^ (e * 8) := by rw [Nat.mul_comm]
      _ = (2 ^ e) ^ 8 := by rw [pow_mul]
      _ ≤ (2 ^ e) ^ (finrank k (BModel k ε) -
            finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) :=
          Nat.pow_le_pow_right (by positivity) h8
      _ ≤ N ^ (finrank k (BModel k ε) -
            finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) :=
          Nat.pow_le_pow_left hN _
  have h2P : 2 * Nat.card P ≤ 2 ^ (e + 1) := by
    calc 2 * Nat.card P ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 hcard
      _ = 2 ^ (e + 1) := by rw [pow_succ, mul_comm]
  have hlt : 2 ^ (e + 1) < 2 ^ (8 * e) := by
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    omega
  exact lt_of_le_of_lt h2P (lt_of_lt_of_le hlt hNd)

end CFSG.LieType.SpecialLinear.SLModel
