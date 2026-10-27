module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Iso
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Module Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

private theorem u35_det {E : Type} [Field E] [CharP E 5] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Basis (Fin 3) E (ι → E)) (L : (ι → E) →ₗ[E] (ι → E))
    (h0 : L (b 0) = (2 : E) • b 0) (h1 : L (b 1) = (3 : E) • b 1) (h2 : L (b 2) = b 2) :
    LinearMap.det L = 1 := by
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b L = Matrix.diagonal ![(2 : E), 3, 1] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases j <;> fin_cases i <;> simp [h0, h1, h2, Matrix.diagonal_apply]
  rw [this, det_diagonal, Fin.prod_univ_three]
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  simp
  linear_combination h5

private theorem u35_pow {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : (ι → E) →ₗ[E] (ι → E)) (v : ι → E) (c : E) (hv : L v = c • v) (n : ℕ) :
    (L ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ]; ring_nf

private theorem u35_matrix_eq {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [Field E]
    {M N : Matrix ι ι E} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one, col_apply] using this

private theorem u35_main {E : Type} [Field E] {h : UnitaryFieldData 5 1 E}
    {A : GL (HypIndex 1 1) E} {σ : E ≃+* E}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1)
    (hσ : ∀ c, σ c = h.bar c)
    (b : Basis (Fin 3) E (HypIndex 1 1 → E))
    (g₁ : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E))
    (hu : g₁ ∈ sesqUnitaryGroup (hypForm h 1 1))
    (hc : ∀ v, (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E))
      (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) v) =
      semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)
        ((g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) v))
    (h0 : (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 0) = (2 : E) • b 0)
    (h1 : (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 1) = (3 : E) • b 1)
    (h2 : (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 2) = b 2) :
    ∃ g : hypSU h 1 1,
      semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ (hypProj h 1 1 g) = hypProj h 1 1 g ∧
        orderOf (hypProj h 1 1 g) = 4 := by
  haveI : CharP E 5 := h.charP
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hdet := u35_det b _ h0 h1 h2
  set g₂ : sesqSpecialUnitaryGroup (hypForm h 1 1) :=
    ⟨g₁, mem_sesqSpecialUnitaryGroup.mpr ⟨hu, hdet⟩⟩ with hg₂
  set g : hypSU h 1 1 := (hypSesqSUEquiv 1 1 h).symm g₂ with hg
  have hgl : (Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex 1 1) E)) = g₁ := by
    rw [← coe_hypSesqSUEquiv, hg, MulEquiv.apply_symm_apply]
  have hmv : ∀ v, ((g : GL (HypIndex 1 1) E) : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *ᵥ v =
      (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) v := fun v => by
    rw [← hgl, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hcomm : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *
      ((g : GL (HypIndex 1 1) E) : Matrix (HypIndex 1 1) (HypIndex 1 1) E).map h.bar =
      ((g : GL (HypIndex 1 1) E) : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) := by
    symm
    ext i j
    have h3 := congrFun (hc (Pi.single j 1)) i
    simp only [semilinearMatrixMap_apply, ← hmv] at h3
    have hb : (fun k => h.bar ((Pi.single j (1 : E) : HypIndex 1 1 → E) k)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [hb, Matrix.mulVec_mulVec, mulVec_single_one, col_apply] at h3
    rw [h3, mulVec_single_one]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, col_apply]
  refine ⟨g, semilinearAutHom_hypProj_of_mul_eq h le_rfl le_rfl hx g ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut_of_bar h hσ]
    exact hcomm
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmvn : ∀ (n : ℕ) v, (((g ^ n : hypSU h 1 1) : GL (HypIndex 1 1) E) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) E) *ᵥ v =
        ((g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) ^ n) v := fun n v => by
      have : Matrix.GeneralLinearGroup.toLin (((g ^ n : hypSU h 1 1)) : GL (HypIndex 1 1) E) =
          g₁ ^ n := by
        rw [Subgroup.coe_pow, map_pow, hgl]
      rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, this,
        Units.val_pow_eq_pow_val]
    have hL4 : (g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) ^ 4 = 1 := by
      refine b.ext fun i => ?_
      fin_cases i
      · show ((g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) ^ 4) (b 0) =
          (1 : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 0)
        rw [u35_pow _ _ _ h0, show (2 : E) ^ 4 = 1 by linear_combination 3 * h5, one_smul]; rfl
      · show ((g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) ^ 4) (b 1) =
          (1 : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 1)
        rw [u35_pow _ _ _ h1, show (3 : E) ^ 4 = 1 by linear_combination 16 * h5, one_smul]; rfl
      · show ((g₁ : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) ^ 4) (b 2) =
          (1 : (HypIndex 1 1 → E) →ₗ[E] (HypIndex 1 1 → E)) (b 2)
        rw [u35_pow _ _ _ (by rw [h2, one_smul] : _ = (1 : E) • b 2), one_pow, one_smul]; rfl
    have hg4 : g ^ 4 = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply u35_matrix_eq
      intro v
      rw [hmvn, hL4]
      simp
    have hg2 : ¬ g ^ 2 ∈ hypScalars h 1 1 := by
      intro hmem
      obtain ⟨c, hcm⟩ := exists_eq_smul_one_of_mem_hypScalars hmem
      have e0 := hmvn 2 (b 0)
      have e2 := hmvn 2 (b 2)
      rw [hcm, u35_pow _ _ _ h0, Matrix.smul_mulVec, Matrix.one_mulVec] at e0
      rw [hcm, u35_pow _ _ _ (by rw [h2, one_smul] : _ = (1 : E) • b 2), Matrix.smul_mulVec,
        Matrix.one_mulVec] at e2
      have c4 : c = 2 ^ 2 := smul_left_injective E (b.ne_zero 0) e0
      have c1 : c = 1 ^ 2 := smul_left_injective E (b.ne_zero 2) e2
      have h3 : (3 : E) = 0 := by rw [c4] at c1; linear_combination c1
      have : (1 : E) = 0 := by linear_combination 2 * h3 - h5
      exact one_ne_zero this
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := hypProj h 1 1 g) ?_ ?_
    · simpa using this
    · intro h'
      apply hg2
      rw [← ker_hypProj, MonoidHom.mem_ker, map_pow]
      simpa using h'
    · rw [← map_pow]
      simp [hg4]

theorem psu35_fixed_order_four {E : Type} [Field E] {h : UnitaryFieldData 5 1 E}
    {A : GL (HypIndex 1 1) E} {σ : E ≃+* E}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1)
    (hσ : ∀ c, σ c = h.bar c) (hk : Nat.card h.fixedField = 5)
    (hdim : finrank h.fixedField
      (conjFixed h (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E))) = 3)
    (hbij : Function.Bijective (LinearMap.liftBaseChange E
      (conjFixed h (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E))).subtype))
    (Bf : LinearMap.BilinForm h.fixedField
      (conjFixed h (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E))))
    (hBf : ∀ v w, (Bf v w : E) = hypForm h 1 1 v w) (hs : Bf.IsSymm) (hnd : Bf.Nondegenerate)
    (Φ : commutingUnitary (hypForm h 1 1)
        (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)) ≃*
      TauCeti.BilinForm.isometryGroup Bf)
    (hΦ : ∀ g w, (((Φ g : conjFixed h (semilinearMatrixMap h
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)) ≃ₗ[h.fixedField] conjFixed h
          (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E))) w :
        conjFixed h (semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E))) :
          HypIndex 1 1 → E) =
      ((g : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E)) :
        (HypIndex 1 1 → E) →ₗ[E] HypIndex 1 1 → E) w) :
    ∃ g : hypSU h 1 1,
      semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ (hypProj h 1 1 g) = hypProj h 1 1 g ∧
        orderOf (hypProj h 1 1 g) = 4 := by
  classical
  haveI : Finite h.fixedField := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  letI : Fintype h.fixedField := Fintype.ofFinite _
  have hF : Fintype.card h.fixedField = 5 := by rw [← Nat.card_eq_fintype_card, hk]
  obtain ⟨b, y, hy, y0, y1, y2⟩ := exists_isometry_two_three hF hdim Bf hs hnd
  have hyI : y ∈ TauCeti.BilinForm.isometryGroup Bf :=
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr hy
  set g₁ := Φ.symm ⟨y, hyI⟩ with hg₁
  have hΦy : ∀ w : conjFixed h (semilinearMatrixMap h
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)),
      ((g₁ : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E)) :
        (HypIndex 1 1 → E) →ₗ[E] HypIndex 1 1 → E) (w : HypIndex 1 1 → E) =
      (y w : HypIndex 1 1 → E) :=
    fun w => by
      have := hΦ g₁ w
      rw [hg₁, MulEquiv.apply_symm_apply] at this
      exact this.symm
  let b' : Basis (Fin 3) E (HypIndex 1 1 → E) :=
    (Basis.baseChange E b).map (LinearEquiv.ofBijective _ hbij)
  have hb' : ∀ i, b' i = (b i : HypIndex 1 1 → E) := fun i => by
    simp [b']
  refine u35_main hx hσ b' (g₁ : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E)) g₁.2.1 g₁.2.2
    ?_ ?_ ?_
  · rw [hb', hΦy, y0]; simp [Algebra.smul_def]
    rw [map_ofNat, map_ofNat]
  · rw [hb', hΦy, y1]; simp [Algebra.smul_def]
    rw [map_ofNat, map_ofNat]
  · rw [hb', hΦy, y2]

end CFSG.OddStandard.SmallF3.Omega
