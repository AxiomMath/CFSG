module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUg
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Frame

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
variable {δ : h.fixedFieldˣ} (h2 : (2 : h.fixedField) ≠ 0)

theorem yHom_apply_fixW (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4)
    {A : Matrix (Fin 4) (Fin 4) K}
    (ψW : fixW h A ≃ₗ[h.fixedField] hermitianSubmodule (δ : h.fixedField))
    (hPx : ∀ x : Fin 4 → h.fixedField, (P : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i => (x i : K)) =
      ((((hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm) x : fixW h A) : Fin 4 → K))
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) (w : fixW h A) :
    (((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (w : Fin 4 → K) =
      ((ψW.symm (rowOAction δ g (ψW w)) : fixW h A) : Fin 4 → K) := by
  set χ := (hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm with hχ
  set x := χ.symm w with hx
  have hw : (w : Fin 4 → K) = (P : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i => (x i : K)) := by
    rw [hPx, hx, LinearEquiv.apply_symm_apply]
  have hPi : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hUx : ((GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i => (x i : K)) =
        fun i => (((Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField) *ᵥ x) i : K) := by
    funext i
    exact (RingHom.map_mulVec h.fixedField.subtype _ x i).symm
  have hxw : hermitianCoordinates (δ : h.fixedField) h2 x = ψW w := by
    rw [hx]
    apply ψW.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change χ (χ.symm w) = w
    rw [LinearEquiv.apply_symm_apply]
  rw [coe_yHom, hw, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (P :
    Matrix (Fin 4) (Fin 4) K), hPi, Matrix.mul_one, ← Matrix.mulVec_mulVec, hUx, hPx, hχ,
    LinearEquiv.trans_apply, Umat_mulVec, LinearEquiv.apply_symm_apply, hxw]

theorem toSesq_yHom_mem {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4)
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = P)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) :
    EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g) ∈
      FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu) := by
  have hreal := yHom_real h h2 P hmem hAP g
  set y : GL (Fin 4) K := ((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) with hy
  have hyA : (y : Matrix (Fin 4) (Fin 4) K) * A = A * (y : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    have h1 : y * A = A * GeneralLinearGroup.map h.bar y := by
      calc y * A = A * GeneralLinearGroup.map h.bar y * A⁻¹ * A := by rw [hreal]
        _ = A * GeneralLinearGroup.map h.bar y := by group
    exact congrArg Units.val h1
  refine (mem_fixed_unitaryConj h _ _ (StabU.stdHermForm_antiunitaryMap h hAu) _).mpr
    fun v => ?_
  change unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g))
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) =
    antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g)) v)
  rw [GSThmB.Catalog7U4.unitaryOp_toSesqUnitary h, Matrix.toLin'_apply, Matrix.toLin'_apply,
    antiunitaryMap_apply, antiunitaryMap_apply, StabU.bar_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← hy, hyA]

theorem eq_toSesq_yHom (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4)
    {A : Matrix (Fin 4) (Fin 4) K}
    (ψW : fixW h A ≃ₗ[h.fixedField] hermitianSubmodule (δ : h.fixedField))
    (hPx : ∀ x : Fin 4 → h.fixedField, (P : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i => (x i : K)) =
      ((((hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm) x : fixW h A) : Fin 4 → K))
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)))
    (u : sesqUnitaryGroup (stdHermForm h 4))
    (hu : ∀ w : fixW h A, unitaryOp u (w : Fin 4 → K) =
      ((ψW.symm (rowOAction δ g (ψW w)) : fixW h A) : Fin 4 → K)) :
    u = EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g) := by
  set y : Matrix (Fin 4) (Fin 4) K :=
    (((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hy
  have hreal1 : ∀ i : Fin 4, (Pi.single i 1 : Fin 4 → K) =
      fun j => ((Pi.single i 1 : Fin 4 → h.fixedField) j : K) := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have hL : (unitaryOp u).comp (Matrix.toLin' (P : Matrix (Fin 4) (Fin 4) K)) =
      Matrix.toLin' (y * (P : Matrix (Fin 4) (Fin 4) K)) := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply]
    rw [hreal1, ← Matrix.mulVec_mulVec, hPx, hu, ← yHom_apply_fixW h h2 P hmem ψW hPx g]
  have hPi' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  have hv : v = (P : Matrix (Fin 4) (Fin 4) K) *ᵥ ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hPi', Matrix.one_mulVec]
  have h1 := LinearMap.congr_fun hL ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
  rw [LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hv,
    ← Matrix.mulVec_mulVec, ← hv] at h1
  change unitaryOp u v = unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g)) v
  rw [GSThmB.Catalog7U4.unitaryOp_toSesqUnitary h, Matrix.toLin'_apply, h1]

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
