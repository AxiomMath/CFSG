module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RepresentationTheory.Maschke

public section

namespace CFSG.LinearAlgebra

open Module

variable {K : Type*} [Field K] [Fintype K] {B : Type*} [CommRing B] [Algebra K B]

theorem exists_linearEquiv_pow_card_smul_of_isSimple {W : Type*} [AddCommGroup W] [Module K W]
    [Module B W] [IsScalarTower K B W] [FiniteDimensional K W] [IsSimpleModule B W]
    {δ : K} (hδ : δ ≠ 0) :
    ∃ g : W ≃ₗ[K] W, (∀ (b : B) (w : W), g (b • w) = b ^ Fintype.card K • g w) ∧
      LinearMap.det (g : W →ₗ[K] W) = δ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule B W›
  letI : Field (B ⧸ I) := Ideal.Quotient.field I
  let eK : W ≃ₗ[K] B ⧸ I := e.restrictScalars K
  haveI : FiniteDimensional K (B ⧸ I) := LinearEquiv.finiteDimensional eK
  haveI : Finite (B ⧸ I) := Module.finite_of_finite K
  let φ : (B ⧸ I) ≃ₐ[K] (B ⧸ I) := FiniteField.frobeniusAlgEquivOfAlgebraic K (B ⧸ I)
  have hφ : ∀ y, φ y = y ^ Fintype.card K := FiniteField.frobeniusAlgEquivOfAlgebraic_apply K _
  have hφdet : LinearMap.det (φ.toLinearEquiv : (B ⧸ I) →ₗ[K] (B ⧸ I)) ≠ 0 :=
    (LinearEquiv.isUnit_det' φ.toLinearEquiv).ne_zero
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective K (B ⧸ I)
    (δ * (LinearMap.det (φ.toLinearEquiv : (B ⧸ I) →ₗ[K] (B ⧸ I)))⁻¹)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at ha
    exact mul_ne_zero hδ (inv_ne_zero hφdet) ha.symm
  let u : (B ⧸ I)ˣ := Units.mk0 a ha0
  let gF : (B ⧸ I) ≃ₗ[K] (B ⧸ I) :=
    φ.toLinearEquiv.trans (DistribMulAction.toLinearEquiv K (B ⧸ I) u)
  have hgF : ∀ y, gF y = a * y ^ Fintype.card K := fun y => by
    change u • φ y = a * y ^ Fintype.card K
    rw [Units.smul_def, hφ]
    rfl
  have hmk : ∀ (c : B) (y : B ⧸ I), c • y = Ideal.Quotient.mk I c * y := fun c y => by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  refine ⟨eK.trans (gF.trans eK.symm), fun b w => ?_, ?_⟩
  · change e.symm (gF (e (b • w))) = b ^ Fintype.card K • e.symm (gF (e w))
    rw [e.map_smul, hmk, hgF, hgF, mul_pow, ← map_pow, mul_left_comm, ← hmk, e.symm.map_smul]
  · have h1 : ((eK.trans (gF.trans eK.symm) : W ≃ₗ[K] W) : W →ₗ[K] W) =
        (eK.symm : (B ⧸ I) →ₗ[K] W) ∘ₗ (gF : (B ⧸ I) →ₗ[K] (B ⧸ I)) ∘ₗ
          (eK.symm.symm : W →ₗ[K] (B ⧸ I)) :=
      LinearMap.ext fun w => rfl
    have h2 : (gF : (B ⧸ I) →ₗ[K] (B ⧸ I)) =
        Algebra.lmul K (B ⧸ I) a ∘ₗ (φ.toLinearEquiv : (B ⧸ I) →ₗ[K] (B ⧸ I)) :=
      LinearMap.ext fun y => by
        change u • φ y = a * φ y
        rw [Units.smul_def]
        rfl
    rw [h1, LinearMap.det_conj, h2, LinearMap.det_comp, ← Algebra.norm_apply, ha, mul_assoc,
      inv_mul_cancel₀ hφdet, mul_one]

private theorem exists_linearEquiv_pow_card_smul_aux (n : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module K V] [Module B V] [IsScalarTower K B V]
      [FiniteDimensional K V] [IsSemisimpleModule B V], finrank K V = n → ∀ {δ : K}, δ ≠ 0 →
      ∃ g : V ≃ₗ[K] V, (∀ (b : B) (v : V), g (b • v) = b ^ Fintype.card K • g v) ∧
        (Nontrivial V → LinearMap.det (g : V →ₗ[K] V) = δ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ _ _ _ hn δ hδ
    by_cases hV : Nontrivial V
    · obtain ⟨W, hW⟩ := IsSemisimpleModule.exists_simple_submodule B V
      obtain ⟨W', hWW'⟩ := exists_isCompl W
      haveI : FiniteDimensional K W :=
        Module.Finite.of_injective ((W.subtype).restrictScalars K) Subtype.val_injective
      haveI : FiniteDimensional K W' :=
        Module.Finite.of_injective ((W'.subtype).restrictScalars K) Subtype.val_injective
      let e : (W × W') ≃ₗ[K] V := (Submodule.prodEquivOfIsCompl W W' hWW').restrictScalars K
      have hdim : finrank K W + finrank K W' = n := by
        rw [← hn, ← e.finrank_eq, Module.finrank_prod]
      haveI : Nontrivial W := IsSimpleModule.nontrivial B W
      have hW0 : 0 < finrank K W := Module.finrank_pos
      obtain ⟨gW, hgW, hdW⟩ := exists_linearEquiv_pow_card_smul_of_isSimple (K := K) (B := B)
        (W := W) hδ
      obtain ⟨gW', hgW', hdW'⟩ := ih (finrank K W') (by omega) W' rfl (δ := 1) one_ne_zero
      have hdW'' : LinearMap.det (gW' : W' →ₗ[K] W') = 1 := by
        by_cases hW' : Nontrivial W'
        · exact hdW' hW'
        · haveI : Subsingleton W' := not_nontrivial_iff_subsingleton.mp hW'
          exact LinearMap.det_eq_one_of_subsingleton _
      refine ⟨e.symm.trans ((gW.prodCongr gW').trans e), fun b v => ?_, fun _ => ?_⟩
      · have hes : e.symm (b • v) = b • e.symm v :=
          (Submodule.prodEquivOfIsCompl W W' hWW').symm.map_smul b v
        change e (gW.prodCongr gW' (e.symm (b • v))) = b ^ Fintype.card K • e (gW.prodCongr gW' (e.symm v))
        rw [hes]
        have hp : gW.prodCongr gW' (b • e.symm v) =
            b ^ Fintype.card K • gW.prodCongr gW' (e.symm v) := by
          rw [Prod.smul_def, LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_apply, hgW, hgW',
            Prod.smul_mk]
        rw [hp]
        exact (Submodule.prodEquivOfIsCompl W W' hWW').map_smul _ _
      · have h1 : ((e.symm.trans ((gW.prodCongr gW').trans e) : V ≃ₗ[K] V) : V →ₗ[K] V) =
            (e : (W × W') →ₗ[K] V) ∘ₗ (LinearMap.prodMap (gW : W →ₗ[K] W) (gW' : W' →ₗ[K] W')) ∘ₗ
              (e.symm : V →ₗ[K] (W × W')) :=
          LinearMap.ext fun v => rfl
        rw [h1, LinearMap.det_conj, LinearMap.det_prodMap, hdW, hdW'', mul_one]
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      exact ⟨LinearEquiv.refl K V, fun _ _ => Subsingleton.elim _ _, fun h => absurd h hV⟩

theorem exists_linearEquiv_pow_card_smul {V : Type*} [AddCommGroup V] [Module K V] [Module B V]
    [IsScalarTower K B V] [FiniteDimensional K V] [IsSemisimpleModule B V] {δ : K} (hδ : δ ≠ 0) :
    ∃ g : V ≃ₗ[K] V, (∀ (b : B) (v : V), g (b • v) = b ^ Fintype.card K • g v) ∧
      (Nontrivial V → LinearMap.det (g : V →ₗ[K] V) = δ) :=
  exists_linearEquiv_pow_card_smul_aux (finrank K V) V rfl hδ

theorem exists_conj_eq_pow_card {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {E : Subgroup (V ≃ₗ[K] V)} [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : (Nat.card E : K) ≠ 0) {δ : K} (hδ : δ ≠ 0) :
    ∃ g : V ≃ₗ[K] V, (∀ x ∈ E, g * x * g⁻¹ = x ^ Fintype.card K) ∧
      (Nontrivial V → LinearMap.det (g : V →ₗ[K] V) = δ) := by
  classical
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let ρ : E →* (V →ₗ[K] V) :=
    { toFun := fun x => ((x : V ≃ₗ[K] V) : V →ₗ[K] V)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let L : MonoidAlgebra K E →ₐ[K] (V →ₗ[K] V) := MonoidAlgebra.lift K (V →ₗ[K] V) E ρ
  letI : Module (MonoidAlgebra K E) V := Module.compHom V L.toRingHom
  have hsmul : ∀ (b : MonoidAlgebra K E) (v : V), b • v = L b v := fun _ _ => rfl
  haveI : IsScalarTower K (MonoidAlgebra K E) V := ⟨fun c b v => by
    rw [hsmul, hsmul, map_smul]
    rfl⟩
  haveI : NeZero (Nat.card E : K) := ⟨hcard⟩
  haveI : ComplementedLattice (Submodule (MonoidAlgebra K E) V) :=
    ⟨fun W => MonoidAlgebra.Submodule.exists_isCompl W⟩
  haveI : IsSemisimpleModule (MonoidAlgebra K E) V := IsSemisimpleModule.mk
  obtain ⟨g, hg, hdet⟩ :=
    exists_linearEquiv_pow_card_smul (K := K) (B := MonoidAlgebra K E) (V := V) hδ
  refine ⟨g, fun x hx => ?_, hdet⟩
  have hof : ∀ (y : E) (v : V), MonoidAlgebra.of K E y • v = (y : V ≃ₗ[K] V) v := fun y v => by
    rw [hsmul, MonoidAlgebra.lift_of]
    rfl
  have key : ∀ v, g (x v) = (x ^ Fintype.card K) (g v) := fun v => by
    have h := hg (MonoidAlgebra.of K E ⟨x, hx⟩) v
    rw [← map_pow, hof, hof] at h
    exact h
  refine LinearEquiv.ext fun v => ?_
  change g (x (g.symm v)) = (x ^ Fintype.card K) v
  rw [key, LinearEquiv.apply_symm_apply]

theorem exists_conj_eq_pow_card_GL_of_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Subgroup (GL (ι) K)} [Finite S]
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hcard : (Nat.card S : K) ≠ 0) :
    ∃ g : GL (ι) K, (g : Matrix (ι) (ι) K).det = 1 ∧
      ∀ s ∈ S, g * s * g⁻¹ = s ^ Fintype.card K := by
  classical
  let Φ : GL (ι) K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))
  have hΦ : ∀ A : GL (ι) K,
      ((Φ A : (ι → K) ≃ₗ[K] (ι → K)) : (ι → K) →ₗ[K] (ι → K)) =
        Matrix.toLin' (A : Matrix (ι) (ι) K) := fun _ => LinearMap.ext fun _ => rfl
  let S' : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := S.map Φ.toMonoidHom
  have : Finite S' := inferInstanceAs (Finite ↥(Φ.toMonoidHom '' (S : Set (GL (ι) K))))
  have hcard' : (Nat.card S' : K) ≠ 0 := by
    rw [Subgroup.card_map_of_injective Φ.injective]
    exact hcard
  have hcomm' : ∀ x ∈ S', ∀ y ∈ S', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change Φ x * Φ y = Φ y * Φ x
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  obtain ⟨g', hg', hdet⟩ := exists_conj_eq_pow_card (K := K) (V := ι → K) hcomm' hcard'
    (δ := 1) one_ne_zero
  refine ⟨Φ.symm g', ?_, fun s hs => Φ.injective ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | hι
    · let : IsEmpty ι := hι
      exact Matrix.det_isEmpty
    · let : Nonempty ι := hι
      rw [← LinearMap.det_toLin', ← hΦ, MulEquiv.apply_symm_apply]
      exact hdet inferInstance
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_pow]
    exact hg' (Φ s) ⟨s, hs, rfl⟩

theorem exists_conj_eq_pow_card_GL {d : ℕ} {S : Subgroup (GL (Fin d) K)} [Finite S]
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hcard : (Nat.card S : K) ≠ 0) :
    ∃ g : GL (Fin d) K, (g : Matrix (Fin d) (Fin d) K).det = 1 ∧
      ∀ s ∈ S, g * s * g⁻¹ = s ^ Fintype.card K := by
  exact exists_conj_eq_pow_card_GL_of_fintype hcomm hcard

end CFSG.LinearAlgebra

end
