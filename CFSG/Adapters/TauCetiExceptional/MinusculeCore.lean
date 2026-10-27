module

public import CFSG.Adapters.TauCetiExceptional.MinusculeBigCell

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (hord : DegOrdered D)

@[expose] def ratMats :
    Set (Matrix (Fin D.d) (Fin D.d) ℚ) :=
  {z | ∃ g : hV.minGroup ℚ, natMat ℚ (hV.endo ℚ g) = z}

include hA hpd hord in
theorem exists_ringHom_mapMatrix_minGenMat
    {A : Type*} [CommRing A]
    (M : Matrix (Fin D.d) (Fin D.d) A)
    (hM : ∀ P : MvPolynomial (Fin D.d × Fin D.d) ℤ,
      (∀ g : hV.minGroup ℚ, evalMat (natMat ℚ (hV.endo ℚ g)) P = 0) → evalMat M P = 0)
    (hMunit : IsUnit (bigCellDet M)) :
    ∃ ψ : GenRing τ →+* A, ψ.mapMatrix (minGenMat hV) = M := by
  refine exists_ringHom_mapMatrix_eq (minGenMat hV)
    (isUnit_bigCellDet_bigCellUnit hV (GenRing τ) hord _ _ _)
    (fun T hT hinv => eq_top_of_minGenMat hV hpd hord T hT hinv) (ratMats hV) ?_ M
    (fun P hP => hM P fun g => hP _ ⟨g, rfl⟩) hMunit
  rintro _ ⟨g, rfl⟩ hΔ
  obtain ⟨cm, t, cp, hg⟩ := exists_bigCellUnit_eq hV hA ℚ hpd hord g hΔ
  exact ⟨specialize cm t cp, by rw [mapMatrix_specialize_minGenMat, hg]⟩

theorem bigCellUnit_mem
    (K : Type*) [Field K] (cm : Fin (nPos τ) → K) (t : Fin τ.rank → Kˣ)
    (cp : Fin (nPos τ) → K) : bigCellUnit hV K cm t cp ∈ hV.minGroup K := by
  refine mul_mem (mul_mem ?_ ?_) ?_
  · rw [uNeg, ← list_prod_xm_coe]
    exact Subtype.prop _
  · rw [dT, ← coe_torusElt hV K t]
    exact Subtype.prop _
  · rw [uPos, ← list_prod_xm_coe]
    exact Subtype.prop _

include hA hpd hord in
theorem exists_minGroup_natMat_eq
    (K : Type) [Field K] (M : Matrix (Fin D.d) (Fin D.d) K)
    (hM : ∀ P : MvPolynomial (Fin D.d × Fin D.d) ℤ,
      (∀ g : hV.minGroup ℚ, evalMat (natMat ℚ (hV.endo ℚ g)) P = 0) → evalMat M P = 0)
    (hΔ : bigCellDet M ≠ 0) : ∃ g : hV.minGroup K, natMat K (hV.endo K g) = M := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_mapMatrix_minGenMat hV hA hpd hord M hM (Ne.isUnit hΔ)
  rw [minGenMat, mapMatrix_natMat_bigCellUnit] at hψ
  exact ⟨⟨_, bigCellUnit_mem hV K _ _ _⟩, hψ⟩

theorem evalMat_rename {A : Type*} [CommRing A] {n m : ℕ} (f : Fin m × Fin m → Fin n × Fin n)
    (Y : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (Fin m × Fin m) ℤ) :
    evalMat Y (MvPolynomial.rename f P) =
      evalMat (Matrix.of fun a b => Y (f (a, b)).1 (f (a, b)).2) P := by
  simp only [evalMat, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  rfl

theorem submatrix_toMat
    {n : ℕ} (lab : Fin n ≃ Fin D.d) (K : Type*) [Field K]
    (h : hV.minGroup K) :
    ((toMat lab K h : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).submatrix lab.symm lab.symm = natMat K (hV.endo K h) := by
  ext a b
  rw [Matrix.submatrix_apply, toMat_apply, natMat_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

include hA hpd hord in
theorem exists_toMat_eq
    {n : ℕ} (lab : Fin n ≃ Fin D.d) (K : Type) [Field K]
    (g : Matrix.GeneralLinearGroup (Fin n) K)
    (hg : ∀ P : MvPolynomial (Fin n × Fin n) ℤ,
      (∀ h : hV.minGroup ℚ, evalMat ((toMat lab ℚ h : Matrix.GeneralLinearGroup (Fin n) ℚ) :
        Matrix (Fin n) (Fin n) ℚ) P = 0) → evalMat (g : Matrix (Fin n) (Fin n) K) P = 0)
    (hΔ : bigCellDet ((g : Matrix (Fin n) (Fin n) K).submatrix lab.symm lab.symm) ≠ 0) :
    ∃ h : hV.minGroup K, toMat lab K h = g := by
  set f : Fin D.d × Fin D.d → Fin n × Fin n := fun ab => (lab.symm ab.1, lab.symm ab.2)
  have hM : ∀ P : MvPolynomial (Fin D.d × Fin D.d) ℤ,
      (∀ h : hV.minGroup ℚ, evalMat (natMat ℚ (hV.endo ℚ h)) P = 0) →
        evalMat ((g : Matrix (Fin n) (Fin n) K).submatrix lab.symm lab.symm) P = 0 := by
    intro P hP
    have h1 := hg (MvPolynomial.rename f P) fun h => by
      rw [evalMat_rename, ← hP h, ← submatrix_toMat hV lab ℚ h]
      rfl
    rw [evalMat_rename] at h1
    exact h1
  obtain ⟨h, hh⟩ := exists_minGroup_natMat_eq hV hA hpd hord K _ hM hΔ
  refine ⟨h, Units.ext ?_⟩
  ext r s
  rw [toMat_apply, ← natMat_apply, hh, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

end CFSG.TauCetiBridge.Minuscule
