module

public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg

section NatMat

variable {d : ℕ} (R : Type*) [CommRing R]

@[expose] def natMat : Module.End R (Fin d →₀ R) ≃ₐ[R] Matrix (Fin d) (Fin d) R :=
  LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne

theorem natMat_apply (f : Module.End R (Fin d →₀ R)) (r s : Fin d) :
    natMat R f r s = f (Finsupp.single s 1) r := by
  simp [natMat, LinearMap.toMatrixAlgEquiv_apply]

theorem natMat_diagUnit
    (f : Fin d → Rˣ) :
    natMat R (diagUnit f : Module.End R (Fin d →₀ R)) =
      Matrix.diagonal fun a => ((f a : Rˣ) : R) := by
  ext r s
  rw [natMat_apply, diagUnit_single, Matrix.diagonal_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  by_cases h : s = r
  · subst h
    simp
  · simp [h, Ne.symm h]

end NatMat

variable {τ : Tag} (D : MinData τ)

@[expose] def rootMat (γ : Fin τ.rank → ℤ) : Matrix (Fin D.d) (Fin D.d) ℤ :=
  natMat ℤ (D.rootOp ℤ γ)

theorem rootOp_single_apply_eq_cast
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ)
    (r s : Fin D.d) :
    D.rootOp R γ (Finsupp.single s 1) r = ((D.rootOp ℤ γ (Finsupp.single s 1) r : ℤ) : R) := by
  classical
  unfold MinData.rootOp
  split_ifs with h
  · simp only [MinData.E, toEnd_single, digVec]
    split_ifs with h'
    · simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> push_cast <;> ring
    · simp
  · simp

theorem natMat_rootOp
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ) :
    natMat R (D.rootOp R γ) = (rootMat D γ).map (Int.cast : ℤ → R) := by
  ext r s
  rw [natMat_apply, Matrix.map_apply, rootMat, natMat_apply, rootOp_single_apply_eq_cast]

variable {D} (hV : D.Valid)

theorem natMat_rootUnit
    (R : Type*) [CommRing R] (γ : Fin τ.rank → ℤ) (c : R) :
    natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R)) =
      1 + c • (rootMat D γ).map (Int.cast : ℤ → R) := by
  rw [coe_rootUnit, map_add, map_one, map_smul, natMat_rootOp]

theorem mapMatrix_natMat_rootUnit
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (γ : Fin τ.rank → ℤ) (c : R) :
    f.mapMatrix (natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R))) =
      natMat S (rootUnit hV S γ (f c) : Module.End S (Fin D.d →₀ S)) := by
  rw [natMat_rootUnit, natMat_rootUnit]
  ext r s
  simp [Matrix.one_apply, apply_ite f]

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

structure IsUpperUni (M : Matrix (Fin n) (Fin n) R) : Prop where
  diag : ∀ i, M i i = 1
  lower : ∀ i j, j < i → M i j = 0

structure IsLowerUni (M : Matrix (Fin n) (Fin n) R) : Prop where
  diag : ∀ i, M i i = 1
  upper : ∀ i j, i < j → M i j = 0

theorem isUpperUni_one : IsUpperUni (1 : Matrix (Fin n) (Fin n) R) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ h => Matrix.one_apply_ne (ne_of_gt h)⟩

theorem isLowerUni_one : IsLowerUni (1 : Matrix (Fin n) (Fin n) R) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ h => Matrix.one_apply_ne (ne_of_lt h)⟩

theorem IsUpperUni.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsUpperUni M)
    (hN : IsUpperUni N) : IsUpperUni (M * N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.diag, hN.diag, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM.lower i k h, zero_mul]
      · rw [hN.lower k i h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM.lower i k h, zero_mul]
    · rw [hN.lower k j (lt_of_lt_of_le hij h), mul_zero]

theorem IsLowerUni.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsLowerUni M)
    (hN : IsLowerUni N) : IsLowerUni (M * N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.diag, hN.diag, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN.upper k i h, mul_zero]
      · rw [hM.upper i k h, zero_mul]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with h | h
    · rw [hM.upper i k h, zero_mul]
    · rw [hN.upper k j (lt_of_le_of_lt h hij), mul_zero]

end Uni

@[expose] def DegOrdered (D : MinData τ) : Prop :=
  ∀ a b : Fin D.d, a ≤ b → D.deg b ≤ D.deg a

include hV in
theorem rootMat_eq_zero_of_pos
    (hord : DegOrdered D) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : 0 < ht γ) {r s : Fin D.d} (hsr : s ≤ r) : rootMat D γ r s = 0 := by
  rw [rootMat, natMat_apply]
  rcases hV.isSignedMap_rootOp (R := ℤ) hγ s with h0 | ⟨b, hb, hs⟩
  · rw [h0, Finsupp.zero_apply]
  · have hdeg := hV.deg_eq_add hb
    have hsc : (0 : ℤ) < D.scale := by exact_mod_cast hV.scale_pos
    have hbr : b ≠ r := by
      rintro rfl
      have := hord s b hsr
      nlinarith
    rcases hs with hs | hs <;> rw [hs] <;> simp [hbr]

include hV in
theorem rootMat_eq_zero_of_neg
    (hord : DegOrdered D) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : ht γ < 0) {r s : Fin D.d} (hrs : r ≤ s) : rootMat D γ r s = 0 := by
  rw [rootMat, natMat_apply]
  rcases hV.isSignedMap_rootOp (R := ℤ) hγ s with h0 | ⟨b, hb, hs⟩
  · rw [h0, Finsupp.zero_apply]
  · have hdeg := hV.deg_eq_add hb
    have hsc : (0 : ℤ) < D.scale := by exact_mod_cast hV.scale_pos
    have hbr : b ≠ r := by
      rintro rfl
      have := hord b s hrs
      nlinarith
    rcases hs with hs | hs <;> rw [hs] <;> simp [hbr]

theorem isUpperUni_natMat_rootUnit
    (hord : DegOrdered D) (R : Type*) [CommRing R]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < ht γ) (c : R) :
    IsUpperUni (natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R))) := by
  rw [natMat_rootUnit]
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · simp [rootMat_eq_zero_of_pos hV hord hγ hpos le_rfl]
  · simp [Matrix.one_apply_ne (ne_of_gt hji), rootMat_eq_zero_of_pos hV hord hγ hpos hji.le]

theorem isLowerUni_natMat_rootUnit
    (hord : DegOrdered D) (R : Type*) [CommRing R]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hneg : ht γ < 0) (c : R) :
    IsLowerUni (natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R))) := by
  rw [natMat_rootUnit]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [rootMat_eq_zero_of_neg hV hord hγ hneg le_rfl]
  · simp [Matrix.one_apply_ne (ne_of_lt hij), rootMat_eq_zero_of_neg hV hord hγ hneg hij.le]

end CFSG.TauCetiBridge.Minuscule
