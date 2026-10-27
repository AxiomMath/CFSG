module

public import CFSG.Blueprint.ChevalleyInfinitesimals
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

public noncomputable section

namespace CFSG.TauCetiBridge.GeckEntries

open TauCeti CFSG.Blueprint.Chevalley

attribute [local instance] TauCeti.moduleNNRat

theorem eq_sum_single {ι κ : Type*} [Fintype ι] [DecidableEq κ] (ℓ : ι ≃ κ) (w : κ →₀ ℚ) :
    w = ∑ z, w (ℓ z) • Finsupp.single (ℓ z) 1 := by
  ext a
  obtain ⟨z₀, rfl⟩ := ℓ.surjective a
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single z₀]
  · simp
  · intro z _ hz
    simp [ℓ.injective.ne hz]
  · simp

theorem pow_apply_of_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (ℓ : ι ≃ κ)
    (M : Matrix ι ι ℚ) (T : Module.End ℚ (κ →₀ ℚ))
    (h : ∀ x y, M x y = T (Finsupp.single (ℓ y) 1) (ℓ x)) (k : ℕ) (x y : ι) :
    (M ^ k) x y = (T ^ k) (Finsupp.single (ℓ y) 1) (ℓ x) := by
  induction k generalizing x y with
  | zero =>
    simp [Matrix.one_apply, Finsupp.single_apply, ℓ.injective.eq_iff, eq_comm]
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Module.End.mul_apply,
      eq_sum_single ℓ ((T ^ k) (Finsupp.single (ℓ y) 1)), map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← ih, ← h, mul_comm]

variable {t : DynkinType} {ht : t.Valid}

theorem intCast_repr_integralDividedPower (i : Fin t.rank ⊕ Fin t.rank) (k : ℕ)
    (hM : ∀ v ∈ (t.geckCoordinateLattice ht).toAddSubgroup,
      Associative.dividedPower k (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))) • v ∈
          (t.geckCoordinateLattice ht).toAddSubgroup)
    (r s : Fin (t.geckDim ht)) :
    (((t.geckCoordinateBasisFin ht).repr
        (integralDividedPower (t.geckRepresentation ht
            (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
          (t.geckCoordinateLattice ht).toAddSubgroup k hM (t.geckCoordinateBasisFin ht s)) r :
        ℤ) : ℚ) =
      Associative.dividedPower k
        ((t.lieBasis ht).rootGenerator i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
        ((Fintype.equivFin (t.GeckIndex ht)).symm r)
        ((Fintype.equivFin (t.GeckIndex ht)).symm s) := by
  rw [t.intCast_geckCoordinateBasisFin_repr ht, coe_integralDividedPower_apply,
    ← Associative.map_dividedPower, Module.End.smul_def,
    t.geckRepresentation_dividedPower_ι_apply ht, t.coe_geckCoordinateBasisFin ht,
    Matrix.mulVec_single_one, Matrix.col_apply]

theorem rootGenerator_pow_eq_zero (i : Fin t.rank ⊕ Fin t.rank) {k : ℕ}
    (hk : nilpotencyClass (t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))) ≤ k) :
    ((t.lieBasis ht).rootGenerator i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k = 0 := by
  set N := nilpotencyClass (t.geckRepresentation ht
    (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
  have h : t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)) ^ N = 0 :=
    pow_nilpotencyClass (t.isNilpotent_geckRepresentation_rootGenerator ht i)
  have h0 : ((t.lieBasis ht).rootGenerator i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^
      N = 0 :=
    Matrix.toLinAlgEquiv'.injective (by rw [map_pow, ← t.geckRepresentation_ι ht, h, map_zero])
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, h0, zero_mul]

theorem entry_eq_sum (i : Fin t.rank ⊕ Fin t.rank) (A : Type) [CommRing A] (c : A)
    (r s : Fin (t.geckDim ht)) (w : ℕ → ℤ)
    (hw : ∀ k, Associative.dividedPower k
        ((t.lieBasis ht).rootGenerator i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
        ((Fintype.equivFin (t.GeckIndex ht)).symm r)
        ((Fintype.equivFin (t.GeckIndex ht)).symm s) = (w k : ℚ))
    (hw4 : ∀ k, 4 ≤ k → w k = 0) :
    ((t.geckRootSubgroupPoints ht i A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      ∑ k ∈ Finset.range 4, c ^ k * (w k : A) := by
  rw [t.coe_geckRootSubgroupPoints ht,
    UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply,
    UniversalEnvelopingAlgebra.repr_kostantRootSubgroupPoints_baseChange]
  have key : ∀ k hM, (t.geckCoordinateBasisFin ht).repr
      (integralDividedPower (t.geckRepresentation ht
          (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
        (t.geckCoordinateLattice ht).toAddSubgroup k hM (t.geckCoordinateBasisFin ht s)) r =
        w k := fun k hM =>
    Int.cast_injective (α := ℚ) (by rw [intCast_repr_integralDividedPower, hw])
  simp only [key, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  set N := nilpotencyClass (t.geckRepresentation ht
    (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
  have hN : ∀ k, N ≤ k → w k = 0 := fun k hk => Int.cast_injective (α := ℚ) (by
    rw [← hw, Associative.dividedPower_def, rootGenerator_pow_eq_zero i hk]
    simp)
  calc ∑ k ∈ Finset.range N, w k • c ^ k = ∑ k ∈ Finset.range (N + 4), w k • c ^ k :=
        Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => by
          rw [hN k (by simpa using hk), zero_smul]
    _ = ∑ k ∈ Finset.range 4, w k • c ^ k :=
        (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => by
          rw [hw4 k (by simpa using hk), zero_smul]).symm
    _ = ∑ k ∈ Finset.range 4, c ^ k * (w k : A) :=
        Finset.sum_congr rfl fun k _ => by rw [zsmul_eq_mul, mul_comm]

variable {τ : Tag}

theorem entry_inl_of_apply
    (ℓ : t.GeckIndex ht ≃ Label τ) (ν : Fin t.rank ≃ Fin τ.rank)
    (i : Fin t.rank)
    (he : ∀ x y, (RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) x y =
        infE τ ℚ (ν i) (Finsupp.single (ℓ y) 1) (ℓ x))
    (A : Type) [CommRing A] (c : A) (r s : Fin (t.geckDim ht)) :
    ((t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      xOp τ A (ν i) c (Finsupp.single (ℓ ((Fintype.equivFin (t.GeckIndex ht)).symm s)) 1)
        (ℓ ((Fintype.equivFin (t.GeckIndex ht)).symm r)) := by
  set r' := (Fintype.equivFin (t.GeckIndex ht)).symm r
  set s' := (Fintype.equivFin (t.GeckIndex ht)).symm s
  rw [entry_eq_sum (.inl i) A c r s (fun k => xCoeff τ ℤ (ν i) k (Finsupp.single (ℓ s') 1) (ℓ r'))
    (fun k => ?_) (fun k hk => ?_), xOp_eq_sum_xCoeff, LinearMap.sum_apply,
    Finsupp.finsetSum_apply]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      ← mapRange_xCoeff_single (Int.castRingHom A), Finsupp.mapRange_apply, eq_intCast]
  · rw [LieAlgebra.Basis.rootGenerator_inl, t.coe_lieBasis_e ht, Associative.dividedPower_def,
      Matrix.smul_apply, pow_apply_of_apply ℓ _ _ he, infE_pow, LinearMap.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, ← mapRange_xCoeff_single (Int.castRingHom ℚ),
      Finsupp.mapRange_apply, eq_intCast, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  · rw [xCoeff_eq_zero (ν i) hk, LinearMap.zero_apply, Finsupp.zero_apply]

theorem entry_inr_of_apply
    (ℓ : t.GeckIndex ht ≃ Label τ) (ν : Fin t.rank ≃ Fin τ.rank)
    (i : Fin t.rank)
    (hf : ∀ x y, (RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) x y =
        infF τ ℚ (ν i) (Finsupp.single (ℓ y) 1) (ℓ x))
    (A : Type) [CommRing A] (c : A) (r s : Fin (t.geckDim ht)) :
    ((t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      yOp τ A (ν i) c (Finsupp.single (ℓ ((Fintype.equivFin (t.GeckIndex ht)).symm s)) 1)
        (ℓ ((Fintype.equivFin (t.GeckIndex ht)).symm r)) := by
  set r' := (Fintype.equivFin (t.GeckIndex ht)).symm r
  set s' := (Fintype.equivFin (t.GeckIndex ht)).symm s
  rw [entry_eq_sum (.inr i) A c r s (fun k => yCoeff τ ℤ (ν i) k (Finsupp.single (ℓ s') 1) (ℓ r'))
    (fun k => ?_) (fun k hk => ?_), yOp_eq_sum_yCoeff, LinearMap.sum_apply,
    Finsupp.finsetSum_apply]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      ← mapRange_yCoeff_single (Int.castRingHom A), Finsupp.mapRange_apply, eq_intCast]
  · rw [LieAlgebra.Basis.rootGenerator_inr, t.coe_lieBasis_f ht, Associative.dividedPower_def,
      Matrix.smul_apply, pow_apply_of_apply ℓ _ _ hf, infF_pow, LinearMap.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, ← mapRange_yCoeff_single (Int.castRingHom ℚ),
      Finsupp.mapRange_apply, eq_intCast, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  · rw [yCoeff_eq_zero (ν i) hk, LinearMap.zero_apply, Finsupp.zero_apply]

end CFSG.TauCetiBridge.GeckEntries
