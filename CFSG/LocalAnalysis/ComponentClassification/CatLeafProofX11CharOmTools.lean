module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Module QuadraticMap
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr isPlusType_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

section Index

theorem polar_map_isometryEquiv {K : Type} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module K V₁] [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) (x y : V₁) :
    polar Q₂ (e x) (e y) = polar Q₁ x y := by
  simp only [polar, ← map_add, e.map_app]

variable (K : Type) [Field K] (b c : K)

@[expose] def hypPairMinus (i : Fin 3) :
    ClassicalGroups.Orthogonal.HypPair (coordinateQuadMinus 4 K (by norm_num) b c) where
  e := coordinateMinusIsometry 4 K (by norm_num) b c
    (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).e
  f := coordinateMinusIsometry 4 K (by norm_num) b c
    (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).f
  Q_e := by
    rw [QuadraticMap.IsometryEquiv.map_app]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).Q_e
  Q_f := by
    rw [QuadraticMap.IsometryEquiv.map_app]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).Q_f
  polar_ef := by
    rw [polar_map_isometryEquiv]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).polar_ef

theorem hypPairMinus_orth {i j : Fin 3} (hij : i ≠ j) :
    (hypPairMinus K b c i).Orth (hypPairMinus K b c j) := by
  have h := ClassicalGroups.Orthogonal.minusPair_orth (K := K) (b := b) (c := c) (n := 4) hij
  exact ⟨(polar_map_isometryEquiv _ _ _).trans h.ee, (polar_map_isometryEquiv _ _ _).trans h.ef,
    (polar_map_isometryEquiv _ _ _).trans h.fe, (polar_map_isometryEquiv _ _ _).trans h.ff⟩

attribute [local instance] GSThmB.Catalog7Std.Om8.finite_linearEquiv

theorem index_orthogonalDerived [Finite K] (h2 : (2 : K) ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (orthogonalDerived (coordinateQuadMinus 4 K (by norm_num) b c)).index = 4 := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  have hnd := (regular_coordinateQuadMinus 4 K b c le_rfl hirr).1
  obtain ⟨hO, -⟩ := ClassicalInvolution.orthogonalGroup_index_four hnd
    (hypPairMinus_orth K b c (i := 0) (j := 1) (by decide))
    (hypPairMinus_orth K b c (i := 0) (j := 2) (by decide))
    (hypPairMinus_orth K b c (i := 1) (j := 2) (by decide))
  have hE : Nat.card (orthogonalDerived (coordinateQuadMinus 4 K (by norm_num) b c)) =
      Nat.card (ClassicalGroups.Orthogonal.elementaryGroup
        (coordinateQuadMinus 4 K (by norm_num) b c)) := by
    rw [← commutator_coordinateQuadMinus 4 K b c le_rfl hirr, ← Subgroup.map_subtype_commutator]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  have hmul := (orthogonalDerived (coordinateQuadMinus 4 K (by norm_num) b c)).card_mul_index
  rw [hE, hO] at hmul
  have hpos : 0 < Nat.card (ClassicalGroups.Orthogonal.elementaryGroup
      (coordinateQuadMinus 4 K (by norm_num) b c)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans (Nat.mul_comm _ _))

end Index

section Decomposition

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {U U' : Submodule K V}

theorem polar_eq_zero_of_decomp {A : V ≃ₗ[K] V}
    (ψ : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (hψ : ∀ h (x : U) (y : U'), (ψ.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val) (h2 : (2 : K) ≠ 0) (x : U) (y : U') :
    polar Q x y = 0 := by
  have h1 := hψ (negOrthogonal (Q.comp U.subtype), 1) x y
  have hQ := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (ψ.symm (negOrthogonal (Q.comp U.subtype), 1)).val.property (x.val + y.val)
  have e1 : ((negOrthogonal (Q.comp U.subtype)).val x).val = -x.val := by
    simp [coe_negOrthogonal]
  have e2 : ((1 : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)).val y).val =
      y.val := rfl
  rw [h1, e1, e2] at hQ
  have h3 : Q (-x.val + y.val) = Q x.val + Q y.val - polar Q x.val y.val := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_neg, QuadraticMap.polar_neg_left]
    ring
  have h4 : Q (x.val + y.val) = Q x.val + Q y.val + polar Q x.val y.val :=
    QuadraticMap.map_add Q _ _
  have h5 : (2 : K) * polar Q x.val y.val = 0 := by linear_combination h3 - h4 - hQ
  exact (mul_eq_zero.mp h5).resolve_left h2

@[expose] def sumIsometry (hc : IsCompl U U') (horth : ∀ (x : U) (y : U'), polar Q x y = 0) :
    ((Q.comp U.subtype).prod (Q.comp U'.subtype)).IsometryEquiv Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl U U' hc
  map_app' x := by
    change Q ((x.1 : V) + x.2) = Q x.1 + Q x.2
    rw [QuadraticMap.map_add Q, horth, add_zero]

theorem isPlusType_of_compl [Finite K] [FiniteDimensional K V] (hnp : ¬ IsPlusType Q)
    (hc : IsCompl U U') (horth : ∀ (x : U) (y : U'), polar Q x y = 0)
    (hndU : (Q.comp U.subtype).polarBilin.Nondegenerate) (hU : finrank K U = 4)
    (hnpU : ¬ IsPlusType (Q.comp U.subtype))
    (hndU' : (Q.comp U'.subtype).polarBilin.Nondegenerate) (hU' : finrank K U' = 4) :
    IsPlusType (Q.comp U'.subtype) := by
  by_contra h'
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus (Q.comp U'.subtype)
    hndU' (n := 2) (by norm_num) hU' with ⟨⟨e⟩⟩ | ⟨b', c', hirr', ⟨e⟩⟩
  · exact h' ((isPlusType_congr e).2 (isPlusType_quadPlus K 2))
  · apply hnp
    have h1 := CFSG.GroupTheory.WeirSylow.isPlusType_prod_quadMinus hndU (d := 2) (by norm_num)
      hU hnpU 2 hirr'
    exact (isPlusType_congr (sumIsometry hc horth)).1
      ((isPlusType_congr ((QuadraticMap.IsometryEquiv.refl _).prod e)).2 h1)

end Decomposition

theorem card_orthogonalGroup_plus_four {K : Type} [Field K] [Finite K] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q' : QuadraticForm K W}
    (hK : Nat.card K = 3) (hnd : Q'.polarBilin.Nondegenerate) (hdim : finrank K W = 4)
    (hp : IsPlusType Q') : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') = 1152 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd (m := 1) hdim
    (ε := 1) (Or.inl ⟨rfl, hp⟩)
  have h' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') : ℤ) = 1152 := by
    rw [h, hK]
    norm_num [Finset.Icc_self]
  exact_mod_cast h'

theorem dvd_card_comap_orthogonalDerived {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {X : Type} [Group X] [Finite X]
    (φ : X →* TauCeti.QuadraticMap.orthogonalGroup Q) (hX : Nat.card X = 1152)
    (hidx : (orthogonalDerived Q).index = 4) :
    32 ∣ Nat.card ((orthogonalDerived Q).comap φ) := by
  have h1 : ((orthogonalDerived Q).comap φ).index ∣ 4 := by
    rw [Subgroup.index_comap, ← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have h2 := ((orthogonalDerived Q).comap φ).card_mul_index
  rw [hX] at h2
  set i := ((orthogonalDerived Q).comap φ).index with hi
  have hi4 : i ≤ 4 := Nat.le_of_dvd (by norm_num) h1
  obtain ⟨j, hj⟩ := h1
  interval_cases i <;> omega

end CFSG.ComponentClassification.CatLeafProof.X11Char
