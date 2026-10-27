module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CCaseA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CCaseB

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Module QuadraticMap CliffordAlgebra
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem caseA_choose {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (center Y) = 2)
    (α : MulAut Y) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e)
    (φ : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))
    (hQ0 : ∃ v, qM K b c v ≠ 0) (Φ : Y ≃* spinGroup (quadMinus 4 K b c))
    (hΦ : ∀ y : Y, φ (QuotientGroup.mk y) = spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) (Φ y))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
    (hsim : ∀ x, qM K b c (A x) = (μ : K) * qM K b c x)
    (hconj : ∀ x, thetaOf φ hQ0 (barAut α x) =
      projectiveConjugation (qM K b c) A μ hsim (thetaOf φ hQ0 x))
    {W W' : Submodule K (Fin (2 * 4) → K)}
    (ι : orthogonalOperatorCentralizer (qM K b c) A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup ((qM K b c).comp W.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup ((qM K b c).comp W'.subtype))
    (hcompl : IsCompl W W') (horth : ∀ x ∈ W, ∀ y ∈ W', polar (qM K b c) x y = 0)
    (hnd₁ : ((qM K b c).comp W.subtype).polarBilin.Nondegenerate)
    (hnd₂ : ((qM K b c).comp W'.subtype).polarBilin.Nondegenerate)
    (hι : ∀ h (x : W) (y : W'), (ι.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧ center Y ≤ N := by
  have hdim : finrank K (Fin (2 * 4) → K) = 8 := by simp
  have hnp := Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 one_le_four' hirr
  have horth2 : ∀ x ∈ W', ∀ y ∈ W, polar (qM K b c) x y = 0 := fun x hx y hy => by
    rw [polar_comm]; exact horth y hy x hx
  have hι2 : ∀ h (x : W') (y : W), ((ι.trans MulEquiv.prodComm).symm h).val.val (x.val + y.val)
      = (h.1.val x).val + (h.2.val y).val := by
    intro h x y
    rw [add_comm x.val y.val, add_comm (h.1.val x).val]
    exact hι (h.2, h.1) y x
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hdim] at hsum
  by_cases h5 : 5 ≤ finrank K W
  · exact caseA_core hZ α hirr hp hp2 hK φ hQ0 Φ hΦ A μ hsim hconj ι hcompl horth hnd₁ hι
      (Or.inl h5)
  by_cases h5' : 5 ≤ finrank K W'
  · exact caseA_core hZ α hirr hp hp2 hK φ hQ0 Φ hΦ A μ hsim hconj
      (ι.trans MulEquiv.prodComm) hcompl.symm horth2 hnd₂ hι2 (Or.inl h5')
  by_cases hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, ((qM K b c).comp W.subtype) x = 0
  · by_cases hS' : ∃ S : Submodule K W', finrank K S = 2 ∧
        ∀ x ∈ S, ((qM K b c).comp W'.subtype) x = 0
    · exact absurd (isPlusType_of_split hcompl horth hdim hS hS') hnp
    · exact caseA_core hZ α hirr hp hp2 hK φ hQ0 Φ hΦ A μ hsim hconj
        (ι.trans MulEquiv.prodComm) hcompl.symm horth2 hnd₂ hι2 (Or.inr ⟨by omega, hS'⟩)
  · exact caseA_core hZ α hirr hp hp2 hK φ hQ0 Φ hΦ A μ hsim hconj ι hcompl horth hnd₁ hι
      (Or.inr ⟨by omega, hS⟩)

theorem caseA_concl {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (center Y) = 2)
    (α : MulAut Y) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (φ : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))
    (hQ0 : ∃ v, qM K b c v ≠ 0) (Φ : Y ≃* spinGroup (quadMinus 4 K b c))
    (hΦ : ∀ y : Y, φ (QuotientGroup.mk y) = spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) (Φ y))
    (D : AutModel (qM K b c) (thetaOf φ hQ0) (barAut α)) (β : Kˣ)
    (hβ : (D.c : K) = (β : K) ^ 2) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧ center Y ≤ N := by
  have hnd := (regular_coordinateQuadMinus (n := 4) K b c (le_refl 4) hirr).1
  have hsim := matrix_similarity (qM K b c) D.g D.hg
  have hsimP := polar_similarity (qM K b c) (matrixLinearEquiv D.g.val.left) _ hsim
  obtain ⟨-, -, hA, -⟩ := scalar_square_centralizer_structure p e hp hp2 he hK (by simp)
    (qM K b c) hnd (matrixLinearEquiv D.g.val.left) D.c (multiplier _ D.g) D.hsq hsimP D.hns
  have hμd : (multiplier (qM K b c) D.g : K) / (D.c : K) = 1 := by
    rw [D.hμc]; exact div_self (Units.ne_zero _)
  obtain ⟨hcompl, -, -, hpos, -⟩ := hA β hβ
  obtain ⟨horth, hnd₁, hnd₂, ι, -, -, hι⟩ := hpos hμd
  exact caseA_choose hZ α hirr hp hp2 hK φ hQ0 Φ hΦ _ _ hsim D.hconj ι hcompl horth hnd₁ hnd₂ hι

theorem cent516_omega {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y)
    (hZ : Nat.card (center Y) = 2) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hm : Blueprint.LieModel (Y ⧸ center Y) .POmegaMinus 4 p e) (α : MulAut Y)
    (hα : α ^ 2 = 1) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧
      (center Y ≤ N ∨ ((∀ t : Y, α ≠ MulAut.conj t) ∧ 4 ∣ Nat.card N)) := by
  have := hY.1
  have hstated := GH74.statedClassicalModel_of_lieModel (by norm_num) hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨φ⟩⟩ := id hstated
  obtain ⟨Φ, hΦ⟩ := exists_equiv_spinMinus hZ hirr hp hp2 hK φ
  have hQ0 := qM_ne_zero hirr
  by_cases h1 : barAut α = 1
  · have hM : ⁅(⊤ : Subgroup (Y ⧸ center Y)), (⊤ : Subgroup (Y ⧸ center Y))⁆ =
        (⊤ : Subgroup (Y ⧸ center Y)) := by
      rw [← range_piZ, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have hN : liftN (piZ (Y := Y)) ⊤ = ⊤ := by
      rw [liftN, Subgroup.comap_top, ← commutator_def, Group.IsPerfect.commutator_eq_top]
    refine ⟨liftN (piZ (Y := Y)) ⊤, fixed_lift α hM (fun x _ => by rw [h1]; rfl),
      liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ ⊤), Or.inl ?_⟩
    rw [hN]
    exact le_top
  have hord : orderOf (barAut α) = 2 := orderOf_eq_prime (barAut_sq hα) h1
  obtain ⟨D⟩ := exists_autModel hp hp2 he hstated K hK b c hirr φ hQ0 (barAut α) hord
  by_cases hsq : IsSquare (D.c : K)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact Units.ne_zero _ hr
    obtain ⟨N, hfix, hN, hZN⟩ := caseA_concl hZ α hirr hp hp2 he hK φ hQ0 Φ hΦ D
      (Units.mk0 r hr0) (by rw [Units.val_mk0, hr, _root_.sq])
    exact ⟨N, hfix, hN, Or.inl hZN⟩
  · obtain ⟨M, hM, hfix, h4, hout⟩ := caseB_concl hp hp2 he hK hirr φ hQ0 (barAut α) D hsq
    obtain ⟨N, hNfix, hN, hNout, hN4⟩ := concl_outer α hM hfix hout h4
    exact ⟨N, hNfix, hN, Or.inr ⟨hNout, hN4⟩⟩

end CFSG.ComponentClassification.GSThmB.Cent516
