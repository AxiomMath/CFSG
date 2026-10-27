module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Two
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Module QuadraticMap
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K]

theorem caseB_core {L : Type} [Group L] [Finite L] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (Θ : L ≃* projectiveDerived Q) (α : MulAut L) (A : V ≃ₗ[K] V)
    (μ : Kˣ) (hsim : ∀ x, Q (A x) = (μ : K) * Q x)
    (hconj : ∀ x, Θ (α x) = projectiveConjugation Q A μ hsim (Θ x)) (h2 : (2 : K) ≠ 0)
    {E : Type} [Field E] [Finite E] [Module E V] [FiniteDimensional E V]
    (hEodd : Odd (Nat.card E)) (QE : QuadraticForm E V) (hQE : QE.polarBilin.Nondegenerate)
    (hdimE : finrank E V = 4) (hno : ¬ ∃ S : Submodule E V, finrank E S = 2 ∧ ∀ x ∈ S, QE x = 0)
    (ι : orthogonalOperatorCentralizer Q A.toLinearMap ≃* TauCeti.QuadraticMap.orthogonalGroup QE)
    (hιs : ∀ g x, (ι.symm g).val.val x = g.val x) :
    ∃ M : Subgroup L, ⁅M, M⁆ = M ∧ (∀ x ∈ M, α x = x) ∧ 4 ∣ Nat.card M := by
  have h2E : (2 : E) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hEodd QE hQE hdimE hno
  have hF := hq.1.commutator_eq_top
  set f : commutator (TauCeti.QuadraticMap.orthogonalGroup QE) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    (orthogonalOperatorCentralizer Q A.toLinearMap).subtype.comp
      (ι.symm.toMonoidHom.comp (commutator _).subtype) with hf
  have hfv : ∀ a x, (f a).val x = a.val.val x := fun a x => hιs a.val x
  have hfA : ∀ a v, (f a).val (A v) = A ((f a).val v) := fun a v =>
    (ι.symm a.val).property v
  obtain ⟨eb, heo, hQe⟩ := Catalog7Std.Om8.exists_unit_orthogonal_basis hEodd hQE (by omega)
  have hl : ∀ i : ℕ, i < 3 → i < finrank E V := fun i hi => by omega
  have hm : ∀ i : ℕ, i < 3 → i < finrank E V - 1 := fun i hi => by omega
  set e₀ := eb ⟨0, hl 0 (by norm_num)⟩
  set e₁ := eb ⟨1, hl 1 (by norm_num)⟩
  set e₂ := eb ⟨2, hl 2 (by norm_num)⟩
  have hq₀ : QE e₀ = 1 := hQe _ (hm 0 (by norm_num))
  have hq₁ : QE e₁ = 1 := hQe _ (hm 1 (by norm_num))
  have hq₂ : QE e₂ = 1 := hQe _ (hm 2 (by norm_num))
  have hne : ∀ i j : ℕ, (hi : i < 3) → (hj : j < 3) → i ≠ j →
      polar QE (eb ⟨i, hl i hi⟩) (eb ⟨j, hl j hj⟩) = 0 :=
    fun i j hi hj hij => heo _ _ (fun h => hij (congrArg Fin.val h))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := reflect_klein (Q := QE)
    (by rw [hq₀]; exact one_ne_zero) (by rw [hq₁]; exact one_ne_zero)
    (by rw [hq₂]; exact one_ne_zero) (hne 0 1 (by norm_num) (by norm_num) (by norm_num))
    (hne 0 2 (by norm_num) (by norm_num) (by norm_num))
    (hne 1 2 (by norm_num) (by norm_num) (by norm_num))
  set a : commutator (TauCeti.QuadraticMap.orthogonalGroup QE) :=
    ⟨⟨_, mul_mem (reflect_mem_orthogonalGroup _ e₀) (reflect_mem_orthogonalGroup _ e₁)⟩,
      Catalog7Std.Om8.reflect_mul_reflect_mem_commutator h2E hq₀ hq₁⟩
  set b : commutator (TauCeti.QuadraticMap.orthogonalGroup QE) :=
    ⟨⟨_, mul_mem (reflect_mem_orthogonalGroup _ e₀) (reflect_mem_orthogonalGroup _ e₂)⟩,
      Catalog7Std.Om8.reflect_mul_reflect_mem_commutator h2E hq₀ hq₂⟩
  have ha : a * a = 1 := Subtype.ext (Subtype.ext k1)
  have hb : b * b = 1 := Subtype.ext (Subtype.ext k2)
  have hab : Commute a b := Subtype.ext (Subtype.ext k3)
  have hn₀ : e₀ ≠ 0 := eb.ne_zero _
  have hn₁ : e₁ ≠ 0 := eb.ne_zero _
  have hn₂ : e₂ ≠ 0 := eb.ne_zero _
  refine ⟨imgL Θ hF f, imgL_perfect Θ hF f, imgL_fixed Θ hF f α A μ hsim hconj hfA,
    four_dvd_card_imgL Θ hF f ha hb hab ?_ ?_ ?_⟩
  · exact not_mem_scalarSigns h2 (f a) hn₁ hn₂ (by rw [hfv]; exact k4) (by rw [hfv]; exact k5)
  · exact not_mem_scalarSigns h2 (f b) hn₂ hn₁ (by rw [hfv]; exact k6) (by rw [hfv]; exact k7)
  · exact not_mem_scalarSigns h2 (f (a * b)) hn₁ hn₀ (by rw [hfv]; exact k8)
      (by rw [hfv]; exact k9)

variable {b c : K}

theorem isSquare_of_inner {L : Type} [Group L]
    {φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))} {hQ0 : ∃ v, qM K b c v ≠ 0}
    {α : MulAut L} (D : AutModel (qM K b c) (thetaOf φ hQ0) α) (h : ∃ x, α = MulAut.conj x) :
    IsSquare (D.c : K) := by
  obtain ⟨a, Dm, hDm, hDeq⟩ := D.hinner h
  obtain ⟨v, hv⟩ := hQ0
  have hiso : ∀ w, qM K b c (matrixLinearEquiv Dm w) = qM K b c w := fun w =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (matrixDerived_le_isometries _ hDm) w
  have h1 := matrix_similarity _ D.g D.hg v
  rw [hDeq, matrixLinearEquiv_mul, LinearEquiv.mul_apply, matrixLinearEquiv_scalar, hiso,
    QuadraticMap.map_smul, smul_eq_mul, D.hμc] at h1
  exact ⟨a, (mul_right_cancel₀ hv h1).symm⟩

theorem caseB_concl [Finite K] {L : Type} [Group L] [Finite L] {r e : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = r ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hQ0 : ∃ v, qM K b c v ≠ 0)
    (α : MulAut L) (D : AutModel (qM K b c) (thetaOf φ hQ0) α) (hns : ¬ IsSquare (D.c : K)) :
    ∃ M : Subgroup L, ⁅M, M⁆ = M ∧ (∀ x ∈ M, α x = x) ∧ 4 ∣ Nat.card M ∧
      ∀ x, α ≠ MulAut.conj x := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hr.odd_of_ne_two hr2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hnd := (regular_coordinateQuadMinus (n := 4) K b c (le_refl 4) hirr).1
  have hdim : finrank K (Fin (2 * 4) → K) = 8 := by simp
  have hnp := Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 one_le_four' hirr
  have : Nontrivial (Fin (2 * 4) → K) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsim := matrix_similarity (qM K b c) D.g D.hg
  have hsimP := polar_similarity (qM K b c) (matrixLinearEquiv D.g.val.left) _ hsim
  obtain ⟨-, -, -, hB⟩ := scalar_square_centralizer_structure r e hr hr2 he hK (by omega)
    (qM K b c) hnd (matrixLinearEquiv D.g.val.left) D.c (multiplier _ D.g) D.hsq hsimP D.hns
  have hμd : (multiplier (qM K b c) D.g : K) / (D.c : K) = 1 := by
    rw [D.hμc]; exact div_self (Units.ne_zero _)
  obtain ⟨-, hpos, -⟩ := hB hns
  obtain ⟨-, -, -, hQEnd, -, -, ι, -, hιs, -, -⟩ := hpos hμd
  have hs := original_endomorphism_square (matrixLinearEquiv D.g.val.left) D.c D.hsq
  let := scalarField (matrixLinearEquiv D.g.val.left).toLinearMap (D.c : K) hns hs
  let := evaluationModule (matrixLinearEquiv D.g.val.left).toLinearMap
  let := evaluationScalarTower (matrixLinearEquiv D.g.val.left).toLinearMap
  let := scalarAlgebra_finite_type (matrixLinearEquiv D.g.val.left).toLinearMap (D.c : K) hns hs
  let := evaluationModule_finite (matrixLinearEquiv D.g.val.left).toLinearMap
  have hE : Nat.card (scalarAlgebra (matrixLinearEquiv D.g.val.left).toLinearMap) =
      r ^ (2 * e) := by
    rw [scalarAlgebra_card _ _ hns hs, hK, ← pow_mul, mul_comm]
  have hEodd : Odd (Nat.card (scalarAlgebra (matrixLinearEquiv D.g.val.left).toLinearMap)) := by
    rw [hE]; exact (hr.odd_of_ne_two hr2).pow
  have hdimE : finrank (scalarAlgebra (matrixLinearEquiv D.g.val.left).toLinearMap)
      (Fin (2 * 4) → K) = 4 := by
    rw [evaluationModule_finrank_div_two _ _ hns hs, hdim]
  have hno := Catalog7Std.Om8.actualPositive_not_split hodd (qM K b c) hdim hnp
    (matrixLinearEquiv D.g.val.left).toLinearMap (D.c : K)
    (Units.ne_zero _) hns hs (positive_square_adjoint (qM K b c) _ D.c _ (Units.ne_zero _)
      D.hsq hsimP hμd)
  obtain ⟨M, hM, hfix, h4⟩ := caseB_core (thetaOf φ hQ0) α _ _ hsim D.hconj h2 hEodd _ hQEnd
    hdimE hno ι hιs
  exact ⟨M, hM, hfix, h4, fun x hx => hns (isSquare_of_inner D ⟨x, hx⟩)⟩

end CFSG.ComponentClassification.GSThmB.Cent516
