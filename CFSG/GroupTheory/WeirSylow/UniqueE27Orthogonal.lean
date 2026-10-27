module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Open.StatedDefs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaOddOrder
import CFSG.GroupTheory.UniqueElemSylowProj
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem uniqueElemSylow_isometryCore_of_orthogonalGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    {p k : ℕ} (h : UniqueElemSylow p k (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    UniqueElemSylow p k (CFSG.MatrixModel.isometryCore Q₀) := by
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup Q).map (toLinEquiv ι K).symm.toMonoidHom =
      CFSG.MatrixModel.isometryCore Q₀ :=
    (Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι K) _).symm.trans
      (closure_isometries_eq_comap hQ).symm
  exact UniqueElemSylow.of_mulEquiv
    (((toLinEquiv ι K).symm.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)) h

theorem apply_mulVec_of_mem_isometryCore {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q₀ : (ι → K) → K} {g : GL ι K} (hg : g ∈ CFSG.MatrixModel.isometryCore Q₀)
    (v : ι → K) : Q₀ (Matrix.mulVec (g : Matrix ι ι K) v) = Q₀ v := by
  open Matrix in
  unfold CFSG.MatrixModel.isometryCore at hg
  induction hg using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    have := hx ((↑x⁻¹ : Matrix ι ι K) *ᵥ v)
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, eq_comm] at this

theorem statedOmega_le_isometryCore {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q₀ : (ι → K) → K) : StatedOmega Q₀ ≤ CFSG.MatrixModel.isometryCore Q₀ :=
  open Matrix in
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
    (Subgroup.inv_mem _ h₂)

theorem uniqueElemSylow_statedOmega_of_isometryCore {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {Q₀ : (ι → K) → K} {p k : ℕ} [Fact p.Prime] (hp : ¬ p ∣ 2)
    (hsq : ∀ g : GL ι K, (∀ v, Q₀ (Matrix.mulVec (g : Matrix ι ι K) v) = Q₀ v) →
      g ^ 2 ∈ StatedOmega Q₀)
    (h : UniqueElemSylow p k (CFSG.MatrixModel.isometryCore Q₀)) :
    UniqueElemSylow p k (StatedOmega Q₀) := by
  open Matrix in
  refine (UniqueElemSylow.subgroup_of_pow_mem
    ((StatedOmega Q₀).subgroupOf (CFSG.MatrixModel.isometryCore Q₀)) hp (fun g => ?_)
    h).of_mulEquiv (Subgroup.subgroupOfEquivOfLe (statedOmega_le_isometryCore Q₀))
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  exact hsq g.1 (apply_mulVec_of_mem_isometryCore g.2)

theorem sq_eq_one_of_scalar_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q₀ : (ι → K) → K} (hhom : ∀ (c : K) (v : ι → K), Q₀ (c • v) = c ^ 2 * Q₀ v)
    {w : ι → K} (hw : Q₀ w ≠ 0) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar ι c ∈ StatedOmega Q₀) : c ^ 2 = 1 := by
  open Matrix in
  have h1 := apply_mulVec_of_mem_isometryCore (statedOmega_le_isometryCore Q₀ hc) w
  have h2 : ((GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ w = (c : K) • w := by
    rw [GeneralLinearGroup.coe_scalar]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [h2, hhom] at h1
  have : (c : K) ^ 2 = 1 := mul_right_cancel₀ hw (h1.trans (one_mul _).symm)
  exact Units.ext (by simpa using this)

theorem uniqueElemSylow_orthogonalGroup_quadOdd_three (K : Type) [Field K] [Finite K]
    (hK2 : Odd (Nat.card K)) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) := by
  open CFSG.LieType.Universal.Spin Module in
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK2 hK3
  have hring : ringChar K ≠ 2 := fun h =>
    absurd (FiniteField.even_card_iff_char_two.1 h) (by rw [Nat.odd_iff] at hK2; omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hring
  have hnd := nondegenerate_polarBilin_quadOdd 3 K h2
  have hdim : finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 2 * 3 + 1 := by simp
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) := inferInstance
  refine uniqueElemSylow_of_sylow_mulEquiv_statedSp K (by rwa [Nat.card_eq_fintype_card])
    fun P => ?_
  obtain ⟨P'⟩ : Nonempty (Sylow 3 (StatedSp 3 K)) := inferInstance
  exact ⟨P', sylow_orthogonal_odd (by decide) hK2 hK3 hdim _ hnd P P'⟩

theorem uniqueElemSylow_orthogonalGroup_quadMinus_four (K : Type) [Field K] [Finite K] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) := by
  open CFSG.LieType.Universal.Spin Module in
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK3
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 4 K hbc
  have hdim : finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 2 * 4 :=
    finrank_quadMinus_space (by norm_num)
  have hε : ((-1 : ℤ) = 1 ∧ IsPlusType (quadMinus 4 K b c)) ∨
      ((-1 : ℤ) = -1 ∧ IsMinusType (quadMinus 4 K b c)) :=
    Or.inr ⟨rfl,
      CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega.isMinusType_quadMinus
        (by norm_num) hbc⟩
  have hq3 : ¬ ((3 : ℕ) : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 - (-1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h0 : ((Fintype.card K : ℕ) : ZMod 3) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    push_cast
    revert h0
    generalize ((Fintype.card K : ℕ) : ZMod 3) = x
    revert x
    decide
  refine uniqueElemSylow_of_sylow_mulEquiv_statedSp K (by rwa [Nat.card_eq_fintype_card])
    fun P => ?_
  obtain ⟨P'⟩ : Nonempty (Sylow 3 (StatedSp 3 K)) := inferInstance
  exact ⟨P', (sylow_orthogonal_even (by decide) hK3 (by norm_num) hdim _ hnd hε P).2.1 hq3 P'⟩

theorem uniqueElemSylow_statedOmega_quadOdd_three (K : Type) [Field K] [Finite K]
    (hK2 : Odd (Nat.card K)) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (StatedOmega (StatedQuadOdd 3 K)) := by
  open CFSG.LieType.Universal.Spin in
  letI := Fintype.ofFinite K
  have hring : ringChar K ≠ 2 := fun h =>
    absurd (FiniteField.even_card_iff_char_two.1 h)
      (by rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hK2; omega)
  exact uniqueElemSylow_statedOmega_of_isometryCore (by decide)
    (fun g hg => sq_mem_statedOmega_quadOdd hring g hg)
    (uniqueElemSylow_isometryCore_of_orthogonalGroup (coe_quadOdd 3 K)
      (uniqueElemSylow_orthogonalGroup_quadOdd_three K hK2 hK3))

theorem uniqueElemSylow_statedOmega_quadMinus_four (K : Type) [Field K] [Finite K] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (StatedOmega (StatedQuadMinus 4 K b c)) :=
  open CFSG.LieType.Universal.Spin in
  uniqueElemSylow_statedOmega_of_isometryCore (by decide)
    (fun g hg => sq_mem_statedOmega_quadMinus b c hbc g hg)
    (uniqueElemSylow_isometryCore_of_orthogonalGroup (coe_quadMinus 4 K b c)
      (uniqueElemSylow_orthogonalGroup_quadMinus_four K hbc hK3))

theorem uniqueElemSylow_statedProj_statedOmega_quadOdd_three (K : Type) [Field K] [Finite K]
    (hK2 : Odd (Nat.card K)) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
  open CFSG.LieType.Universal.Spin in
  refine UniqueElemSylow.statedProj (d := 2) (by decide)
    (fun c hc => sq_eq_one_of_scalar_mem_statedOmega (w := Pi.single (.inr (.inr ())) 1) ?_ ?_ hc)
    (uniqueElemSylow_statedOmega_quadOdd_three K hK2 hK3)
  · intro c v
    rw [← coe_quadOdd 3 K, QuadraticMap.map_smul, smul_eq_mul, sq]
  · simp [StatedQuadOdd, Pi.single_apply]

theorem uniqueElemSylow_statedProj_statedOmega_quadMinus_four (K : Type) [Field K] [Finite K]
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK3 : ¬ 3 ∣ Nat.card K) :
    UniqueElemSylow 3 3 (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  open CFSG.LieType.Universal.Spin in
  refine UniqueElemSylow.statedProj (d := 2) (by decide)
    (fun a ha => sq_eq_one_of_scalar_mem_statedOmega (w := Pi.single (.inr (.inr 0)) 1) ?_ ?_ ha)
    (uniqueElemSylow_statedOmega_quadMinus_four K hbc hK3)
  · intro a v
    rw [← coe_quadMinus 4 K b c, QuadraticMap.map_smul, smul_eq_mul, sq]
  · simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]

end CFSG.GroupTheory.WeirSylow
