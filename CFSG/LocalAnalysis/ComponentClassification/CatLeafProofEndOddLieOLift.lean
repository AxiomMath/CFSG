module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Burgoyne.O (linPair linPair_left linPair_right)
open scoped commutatorElement

section Commute

variable {G : Type*} [Group G]

theorem commute_of_comm_commutator {F : Subgroup G} (hF : ⁅F, F⁆ = F) {x : G}
    (h1 : ∀ f ∈ F, ∀ f' ∈ F, f⁻¹ * x⁻¹ * f * x * f' = f' * (f⁻¹ * x⁻¹ * f * x))
    (h2 : ∀ f ∈ F, ∀ f' ∈ F, f⁻¹ * x⁻¹ * f * x * (f'⁻¹ * x⁻¹ * f' * x) =
      f'⁻¹ * x⁻¹ * f' * x * (f⁻¹ * x⁻¹ * f * x)) :
    ∀ f ∈ F, f * x = x * f := by
  let φ : F →* G :=
    { toFun := fun f => (f : G)⁻¹ * x⁻¹ * f * x
      map_one' := by simp
      map_mul' := fun f₁ f₂ => by
        have h := h1 f₁ f₁.2 ((f₂ : G)⁻¹) (inv_mem f₂.2)
        change ((f₁ : G) * f₂)⁻¹ * x⁻¹ * (f₁ * f₂) * x =
          (f₁ : G)⁻¹ * x⁻¹ * f₁ * x * ((f₂ : G)⁻¹ * x⁻¹ * f₂ * x)
        calc ((f₁ : G) * f₂)⁻¹ * x⁻¹ * (f₁ * f₂) * x
            = (f₂ : G)⁻¹ * ((f₁ : G)⁻¹ * x⁻¹ * f₁ * x) * (x⁻¹ * f₂ * x) := by group
          _ = (f₁ : G)⁻¹ * x⁻¹ * f₁ * x * (f₂ : G)⁻¹ * (x⁻¹ * f₂ * x) := by rw [← h]
          _ = (f₁ : G)⁻¹ * x⁻¹ * f₁ * x * ((f₂ : G)⁻¹ * x⁻¹ * f₂ * x) := by group }
  have hle : ⁅F, F⁆ ≤ φ.ker.map F.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : F), ⟨b, hb⟩⁆, ?_, rfl⟩
    change φ ⁅(⟨a, ha⟩ : F), ⟨b, hb⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h2 a ha b hb
  intro f hf
  have hf' : f ∈ ⁅F, F⁆ := by rw [hF]; exact hf
  obtain ⟨f', hf'k, rfl⟩ := hle hf'
  have h0 : (f' : G)⁻¹ * x⁻¹ * f' * x = 1 := MonoidHom.mem_ker.mp hf'k
  show (f' : G) * x = x * f'
  calc (f' : G) * x = x * (f' * ((f' : G)⁻¹ * x⁻¹ * f' * x)) := by group
    _ = x * f' := by rw [h0, mul_one]

theorem commute_of_commutator_mem_center {F : Subgroup G} (hF : ⁅F, F⁆ = F) {x : G}
    (hx : ∀ f ∈ F, f⁻¹ * x⁻¹ * f * x ∈ center G) : ∀ f ∈ F, f * x = x * f :=
  commute_of_comm_commutator hF (fun f hf f' _ => (mem_center_iff.mp (hx f hf) f').symm)
    (fun f hf _ _ => (mem_center_iff.mp (hx f hf) _).symm)

theorem commute_of_commutator_mem_center_self {F : Subgroup G} (hF : ⁅F, F⁆ = F) {x : G}
    (hx : ∀ f ∈ F, f⁻¹ * x⁻¹ * f * x ∈ (center F).map F.subtype) : ∀ f ∈ F, f * x = x * f := by
  refine commute_of_comm_commutator hF (fun f hf f' hf' => ?_) (fun f hf f' hf' => ?_)
  · obtain ⟨c, hc, hcf⟩ := hx f hf
    rw [← hcf]
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨f', hf'⟩).symm
  · obtain ⟨c, hc, hcf⟩ := hx f hf
    obtain ⟨c', -, hcf'⟩ := hx f' hf'
    rw [← hcf, ← hcf']
    exact congrArg Subtype.val (mem_center_iff.mp hc c').symm

end Commute

theorem fixedSubgroup_conj_eq {G : Type*} [Group G] (x : G) :
    fixedSubgroup (MulAut.conj x) = centralizer ({x} : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj x g = g ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

variable {K : Type} [Field K] {d : ℕ}

theorem matrixProjectiveConjugationHom_linPair (Q : QuadraticForm K (Fin d → K))
    (W : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (linPair W.val (matrixDerived_le_isometries Q W.2)) =
      MulAut.conj (matrixProjectiveProjection Q W) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨X, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q X) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem commutant_linPair (Q : QuadraticForm K (Fin d → K)) (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) :
    commutant (coordinateSemilinearMap (linPair A hA).val) =
      CatalogueBProjectiveInvolution.operatorCentralizer (matrixLinearEquiv A).toLinearMap := by
  have hτ : ∀ v, coordinateSemilinearMap (linPair A hA).val v = matrixLinearEquiv A v := by
    intro v
    rw [coordinateSemilinearMap_apply, linPair_right]
    rfl
  ext u
  rw [mem_commutant]
  change _ ↔ ∀ x, u (matrixLinearEquiv A x) = matrixLinearEquiv A (u x)
  simp only [hτ]

theorem exists_scalar_sq (Q : QuadraticForm K (Fin d → K)) (W : matrixDerived Q)
    (hw : matrixProjectiveProjection Q W * matrixProjectiveProjection Q W = 1) :
    ∃ c : Kˣ, W.val * W.val = GeneralLinearGroup.scalar (Fin d) c := by
  have h1 : W * W ∈ (matrixProjectiveProjection Q).ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hw
  rw [matrixProjectiveProjection, QuotientGroup.ker_mk'] at h1
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp h1
  exact ⟨c, hc.symm⟩

theorem scalar_ne_of_ne_one (Q : QuadraticForm K (Fin d → K)) (W : matrixDerived Q)
    (hw : matrixProjectiveProjection Q W ≠ 1) (a : Kˣ) :
    GeneralLinearGroup.scalar (Fin d) a ≠ W.val := by
  intro ha
  apply hw
  have h1 : W ∈ matrixDerivedScalars Q := (mem_matrixDerivedScalars_iff Q W).mpr ⟨a, ha⟩
  have h2 : W ∈ (matrixProjectiveProjection Q).ker := by
    rw [matrixProjectiveProjection, QuotientGroup.ker_mk']
    exact h1
  exact MonoidHom.mem_ker.mp h2

@[expose] def liftHat (Q : QuadraticForm K (Fin d → K))
    (X : Subgroup (matrixProjectiveDerived Q)) : Subgroup (matrixDerived Q) :=
  ⁅X.comap (matrixProjectiveProjection Q), X.comap (matrixProjectiveProjection Q)⁆

theorem inner_lift [Finite K] (Q : QuadraticForm K (Fin d → K)) (W : matrixDerived Q)
    (hw : matrixProjectiveProjection Q W * matrixProjectiveProjection Q W = 1)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X
      (centralizer ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)))) :
    CFSG.Assembly.IsComponentOf (liftHat Q X) (fixedSubgroup (matrixDerivedConjugation Q
        (linPair W.val (matrixDerived_le_isometries Q W.2)))) ∧
      (liftHat Q X).map (matrixProjectiveProjection Q) = X ∧
      CFSG.Assembly.IsComponentOf ((liftHat Q X).map (derivedLinear Q))
        (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
          CatalogueBProjectiveInvolution.operatorCentralizer
            (matrixLinearEquiv W.val).toLinearMap) ∧
      (liftHat Q X).map (derivedLinear Q) ≤ orthogonalOmega Q ∧
      ∃ σ : (liftHat Q X).map (derivedLinear Q) →* X, Function.Surjective σ ∧
        σ.ker ≤ center ((liftHat Q X).map (derivedLinear Q)) := by
  classical
  obtain ⟨c, hc⟩ := exists_scalar_sq Q W hw
  have hσ : (linPair W.val (matrixDerived_le_isometries Q W.2)).val.right ^ 2 = 1 := by
    rw [linPair_right, one_pow]
  have hc' : ∃ c : Kˣ, (linPair W.val (matrixDerived_le_isometries Q W.2)).val.left *
      CatalogueBHigherLinearField.glFieldAut (Fin d) K
        (linPair W.val (matrixDerived_le_isometries Q W.2)).val.right
        (linPair W.val (matrixDerived_le_isometries Q W.2)).val.left =
      GeneralLinearGroup.scalar (Fin d) c :=
    ⟨c, by rw [linPair_left, linPair_right, map_one, MulAut.one_apply]; exact hc⟩
  have hX' : CFSG.Assembly.IsComponentOf X (fixedSubgroup (matrixProjectiveConjugationHom Q
      (linPair W.val (matrixDerived_le_isometries Q W.2)))) := by
    rw [matrixProjectiveConjugationHom_linPair, fixedSubgroup_conj_eq]
    exact hX
  obtain ⟨-, hYm, hYmap, -⟩ := LocalAnalysis.ComponentInitial.lift_isComponentOf_fixed
    (π := matrixProjectiveProjection Q) (a := matrixDerivedConjugation Q _)
    (α := matrixProjectiveConjugationHom Q _)
    (matrixProjectiveProjection_surjective Q) (ker_matrixProjectiveProjection_le Q)
    (matrixDerivedConjugation_involutive Q _ hσ hc') (matrixProjective_comm Q _) hX'
  have hYmap' : (liftHat Q X).map (matrixProjectiveProjection Q) = X := hYmap
  have hJi := derivedLinear_injective Q
  have hYc1 : CFSG.Assembly.IsComponentOf ((liftHat Q X).map (derivedLinear Q))
      (orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap
        (linPair W.val (matrixDerived_le_isometries Q W.2)).val)) := by
    rw [← map_derivedLinear_fixed]
    exact SymmetricLocal.isComponentOf_map_of_injective (derivedLinear Q) hJi hYm
  rw [commutant_linPair] at hYc1
  have hle : orthogonalOmega Q ⊓ CatalogueBProjectiveInvolution.operatorCentralizer
        (matrixLinearEquiv W.val).toLinearMap ≤
      TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        CatalogueBProjectiveInvolution.operatorCentralizer
          (matrixLinearEquiv W.val).toLinearMap :=
    inf_le_inf_right _ (Subgroup.commutator_le_self _)
  have hnorm : ((orthogonalOmega Q ⊓ CatalogueBProjectiveInvolution.operatorCentralizer
      (matrixLinearEquiv W.val).toLinearMap).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ CatalogueBProjectiveInvolution.operatorCentralizer
        (matrixLinearEquiv W.val).toLinearMap)).Normal := by
    rw [normal_subgroupOf_iff hle]
    intro h k hh hk
    rw [Subgroup.mem_inf] at hh hk ⊢
    refine ⟨?_, mul_mem (mul_mem hk.2 hh.2) (inv_mem hk.2)⟩
    exact (mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_left _ _ hk.1) h).mp hh.1
  let eY : liftHat Q X ≃* (liftHat Q X).map (derivedLinear Q) :=
    (liftHat Q X).equivMapOfInjective _ hJi
  have hρ : ∀ y : liftHat Q X, matrixProjectiveProjection Q y ∈ X := fun y => by
    have h := mem_map_of_mem (matrixProjectiveProjection Q) y.2
    rwa [hYmap'] at h
  let ρm : liftHat Q X →* X :=
    ((matrixProjectiveProjection Q).comp (liftHat Q X).subtype).codRestrict X hρ
  refine ⟨hYm, hYmap', isComponentOf_of_normal_le hYc1 hle hnorm, hYc1.1.trans inf_le_left,
    ρm.comp eY.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    have hx : (x : matrixProjectiveDerived Q) ∈
        (liftHat Q X).map (matrixProjectiveProjection Q) := by
      rw [hYmap']
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨eY ⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hyx
  · intro y hy
    have h1 : matrixProjectiveProjection Q (eY.symm y : matrixDerived Q) = 1 :=
      congrArg Subtype.val hy
    have h2 : (eY.symm y : matrixDerived Q) ∈ center (matrixDerived Q) :=
      ker_matrixProjectiveProjection_le Q h1
    rw [mem_center_iff] at h2 ⊢
    intro z
    apply eY.symm.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact h2 _

end CFSG.ComponentClassification.CatLeafProof.EndOddO
