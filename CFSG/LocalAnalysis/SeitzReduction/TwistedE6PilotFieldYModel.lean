module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.GroupTheory.WeirSylow.FieldTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldExtension
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)
open CFSG.GroupTheory.WeirSylow (binForm binForm_isometry quadMinusIsometry)

section Form

theorem coordinateQuadMinus_fieldMap {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n) (ρ : F ≃+* F)
    (b c : F) (v : Fin (2 * n) → F) :
    coordinateQuadMinus n F hn (ρ b) (ρ c) (coordinateFieldMap (2 * n) ρ v) =
      ρ (coordinateQuadMinus n F hn b c v) := by
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [coordinateFieldMap_apply, map_add, map_mul, map_sum, map_pow]

theorem coordinateQuadMinus_fieldMap_of_fixed {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n)
    {σ : F ≃+* F} {b c : F} (hb : σ b = b) (hc : σ c = c) (v : Fin (2 * n) → F) :
    coordinateQuadMinus n F hn b c (coordinateFieldMap (2 * n) σ v) =
      σ (coordinateQuadMinus n F hn b c v) := by
  have h := coordinateQuadMinus_fieldMap hn σ b c v
  rwa [hb, hc] at h

theorem isExtension_coordinateQuadMinus {K : Type} [Field K] (k : Subfield K) {n : ℕ}
    (hn : 1 ≤ n) (b c : k) :
    IsExtension k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) := by
  intro v
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp [vecIncl]

end Form

section Minus

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_mulEquiv_conj_fieldAutT_of_minus (hn : 1 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hσσ : S.val.right * S.val.right = 1) (hσ1 : S.val.right ≠ 1)
    (hTT : ∀ v, pairSemilinearMap S.val (pairSemilinearMap S.val v) = v)
    (b c : descentField S.val.right)
    (ι : (pairDescentForm hS).IsometryEquiv (quadMinus n (descentField S.val.right) b c))
    (hQ'σ : ∀ v, coordinateQuadMinus n K hn (b : K) (c : K)
      (coordinateFieldMap (2 * n) S.val.right v) =
        S.val.right (coordinateQuadMinus n K hn (b : K) (c : K) v)) :
    ∃ Θ : matrixProjectiveDerived Q ≃*
        matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c : K)),
      ∀ x, Θ (matrixProjectiveConjugationHom Q S x) =
        fieldAutT (coordinateQuadMinus n K hn (b : K) (c : K)) S.val.right hQ'σ (Θ x) := by
  obtain ⟨-, hbij, -, -, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  let b₀ : Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (descentField S.val.right) (pairFix S) :=
    (Pi.basisFun _ _).map ι.toLinearEquiv.symm
  have hrepr : ∀ (w : pairFix S) a, b₀.repr w a = ι w a := fun w a => by
    simp only [b₀, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr]
    rfl
  let φe := LinearEquiv.ofBijective (LinearMap.liftBaseChange K (pairFix S).subtype) hbij
  let bK : Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K (Fin (2 * n) → K) :=
    (b₀.baseChange K).map φe
  have hbK : ∀ a, bK a = ((b₀ a : pairFix S) : Fin (2 * n) → K) := fun a => by
    simp only [bK, Basis.map_apply, Basis.baseChange_apply]
    change LinearMap.liftBaseChange K (pairFix S).subtype (1 ⊗ₜ b₀ a) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hfix : ∀ a, coordinateSemilinearMap S.val (bK a) = bK a := fun a => by
    rw [hbK]
    exact (b₀ a).2
  have hcoord : ∀ (w : pairFix S) a,
      bK.equivFun (w : Fin (2 * n) → K) a = ((ι w a : descentField S.val.right) : K) := by
    intro w a
    have h1 : (w : Fin (2 * n) → K) =
        ∑ a', ((b₀.repr w a' : descentField S.val.right) : K) • bK a' := by
      conv_lhs => rw [← b₀.sum_repr w]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hbK]
      rfl
    rw [h1, Basis.equivFun_apply, bK.repr_sum_self, hrepr]
  obtain ⟨M, hM, hMS⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_extension_matrix
    (minusIndexEquiv n hn) S.val bK hfix
  have hMv : ∀ v, matrixLinearIso M v =
      fun j => bK.equivFun v ((minusIndexEquiv n hn).symm j) := hM
  have hagree : Q.comp (matrixLinearIso M).symm.toLinearMap =
      coordinateQuadMinus n K hn (b : K) (c : K) := by
    apply eq_of_agree (descentField S.val.right)
    intro c'
    rw [QuadraticMap.comp_apply]
    set w : pairFix S := ι.symm (fun a => c' (minusIndexEquiv n hn a)) with hw
    have hpre : (matrixLinearIso M).symm.toLinearMap (vecIncl (descentField S.val.right) c') =
        (w : Fin (2 * n) → K) := by
      change (matrixLinearIso M).symm (vecIncl (descentField S.val.right) c') = _
      rw [LinearEquiv.symm_apply_eq, hMv]
      funext j
      rw [hcoord w, hw, QuadraticMap.IsometryEquiv.apply_symm_apply]
      simp [vecIncl]
    rw [hpre, ← coe_descentForm (pairSemilinearMap_quad hS) w,
      isExtension_coordinateQuadMinus (descentField S.val.right) hn b c c']
    congr 1
    change pairDescentForm hS w = _
    rw [← ι.map_app w, hw, QuadraticMap.IsometryEquiv.apply_symm_apply]
    rfl
  have hiso : ∀ v, coordinateQuadMinus n K hn (b : K) (c : K) (matrixLinearIso M v) =
      ((1 : Kˣ) : K) * Q v := by
    intro v
    have h1 := congrArg (fun F : QuadraticForm K (Fin (2 * n) → K) => F (matrixLinearIso M v))
      hagree
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    rw [Units.val_one, one_mul, ← h1]
  refine ⟨CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv Q
    (coordinateQuadMinus n K hn (b : K) (c : K)) M 1 hiso, fun x => ?_⟩
  exact CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_conj Q
    (coordinateQuadMinus n K hn (b : K) (c : K)) M 1 hiso S
    (fieldPair (coordinateQuadMinus n K hn (b : K) (c : K)) S.val.right hQ'σ) rfl rfl hMS x

end Minus

section TypeDet


theorem false_of_lieModel_omegaPlus_omegaMinus {X : Type} [Group X] {m f m' f' : ℕ}
    (hp : LieModel X .POmegaPlus m 2 f) (hm : LieModel X .POmegaMinus m' 2 f') : False := by
  obtain ⟨htt, -, -⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
    (Or.inr rfl) hm (Or.inl (by decide)) hp rfl
  exact absurd htt (by decide)

theorem false_of_component_of_statedSp_omega {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {g r : ℕ} (hF : Nat.card F = 2 ^ g) (hg : 1 ≤ g) (hr : 3 ≤ r)
    (Φ : X ≃* StatedSp r F) {D : Subgroup X} (hD : CFSG.IsComponent D) {s : StatedLieTag}
    (hs : s = .POmegaPlus ∨ s = .POmegaMinus) {m f : ℕ} (hDm : LieModel D s m 2 f) : False := by
  have : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hF
  have hcond : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ r) ∨
      (Nat.card F = 2 ∧ 3 ≤ r) := by
    rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
    · exact Or.inr (Or.inr ⟨by rw [hF, pow_one], hr⟩)
    · refine Or.inl (Or.inr ?_)
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
  have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F r (by omega) hcond
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp r F) hF (by omega) ⟨MulEquiv.refl _⟩
  have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, by omega, fun h => by
    rw [Prod.mk.injEq] at h
    omega⟩
  have hXs : IsSimpleGroup X := (Φ.trans eProj.symm).isSimpleGroup
  have hmX : LieModel X .PSp r 2 g :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, ⟨Φ.trans eProj.symm⟩⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  obtain ⟨htt, -, -⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
    hs hDm (Or.inl (by decide)) (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX) rfl
  rcases hs with rfl | rfl <;> exact absurd htt (by decide)

end TypeDet

end CFSG.SeitzReduction.TwistedE6Pilot
