module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShearC
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthOddCore
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.SeitzReduction

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog (conj_inclusion_eq_of_commute
  semilinear_commute_of_conj_eq exists_unit_rep kappa_derived_eq_conj)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff)

namespace OrthogonalShearC

variable {K : Type} [Field K] {d : ℕ}

@[expose] def movedSpace (s : GL (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.range ((matrixLinearEquiv s).toLinearMap - LinearMap.id)

@[expose] def fixedSpace (s : GL (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.ker ((matrixLinearEquiv s).toLinearMap - LinearMap.id)

theorem mem_movedSpace (s : GL (Fin d) K) (v : Fin d → K) :
    v ∈ movedSpace s ↔ ∃ x, matrixLinearEquiv s x - x = v := by
  simp [movedSpace]

theorem mem_fixedSpace (s : GL (Fin d) K) (v : Fin d → K) :
    v ∈ fixedSpace s ↔ matrixLinearEquiv s v = v := by
  simp [fixedSpace, sub_eq_zero]

abbrev kappaIso (Q : QuadraticForm K (Fin d → K)) (s : matrixIsometries Q) :
    MulAut (matrixProjectiveDerived Q) :=
  matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)

variable {Q : QuadraticForm K (Fin d → K)}

theorem mem_matrixDerived_of_odd [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) (hodd : Odd (orderOf A)) :
    A ∈ matrixDerived Q := by
  obtain ⟨m, hm⟩ := hodd
  have h := CFSG.RankThree.PartOne.AUTSL.mul_self_mem_matrixDerived hQ hT
    (pow_mem hA (m + 1))
  have e : A ^ (m + 1) * A ^ (m + 1) = A := by
    rw [← pow_add, show m + 1 + (m + 1) = orderOf A + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rwa [e] at h

theorem kappaIso_apply_of_commute (s : matrixIsometries Q) {A : matrixDerived Q}
    (hA : (A : GL (Fin d) K) * s = s * A) :
    kappaIso Q s (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q A := by
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q A) = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val]
  change (s : GL (Fin d) K) *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K 1 A.val *
        (s : GL (Fin d) K)⁻¹ = A.val
  rw [map_one, MulAut.one_apply, ← hA, mul_inv_cancel_right]

theorem matrixLinearEquiv_mem_orthogonalGroup (s : matrixIsometries Q) :
    matrixLinearEquiv (s : GL (Fin d) K) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 ((mem_matrixIsometries_iff Q s.val).1 s.2)

theorem matrixLinearEquiv_involutive {s : GL (Fin d) K} (hs2 : s * s = 1) (v : Fin d → K) :
    matrixLinearEquiv s (matrixLinearEquiv s v) = v := by
  rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hs2]
  exact Matrix.one_mulVec v

theorem kappa_sq_eq_one_of_commute_odd [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (s : matrixIsometries Q) (hs2 : (s : GL (Fin d) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin d) K), Q h ≠ 0)
    (hW₀ : ∃ w ∈ movedSpace (s : GL (Fin d) K), w ≠ 0 ∧ Q w = 0)
    (hLW : ∃ x ∈ fixedSpace (s : GL (Fin d) K), ∃ u ∈ fixedSpace (s : GL (Fin d) K),
      polar Q x u = 1)
    (hroute : (∃ w₁ ∈ movedSpace (s : GL (Fin d) K), ∃ w₂ ∈ movedSpace (s : GL (Fin d) K),
        Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) ∨
      Module.finrank K (movedSpace (s : GL (Fin d) K)) + 3 ≤
        Module.finrank K (fixedSpace (s : GL (Fin d) K)))
    {β : MulAut (matrixProjectiveDerived Q)} (hβ : β ∈ matrixProjectiveImage Q)
    (hβx : β * kappaIso Q s = kappaIso Q s * β)
    (hβc : ∀ c, kappaIso Q s c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 := by
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · obtain ⟨h, -, hh⟩ := hb
      exact absurd (by rw [Subsingleton.elim h 0, QuadraticMap.map_zero]) hh
    · exact h
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep hβ
  set s' : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv (s : GL (Fin d) K) with hs'
  have hs'Q : s' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    matrixLinearEquiv_mem_orthogonalGroup s
  have hs'2 : ∀ v, s' (s' v) = v := matrixLinearEquiv_involutive hs2
  have hSs := conj_inclusion_eq_of_commute hQ hT hE hd hS (g := s) hβx
  have hTs : ∀ v, coordinateSemilinearMap S.val (s' v) = s' (coordinateSemilinearMap S.val v) :=
    semilinear_commute_of_conj_eq hSs
  have hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s' = s' * g →
      Odd (orderOf g) → ∀ v, coordinateSemilinearMap S.val (g v) =
        g (coordinateSemilinearMap S.val v) := by
    intro g hg hgs hgo v
    set A : GL (Fin d) K := matrixLinearIso.symm g with hA
    have hAg : matrixLinearIso A = g := matrixLinearIso.apply_symm_apply g
    have hAiso : A ∈ matrixIsometries Q := by
      change matrixLinearIso A ∈ TauCeti.QuadraticMap.orthogonalGroup Q
      rw [hAg]
      exact hg
    have hAo : orderOf A = orderOf g := by
      rw [← MulEquiv.orderOf_eq matrixLinearIso A, hAg]
    have hAD : A ∈ matrixDerived Q := mem_matrixDerived_of_odd hQ hT hAiso (hAo ▸ hgo)
    have hAs : A * s = s * A := matrixLinearIso.injective (by
      rw [map_mul, map_mul, hAg]
      exact hgs)
    set c := matrixProjectiveProjection Q ⟨A, hAD⟩
    have hxc : kappaIso Q s c = c := kappaIso_apply_of_commute s hAs
    have hco : Odd (orderOf c) := by
      refine (hAo ▸ hgo).of_dvd_nat ?_
      rw [← Subgroup.orderOf_mk A hAD]
      exact orderOf_map_dvd _ _
    have hβc' := hβc c hxc hco
    have hcomm : Commute (matrixProjectiveConjugationHom Q S)
        (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ⟨A, hAiso⟩)) := by
      have e1 : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ⟨A, hAiso⟩) =
          MulAut.conj c := kappa_derived_eq_conj ⟨A, hAD⟩
      rw [e1]
      have e2 := mul_conj_mul_inv_eq_conj (matrixProjectiveConjugationHom Q S) c
      rw [hβc', mul_inv_eq_iff_eq_mul] at e2
      exact e2
    have h := semilinear_commute_of_conj_eq
      (conj_inclusion_eq_of_commute hQ hT hE hd hS hcomm) v
    rw [← hAg]
    exact h
  have hW : ∀ v, v ∈ movedSpace (s : GL (Fin d) K) ↔ ∃ x, s' x - x = v :=
    mem_movedSpace (s : GL (Fin d) K)
  have hL : ∀ v, v ∈ fixedSpace (s : GL (Fin d) K) ↔ s' v = v :=
    mem_fixedSpace (s : GL (Fin d) K)
  obtain ⟨-, hT2⟩ := sq_eq_one_of_commute_odd hQ hs'Q hs'2 hW hL hb hW₀ hLW hroute
    (coordinateSemilinearMap S.val) (coordinateSemilinearMap_smul S.val)
    ((mem_unitMultiplierPairs_iff Q S).1 hS) hTs hodd
  have hS2 : S.val * S.val = 1 := by
    apply coordinateSemilinearHom_injective hd
    change Multiplicative.ofAdd (coordinateSemilinearMap (S.val * S.val)) =
      Multiplicative.ofAdd (coordinateSemilinearMap 1)
    congr 1
    exact AddEquiv.ext fun v => by rw [coordinateSemilinearMap_mul, hT2,
      coordinateSemilinearMap_one]
  rw [pow_two, ← map_mul, show S * S = 1 from Subtype.ext hS2, map_one]

theorem involutionCriterion_kappa_of_image_eq_top [Finite K] [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (htop : matrixProjectiveImage Q = ⊤)
    (s : matrixIsometries Q) (hs2 : (s : GL (Fin d) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin d) K), Q h ≠ 0)
    (hW₀ : ∃ w ∈ movedSpace (s : GL (Fin d) K), w ≠ 0 ∧ Q w = 0)
    (hLW : ∃ x ∈ fixedSpace (s : GL (Fin d) K), ∃ u ∈ fixedSpace (s : GL (Fin d) K),
      polar Q x u = 1)
    (hroute : (∃ w₁ ∈ movedSpace (s : GL (Fin d) K), ∃ w₂ ∈ movedSpace (s : GL (Fin d) K),
        Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) ∨
      Module.finrank K (movedSpace (s : GL (Fin d) K)) + 3 ≤
        Module.finrank K (fixedSpace (s : GL (Fin d) K))) :
    InvolutionCriterion (kappaIso Q s) := fun β hβx hβc =>
  kappa_sq_eq_one_of_commute_odd hQ hT hE s hs2 hb hW₀ hLW hroute (htop ▸ Subgroup.mem_top β) hβx
    hβc

theorem kappa_sq_eq_one_of_commute_odd_of_finrank [Finite K] [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hd : 7 ≤ d)
    (s : matrixIsometries Q) (hs2 : (s : GL (Fin d) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin d) K), Q h ≠ 0)
    (hW2 : 2 ≤ Module.finrank K (movedSpace (s : GL (Fin d) K)))
    (hWL : movedSpace (s : GL (Fin d) K) ≠ fixedSpace (s : GL (Fin d) K))
    {β : MulAut (matrixProjectiveDerived Q)} (hβ : β ∈ matrixProjectiveImage Q)
    (hβx : β * kappaIso Q s = kappaIso Q s * β)
    (hβc : ∀ c, kappaIso Q s c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 := by
  obtain ⟨hW₀, hLW, hroute⟩ := hyps_of_finrank hQ (matrixLinearEquiv_mem_orthogonalGroup s)
    (matrixLinearEquiv_involutive hs2) (mem_movedSpace (s : GL (Fin d) K))
    (mem_fixedSpace (s : GL (Fin d) K)) hb hW2 hWL (by rw [Module.finrank_fin_fun]; exact hd)
  exact kappa_sq_eq_one_of_commute_odd hQ hT hE s hs2 hb hW₀ hLW hroute hβ hβx hβc

theorem involutionCriterion_kappa_of_finrank [Finite K] [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤) (hd : 7 ≤ d)
    (s : matrixIsometries Q) (hs2 : (s : GL (Fin d) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin d) K), Q h ≠ 0)
    (hW2 : 2 ≤ Module.finrank K (movedSpace (s : GL (Fin d) K)))
    (hWL : movedSpace (s : GL (Fin d) K) ≠ fixedSpace (s : GL (Fin d) K)) :
    InvolutionCriterion (kappaIso Q s) := fun β hβx hβc =>
  kappa_sq_eq_one_of_commute_odd_of_finrank hQ hT hE hd s hs2 hb hW2 hWL
    (htop ▸ Subgroup.mem_top β) hβx hβc

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus regular_coordinateQuadPlus regular_coordinateQuadMinus
  commutator_coordinateQuadPlus commutator_coordinateQuadMinus)

theorem kappa_sq_eq_one_coordinatePlus [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hs2 : (s : GL (Fin (2 * n)) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin (2 * n)) K), coordinateQuadPlus n K h ≠ 0)
    (hW2 : 2 ≤ Module.finrank K (movedSpace (s : GL (Fin (2 * n)) K)))
    (hWL : movedSpace (s : GL (Fin (2 * n)) K) ≠ fixedSpace (s : GL (Fin (2 * n)) K))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hβ : β ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (hβx : β * kappaIso _ s = kappaIso _ s * β)
    (hβc : ∀ c, kappaIso _ s c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 :=
  kappa_sq_eq_one_of_commute_odd_of_finrank (regular_coordinateQuadPlus n K (by omega)).1
    (regular_coordinateQuadPlus n K (by omega)).2 (commutator_coordinateQuadPlus n K (by omega))
    (by omega) s hs2 hb hW2 hWL hβ hβx hβc

theorem kappa_sq_eq_one_coordinateMinus [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    (hn1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (s : matrixIsometries (coordinateQuadMinus n K hn1 b c))
    (hs2 : (s : GL (Fin (2 * n)) K) * s = 1)
    (hb : ∃ h ∈ movedSpace (s : GL (Fin (2 * n)) K), coordinateQuadMinus n K hn1 b c h ≠ 0)
    (hW2 : 2 ≤ Module.finrank K (movedSpace (s : GL (Fin (2 * n)) K)))
    (hWL : movedSpace (s : GL (Fin (2 * n)) K) ≠ fixedSpace (s : GL (Fin (2 * n)) K))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))}
    (hβ : β ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c))
    (hβx : β * kappaIso _ s = kappaIso _ s * β)
    (hβc : ∀ c, kappaIso _ s c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 :=
  kappa_sq_eq_one_of_commute_odd_of_finrank (regular_coordinateQuadMinus n K b c hn hirr).1
    (regular_coordinateQuadMinus n K b c hn hirr).2 (commutator_coordinateQuadMinus n K b c hn hirr)
    (by omega) s hs2 hb hW2 hWL hβ hβx hβc

end OrthogonalShearC

end CFSG.SeitzReduction
