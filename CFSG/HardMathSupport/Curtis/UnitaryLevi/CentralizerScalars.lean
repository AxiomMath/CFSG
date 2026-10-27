module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreConj
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction.UnitaryPilot
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis CFSG.Open

variable {K : Type} [Field K]

theorem stdHermForm_single_add_single_smul (h : UnitaryFieldData 2 1 K) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (c : K) :
    stdHermForm h n (Pi.single i 1 + Pi.single j c) (Pi.single i 1 + Pi.single j c) =
      1 + h.bar c * c := by
  rw [stdHermForm_apply, Finset.sum_eq_add i j hij]
  · simp [hij, hij.symm]
  · intro k _ hk
    simp [hk.1, hk.2]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem eq_scalar_of_commute_unitarySU (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ g : unitarySU 2 1 K n, M * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M) :
    ∃ κ : K, M = Matrix.scalar (Fin n) κ := by
  classical
  have := h.charP
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun hh => by simpa [i, j] using congrArg Fin.val hh
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ c : K, c ≠ 0 → c = 1 := fun c hc0 => by
      by_contra hc1
      exact hcon ⟨c, hc0, hc1⟩
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon' x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
    omega
  have hnorm : h.bar c * c = 1 := by
    rw [UnitaryFieldData.bar_apply, pow_one, ← pow_succ]
    simpa [hcard] using FiniteField.pow_card_sub_one_eq_one c hc0
  have hv_iso : stdHermForm h n (Pi.single i 1 + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) =
      0 := by
    have := stdHermForm_single_add_single_smul h hij (1 : K)
    rw [this, map_one, mul_one, CharTwo.add_self_eq_zero]
  have hc_iso : stdHermForm h n (Pi.single i 1 + Pi.single j c) (Pi.single i 1 + Pi.single j c) =
      0 := by
    rw [stdHermForm_single_add_single_smul h hij c, hnorm, CharTwo.add_self_eq_zero]
  have hv0 : (Pi.single i 1 + Pi.single j 1 : Fin n → K) ≠ 0 := fun hh => by
    have := congrFun hh i
    simp [hij] at this
  have hc0' : (Pi.single i 1 + Pi.single j c : Fin n → K) ≠ 0 := fun hh => by
    have := congrFun hh i
    simp [hij] at this
  obtain ⟨κ, hκ⟩ : ∃ κ : K, M *ᵥ (Pi.single i 1 + Pi.single j 1) =
      κ • (Pi.single i 1 + Pi.single j 1) := by
    have hcomm := hM (tvTransSU h hij)
    rw [coe_tvTransSU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      add_right_inj] at hcomm
    have h1 := congrArg (fun N : Matrix (Fin n) (Fin n) K => N *ᵥ (Pi.single i 1 : Fin n → K))
      hcomm
    simp only [tvNil, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul] at h1
    refine ⟨tvVec i j ⬝ᵥ (M *ᵥ Pi.single i 1), ?_⟩
    have hd : tvVec i j ⬝ᵥ (Pi.single i 1 : Fin n → K) = 1 := by
      rw [tvVec_dotProduct]
      simp [hij.symm]
    rw [hd, one_smul] at h1
    exact h1
  have hall : ∀ a : Fin n → K, a ≠ 0 → stdHermForm h n a a = 0 → M *ᵥ a = κ • a := by
    intro a ha0 ha
    obtain ⟨g, hg⟩ := exists_unitarySU_mulVec_eq h hn hv0 hv_iso ha0 ha
    calc M *ᵥ a = M *ᵥ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (Pi.single i 1 + Pi.single j 1)) := by rw [hg]
      _ = (M * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
          (Pi.single i 1 + Pi.single j 1) := Matrix.mulVec_mulVec _ _ _
      _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M) *ᵥ
          (Pi.single i 1 + Pi.single j 1) := by rw [hM g]
      _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (M *ᵥ (Pi.single i 1 + Pi.single j 1)) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = κ • a := by rw [hκ, mulVec_smul, hg]
  have hcol : ∀ l : Fin n, M *ᵥ Pi.single l 1 = κ • (Pi.single l 1 : Fin n → K) := by
    intro l
    obtain ⟨m, hml⟩ : ∃ m : Fin n, m ≠ l := ⟨if l = i then j else i, by
      by_cases hl : l = i
      · simp only [hl, ite_true]; exact hij.symm
      · simp only [hl, ite_false]; exact fun hh => hl hh.symm⟩
    have hiso1 := stdHermForm_single_add_single_smul h hml (1 : K)
    have hiso2 := stdHermForm_single_add_single_smul h hml c
    rw [map_one, mul_one, CharTwo.add_self_eq_zero] at hiso1
    rw [hnorm, CharTwo.add_self_eq_zero] at hiso2
    have ha1 : (Pi.single m 1 + Pi.single l 1 : Fin n → K) ≠ 0 := fun hh => by
      have := congrFun hh m
      simp [hml] at this
    have ha2 : (Pi.single m 1 + Pi.single l c : Fin n → K) ≠ 0 := fun hh => by
      have := congrFun hh m
      simp [hml] at this
    have e1 := hall _ ha1 hiso1
    have e2 := hall _ ha2 hiso2
    have hsum : (Pi.single m 1 + Pi.single l 1 : Fin n → K) +
        (Pi.single m 1 + Pi.single l c) = (1 + c) • (Pi.single l 1 : Fin n → K) := by
      funext k
      by_cases hkm : k = m
      · subst hkm
        simp [hml, CharTwo.add_self_eq_zero]
      · by_cases hkl : k = l
        · subst hkl
          simp [hml.symm]
        · simp [hkm, hkl]
    have h3 : (1 + c) • (M *ᵥ Pi.single l 1) = (1 + c) • (κ • (Pi.single l 1 : Fin n → K)) := by
      calc (1 + c) • (M *ᵥ Pi.single l 1) = M *ᵥ ((1 + c) • (Pi.single l 1 : Fin n → K)) :=
            (mulVec_smul _ _ _).symm
        _ = M *ᵥ ((Pi.single m 1 + Pi.single l 1 : Fin n → K) +
            (Pi.single m 1 + Pi.single l c)) := by rw [hsum]
        _ = κ • (Pi.single m 1 + Pi.single l 1 : Fin n → K) +
            κ • (Pi.single m 1 + Pi.single l c) := by rw [mulVec_add, e1, e2]
        _ = κ • ((Pi.single m 1 + Pi.single l 1 : Fin n → K) +
            (Pi.single m 1 + Pi.single l c)) := (smul_add _ _ _).symm
        _ = (1 + c) • (κ • (Pi.single l 1 : Fin n → K)) := by rw [hsum, smul_comm]
    have h1c : (1 + c) ≠ 0 := fun hh => hc1 (CharTwo.add_eq_zero.mp hh).symm
    exact smul_right_injective _ h1c h3
  refine ⟨κ, ?_⟩
  ext a b
  have := congrFun (hcol b) a
  rw [mulVec_single_one, col_apply] at this
  rw [this, scalar_apply, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab]

theorem scalar_of_conj_eq [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (A A' : GL (Fin n) K)
    (hAA' : ∀ g : StatedSU n 2 K, A * (g : GL (Fin n) K) * A⁻¹ = A' * (g : GL (Fin n) K) * A'⁻¹) :
    A⁻¹ * A' ∈ StatedScalars (Fin n) K := by
  classical
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hcomm : ∀ g : unitarySU 2 1 K n, (A⁻¹ * A') * (g : GL (Fin n) K) =
      (g : GL (Fin n) K) * (A⁻¹ * A') := fun g => by
    calc (A⁻¹ * A') * (g : GL (Fin n) K) = A⁻¹ * (A' * (g : GL (Fin n) K) * A'⁻¹) * A' := by
          group
      _ = A⁻¹ * (A * (g : GL (Fin n) K) * A⁻¹) * A' := by rw [hAA' g]
      _ = (g : GL (Fin n) K) * (A⁻¹ * A') := by group
  obtain ⟨κ, hκ⟩ := eq_scalar_of_commute_unitarySU h hK4 hn (M := ((A⁻¹ * A' : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) fun g => by
      rw [← Units.val_mul, ← Units.val_mul, hcomm g]
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have h1 := congrArg (fun N : Matrix (Fin n) (Fin n) K => N *
      (((A⁻¹ * A')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hκ
    simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, map_zero, Matrix.zero_mul] at h1
    have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  refine ⟨Units.mk0 κ hκ0, ?_⟩
  exact (Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hκ.symm))

end CFSG.HardMathSupport.Curtis.UnitaryLevi
