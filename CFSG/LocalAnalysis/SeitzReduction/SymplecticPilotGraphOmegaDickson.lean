module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaRows
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module QuadraticMap
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace)

section MatrixDickson

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def matrixDickson [CharP K 2] (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) : matrixIsometries Q →* Multiplicative (ZMod 2) :=
  (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).comp
    ((matrixLinearIso.toMonoidHom).subgroupComap (TauCeti.QuadraticMap.orthogonalGroup Q))

theorem matrixDickson_apply [CharP K 2] (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (A : matrixIsometries Q) :
    matrixDickson Q hQ A =
      Multiplicative.ofAdd (finrank K (commSpace (matrixLinearIso (A : GL (Fin d) K))) : ZMod 2) :=
  rfl

theorem coordinateFieldMap_mem_commSpace (σ : K ≃+* K) (B : GL (Fin d) K) {w : Fin d → K}
    (hw : w ∈ commSpace (matrixLinearIso B)) :
    coordinateFieldMap d σ w ∈ commSpace (matrixLinearIso (glFieldAut (Fin d) K σ B)) := by
  obtain ⟨y, rfl⟩ := mem_commSpace.1 hw
  refine mem_commSpace.2 ⟨coordinateFieldMap d σ y, ?_⟩
  rw [map_sub]
  congr 1
  exact (coordinateFieldMap_matrix σ B y).symm

theorem finrank_commSpace_glFieldAut (σ : K ≃+* K) (B : GL (Fin d) K) :
    finrank K (commSpace (matrixLinearIso (glFieldAut (Fin d) K σ B))) =
      finrank K (commSpace (matrixLinearIso B)) := by
  have hback : ∀ w ∈ commSpace (matrixLinearIso (glFieldAut (Fin d) K σ B)),
      (coordinateFieldMap d σ).symm w ∈ commSpace (matrixLinearIso B) := by
    intro w hw
    have h1 := coordinateFieldMap_mem_commSpace σ⁻¹ (glFieldAut (Fin d) K σ B) hw
    have h2 : glFieldAut (Fin d) K σ⁻¹ (glFieldAut (Fin d) K σ B) = B := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [h2] at h1
    exact h1
  let j : commSpace (matrixLinearIso B) ≃+
      commSpace (matrixLinearIso (glFieldAut (Fin d) K σ B)) :=
    { toFun := fun w => ⟨coordinateFieldMap d σ w, coordinateFieldMap_mem_commSpace σ B w.2⟩
      invFun := fun w => ⟨(coordinateFieldMap d σ).symm w, hback w w.2⟩
      left_inv := fun w => Subtype.ext ((coordinateFieldMap d σ).symm_apply_apply w)
      right_inv := fun w => Subtype.ext ((coordinateFieldMap d σ).apply_symm_apply w)
      map_add' := fun a b => Subtype.ext ((coordinateFieldMap d σ).map_add a b) }
  have hrank := rank_eq_of_equiv_equiv (R := K) (R' := K) σ j σ.bijective fun r w =>
    Subtype.ext (show coordinateFieldMap d σ (r • (w : Fin d → K)) =
      σ r • coordinateFieldMap d σ (w : Fin d → K) from coordinateFieldMap_smul σ r _)
  unfold finrank
  rw [hrank]

end MatrixDickson

section UnitPairs

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem left_mem_matrixIsometries_of_unit
    (hσQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v))
    (g : unitMultiplierPairs Q) : (g : similarityPairs Q).val.left ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff]
  intro w
  have hg := g.2 ((coordinateFieldMap d (g : similarityPairs Q).val.right).symm w)
  change Q (matrixLinearEquiv (g : similarityPairs Q).val.left
    (coordinateFieldMap d (g : similarityPairs Q).val.right
      ((coordinateFieldMap d (g : similarityPairs Q).val.right).symm w))) = _ at hg
  rw [AddEquiv.apply_symm_apply] at hg
  rw [hg, ← hσQ, AddEquiv.apply_symm_apply]

theorem glFieldAut_mem_matrixIsometries
    (hσQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v))
    (σ : K ≃+* K) {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) :
    glFieldAut (Fin d) K σ B ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff] at hB ⊢
  intro w
  have h1 : matrixLinearEquiv (glFieldAut (Fin d) K σ B) w =
      coordinateFieldMap d σ (matrixLinearEquiv B ((coordinateFieldMap d σ).symm w)) := by
    rw [coordinateFieldMap_matrix, AddEquiv.apply_symm_apply]
  rw [h1, hσQ, hB, ← hσQ, AddEquiv.apply_symm_apply]

@[expose] noncomputable def unitPairDickson [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hσQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v)) :
    unitMultiplierPairs Q →* Multiplicative (ZMod 2) where
  toFun g := matrixDickson Q hQ ⟨_, left_mem_matrixIsometries_of_unit hσQ g⟩
  map_one' := by
    change matrixDickson Q hQ 1 = 1
    exact map_one _
  map_mul' g h := by
    have hm := map_mul (matrixDickson Q hQ)
      ⟨(g : similarityPairs Q).val.left, left_mem_matrixIsometries_of_unit hσQ g⟩
      ⟨glFieldAut (Fin d) K (g : similarityPairs Q).val.right (h : similarityPairs Q).val.left,
        glFieldAut_mem_matrixIsometries hσQ _ (left_mem_matrixIsometries_of_unit hσQ h)⟩
    refine hm.trans ?_
    congr 1
    rw [matrixDickson_apply, matrixDickson_apply]
    congr 2
    exact finrank_commSpace_glFieldAut _ _

theorem unitPairDickson_apply [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hσQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v))
    (g : unitMultiplierPairs Q) :
    unitPairDickson hQ hσQ g =
      matrixDickson Q hQ ⟨_, left_mem_matrixIsometries_of_unit hσQ g⟩ :=
  rfl

theorem matrixIsometryInclusion_mem_unitMultiplierPairs (A : matrixIsometries Q) :
    matrixIsometryInclusion Q A ∈ unitMultiplierPairs Q := fun v => by
  change Q (matrixLinearEquiv (A : GL (Fin d) K) v) = Q v
  exact (mem_matrixIsometries_iff Q _).1 A.2 v

theorem unitPairDickson_inclusion [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hσQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v))
    (A : matrixIsometries Q) :
    unitPairDickson hQ hσQ
        ⟨matrixIsometryInclusion Q A, matrixIsometryInclusion_mem_unitMultiplierPairs A⟩ =
      matrixDickson Q hQ A :=
  rfl

end UnitPairs

section Plus

theorem omegaPlusDicksonInput_holds : OmegaPlusDicksonInput := by
  intro K _ _ _ N hN
  have hhyp := OmegaPilot.isHypCoord_coordinateQuadPlus (K := K) (n := N) ⟨0, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * N) → K, coordinateQuadPlus N K v = 1 :=
    ⟨(1 : K) • Pi.single (plusIndexEquiv N (.inl ⟨0, by omega⟩)) 1 +
        (1 : K) • Pi.single (plusIndexEquiv N (.inr ⟨0, by omega⟩)) 1 + 0,
      by rw [hhyp.map_add_smul 1 1 rfl rfl, QuadraticMap.map_zero, mul_one, add_zero]⟩
  refine ⟨v, hv, ?_⟩
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hreg := regular_coordinateQuadPlus (K := K) (n := N) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K) (n := N) (by omega)
  obtain ⟨-, -, ⟨Φ, hΦ⟩, -, -⟩ :=
    evenOrthogonalRealization_of_regular hf1 hK (by omega) (coordinateQuadPlus N K) hreg.1 hreg.2 hE
  have hC : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadPlus N K))) .POmegaPlus N 2 f :=
    ⟨⟨Nat.prime_two, hf1, by omega⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have htop : matrixProjectiveImage (coordinateQuadPlus N K) = ⊤ :=
    semilinearImageEqTop _ .POmegaPlus (Or.inl rfl) hC hN K hK (MulEquiv.refl _)
  have hσQ : ∀ (σ : K ≃+* K) (w : Fin (2 * N) → K),
      coordinateQuadPlus N K (coordinateFieldMap (2 * N) σ w) = σ (coordinateQuadPlus N K w) := by
    intro σ w
    rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply, map_sum]
    simp only [coordinateFieldMap_apply, map_mul]
  let ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus N K)) →*
      unitMultiplierPairs (coordinateQuadPlus N K) :=
    Φ.symm.toMonoidHom.comp
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.toMonoidHom
  have hψ : ∀ (g : similarityPairs (coordinateQuadPlus N K))
      (hg : g ∈ unitMultiplierPairs (coordinateQuadPlus N K)),
      ψ (matrixProjectiveConjugationHom (coordinateQuadPlus N K) g) = ⟨g, hg⟩ := by
    intro g hg
    apply Φ.injective
    change Φ (Φ.symm _) = _
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hΦ]
    rfl
  refine ⟨(unitPairDickson hreg.1 hσQ).comp ψ, fun x => ?_, ?_⟩
  ·
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective (coordinateQuadPlus N K) x
    rw [← kappa_derived_eq_conj, MonoidHom.comp_apply,
      hψ (matrixDerivedInclusion _ g) (matrixIsometryInclusion_mem_unitMultiplierPairs
        (Subgroup.inclusion (matrixDerived_le_isometries _) g))]
    refine (unitPairDickson_inclusion hreg.1 hσQ
      (Subgroup.inclusion (matrixDerived_le_isometries _) g)).trans ?_
    have hmem : Subgroup.inclusion (matrixDerived_le_isometries _) g ∈
        commutator (matrixIsometries (coordinateQuadPlus N K)) := by
      have h1 : (g : GL (Fin (2 * N)) K) ∈
          (commutator (matrixIsometries (coordinateQuadPlus N K))).map
            (matrixIsometries (coordinateQuadPlus N K)).subtype := by
        rw [← matrixDerived_eq_map_commutator]
        exact g.2
      obtain ⟨y, hy, hyg⟩ := h1
      have hy' : y = Subgroup.inclusion (matrixDerived_le_isometries _) g := Subtype.ext hyg
      rw [← hy']
      exact hy
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker _ hmem)
  ·
    rw [MonoidHom.comp_apply, hψ _ (matrixIsometryInclusion_mem_unitMultiplierPairs _),
      unitPairDickson_inclusion, matrixDickson_apply]
    have : Invertible (coordinateQuadPlus N K v) := by
      rw [hv]
      exact invertibleOne
    change Multiplicative.ofAdd
      (finrank K (commSpace (matrixLinearIso (symmetryGL (coordinateQuadPlus N K) v))) : ZMod 2)
        ≠ 1
    rw [matrixLinearIso_symmetryGL, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hreg.1, Nat.cast_one, Ne,
      ofAdd_eq_one]
    decide

end Plus

section Rows


theorem false_of_spOmegaPlusRow_of_recognition (hrec : SpOmegaRecognitionInput .omegaPlus)
    (huniq : SpOmegaRowUniqueInput .omegaPlus) : SpOmegaPlusRowInput :=
  false_of_spOmegaPlusRow hrec huniq omegaPlusDicksonInput_holds

theorem spGraphRowsInput_of_omegaInputs' (hLE : SpLinearEvenRowInput)
    (hUE : SpUnitaryEvenRowInput) (hLO : SpLinearOddRowInput) (hUO : SpUnitaryOddRowInput)
    (hrecP : SpOmegaRecognitionInput .omegaPlus) (huniqP : SpOmegaRowUniqueInput .omegaPlus)
    (hrecM : SpOmegaRecognitionInput .omegaMinus) (huniqM : SpOmegaRowUniqueInput .omegaMinus)
    (hO : OmegaMinusOutInput) : SpGraphRowsInput :=
  spGraphRowsInput_of_omegaInputs hLE hUE hLO hUO hrecP huniqP omegaPlusDicksonInput_holds hrecM
    huniqM hO

end Rows

end CFSG.SeitzReduction.SymplecticPilot
