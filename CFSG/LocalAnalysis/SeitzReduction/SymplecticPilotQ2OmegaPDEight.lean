module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndSign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDAlignMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  projectivePointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_val)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar
  coordinate_plus_pointFamily_orbit_subset)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL matrixLinearIso_symmetryGL
  symmetryGL_mul_self symmetryAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.RankThree.PartOne.AUTSL (conjAct derivedProjEquiv)
open scoped Pointwise

section Matrix

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem pd_exists_pair_of_mem_image [Finite K] (hQ : ∃ v, Q v ≠ 0) (α : MulAut (matrixDerived Q))
    (hmem : MulAut.congr (derivedProjEquiv Q hQ) α ∈ matrixProjectiveImage Q) :
    ∃ g : similarityPairs Q, conjAct Q g = α := by
  set Φ := derivedProjEquiv Q hQ
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).1 hmem
  refine ⟨g, MulEquiv.ext fun A => ?_⟩
  have h1 : Φ (α A) = Φ (matrixDerivedConjugation Q g A) := by
    have h2 : MulAut.congr Φ α (Φ A) = Φ (α A) :=
      CFSG.RankThree.PartOne.AUTSL.congr_apply_apply' Φ α A
    rw [← h2, ← hg]
    show matrixProjectiveConjugation _ g (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ _
    exact matrixProjectiveConjugation_mk _ g A
  exact (Φ.injective h1).symm

theorem pd_eq_one_or_eq_symmetry_of_fix_mem_image [Finite K] (hK : Nat.card K = 2)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 6 ≤ d) {v : Fin d → K} (hv : Q v = 1)
    (α : MulAut (matrixDerived Q))
    (hmem : MulAut.congr (derivedProjEquiv Q ⟨v, by rw [hv]; exact one_ne_zero⟩) α ∈
      matrixProjectiveImage Q)
    (hfix : ∀ X : matrixDerived Q, (X.val : Matrix (Fin d) (Fin d) K) *ᵥ v = v → α X = X) :
    α = 1 ∨ ∀ X : matrixDerived Q, (α X).val = symmetryGL Q v * X.val * symmetryGL Q v := by
  obtain ⟨g, hg⟩ := pd_exists_pair_of_mem_image ⟨v, by rw [hv]; exact one_ne_zero⟩ α hmem
  obtain ⟨hiso, hconj⟩ := isometry_of_similarityPairs_two hK g
  set B := g.val.left with hBdef
  have hαB : ∀ X : matrixDerived Q, (α X).val = B * X.val * B⁻¹ := fun X => by
    rw [← hg, CFSG.RankThree.PartOne.AUTSL.conjAct_apply, hconj]
  have hBO : matrixLinearIso B ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hiso
  have hcomm : ∀ h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, h v = v →
        matrixLinearIso B * h = h * matrixLinearIso B := by
    intro h hh hhv
    set X : GL (Fin d) K := matrixLinearIso.symm h with hXdef
    have hXh : matrixLinearIso X = h := MulEquiv.apply_symm_apply _ _
    have hX : X ∈ matrixDerived Q := (mem_matrixDerived_iff Q X).2 (by rw [hXh]; exact hh)
    have hXv : (X : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
      change matrixLinearIso X v = v
      rw [hXh]
      exact hhv
    have h1 := congrArg Subtype.val (hfix ⟨X, hX⟩ hXv)
    rw [hαB] at h1
    have h2 : B * X = X * B := by
      calc B * X = B * X * B⁻¹ * B := by group
        _ = X * B := by rw [h1]
    have h3 := congrArg matrixLinearIso h2
    rwa [map_mul, map_mul, hXh] at h3
  have hdim : 6 ≤ Module.finrank K (Fin d → K) := by
    rw [Module.finrank_fin_fun]
    exact hd
  rcases eq_one_or_eq_reflect_of_commute hK hQ hdim hv hBO hcomm with h | h
  · left
    have hB1 : B = 1 := matrixLinearIso.injective (by rw [h, map_one])
    refine MulEquiv.ext fun X => Subtype.ext ?_
    rw [hαB, hB1, one_mul, inv_one, mul_one]
    rfl
  · right
    have hBs : B = symmetryGL Q v := matrixLinearIso.injective (by
      rw [h, matrixLinearIso_symmetryGL])
    have hsinv : (symmetryGL Q v)⁻¹ = symmetryGL Q v :=
      inv_eq_of_mul_eq_one_right (symmetryGL_mul_self Q v)
    intro X
    rw [hαB, hBs, hsinv]

end Matrix

section Eight

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem pd_reindex_kOmegaVec_three :
    reindexVectorEquiv (plusIndexEquiv (3 + 1)) (kOmegaVec K 3) = OmegaPilot.lastPlaneVec 3 := by
  funext i
  rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexVectorEquiv_apply]
  simp [kOmegaVec, OmegaPilot.lastPlaneVec, Pi.single_apply, Equiv.symm_apply_eq]

theorem pd_eq_one_or_eq_kOmegaBetaC_three (hK : Nat.card K = 2)
    (α : MulAut (StatedOmega (StatedQuadPlus (3 + 1) K)))
    (hmem : MulAut.congr (F4Pilot.omegaProjEquiv (plusIndexEquiv (3 + 1)) (quadPlus (3 + 1) K)
      (coe_quadPlus (3 + 1) K) (kOmega_matrixDerivedScalars_eq_bot K 3)) α ∈
        matrixProjectiveImage (reindexQuadraticForm (plusIndexEquiv (3 + 1)) (quadPlus (3 + 1) K)))
    (hfix : ∀ g ∈ fixedSubgroup (kOmegaBetaC K 3), α g = g) : α = 1 ∨ α = kOmegaBetaC K 3 := by
  set eI := plusIndexEquiv (3 + 1) with heI
  set Q := quadPlus (3 + 1) K with hQdef
  set Q' := reindexQuadraticForm eI Q with hQ'
  set θ := statedDerivedReindexEquiv eI Q (coe_quadPlus (3 + 1) K) with hθ
  set ω := F4Pilot.omegaProjEquiv eI Q (coe_quadPlus (3 + 1) K)
    (kOmega_matrixDerivedScalars_eq_bot K 3) with hω
  set v' := reindexVectorEquiv eI (kOmegaVec K 3) with hv'def
  have hv : Q (kOmegaVec K 3) = 1 := kOmega_quadPlus_vec K 3
  have hv' : Q' v' = 1 := by rw [F4Pilot.reindexQuadraticForm_reindexVectorEquiv, hv]
  have hnd : Q'.polarBilin.Nondegenerate := (regular_coordinateQuadPlus (3 + 1) K (by omega)).1
  set α' : MulAut (matrixDerived Q') := (θ.symm.trans α).trans θ with hα'
  have hα'app : ∀ A, α' (θ A) = θ (α A) := fun A => by
    rw [hα', MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hfix' : ∀ X : matrixDerived Q', (X.val : Matrix (Fin (2 * (3 + 1))) (Fin (2 * (3 + 1))) K)
      *ᵥ v' = v' → α' X = X := by
    intro X hX
    obtain ⟨A, rfl⟩ := θ.surjective X
    have hA : ((A : GL (Fin (3 + 1) ⊕ Fin (3 + 1)) K) : Matrix (Fin (3 + 1) ⊕ Fin (3 + 1))
        (Fin (3 + 1) ⊕ Fin (3 + 1)) K) *ᵥ kOmegaVec K 3 = kOmegaVec K 3 := by
      apply (reindexVectorEquiv (K := K) eI).injective
      rw [← F4Pilot.statedDerivedReindexEquiv_mulVec eI Q (coe_quadPlus (3 + 1) K)]
      exact hX
    rw [hα'app, hfix A ((mem_fixedSubgroup_kOmegaBetaC_iff K (by omega) A).2 hA)]
  have hΦω : ∀ A, ω A = derivedProjEquiv Q' ⟨v', by rw [hv']; exact one_ne_zero⟩ (θ A) :=
    fun A => rfl
  have hmem' : MulAut.congr (derivedProjEquiv Q' ⟨v', by rw [hv']; exact one_ne_zero⟩) α' ∈
      matrixProjectiveImage Q' := by
    convert hmem using 1
    refine MulEquiv.ext fun x => ?_
    obtain ⟨A, rfl⟩ := ω.surjective x
    rw [CFSG.RankThree.PartOne.AUTSL.congr_apply_apply' ω α A, hΦω,
      CFSG.RankThree.PartOne.AUTSL.congr_apply_apply', hα'app, ← hΦω]
  rcases pd_eq_one_or_eq_symmetry_of_fix_mem_image hK hnd (by norm_num) hv' α' hmem' hfix' with
    h1 | h1
  · left
    refine MulEquiv.ext fun A => θ.injective ?_
    rw [← hα'app, h1]
    rfl
  · right
    refine MulEquiv.ext fun A => ω.injective ?_
    rw [show kOmegaBetaC K 3 = F4Pilot.omegaSymmetryAut eI Q (coe_quadPlus (3 + 1) K)
      (kOmega_matrixDerivedScalars_eq_bot K 3) (kOmegaVec K 3) from rfl,
      F4Pilot.omegaProjEquiv_omegaSymmetryAut, F4Pilot.omegaProjEquiv_apply,
      F4Pilot.omegaProjEquiv_apply]
    change _ = matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' (θ A))
    rw [matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    rw [← CFSG.RankThree.PartOne.AUTSL.conjAct_apply,
      CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_val, ← hα'app, h1,
      inv_eq_of_mul_eq_one_right (symmetryGL_mul_self Q' v')]

end Eight

theorem omegaPlusOverlapTwist_three : OmegaPlusOverlapTwist 3 := by
  intro K _ _ _ hK α hfix hcomm
  set Q' := coordinateQuadPlus (3 + 1) K with hQ'
  set ω := F4Pilot.omegaProjEquiv (plusIndexEquiv (3 + 1)) (quadPlus (3 + 1) K)
    (coe_quadPlus (3 + 1) K) (kOmega_matrixDerivedScalars_eq_bot K 3) with hω
  set δ : MulAut (matrixProjectiveDerived Q') := MulAut.congr ω α with hδ
  set κ' : MulAut (matrixProjectiveDerived Q') := symmetryAut Q' (OmegaPilot.lastPlaneVec 3)
    with hκ'
  have hκ : (MulAut.congr ω (kOmegaBetaC K 3) : MulAut (matrixProjectiveDerived Q')) = κ' := by
    have h := F4Pilot.congr_omegaSymmetryAut (plusIndexEquiv (3 + 1)) (quadPlus (3 + 1) K)
      (coe_quadPlus (3 + 1) K) (kOmega_matrixDerivedScalars_eq_bot K 3) (kOmegaVec K 3)
    rw [pd_reindex_kOmegaVec_three] at h
    exact h
  have hδκ : δ * κ' = κ' * δ := by
    have h1 : α * kOmegaBetaC K 3 = kOmegaBetaC K 3 * α := MulEquiv.ext fun g => hcomm g
    have h2 := congrArg (MulAut.congr ω) h1
    rw [map_mul, map_mul] at h2
    rw [← hκ]
    exact h2
  have hκF : κ' • projectivePointFamily Q' = projectivePointFamily Q' :=
    (OmegaPilot.mem_image_iff_smul_pointFamily (n := 3 + 1) (by norm_num) κ').1 ⟨_, rfl⟩
  have hκX : κ' • plusCX (3 + 1) K = plusCXstar (3 + 1) K (by norm_num) ∧
      κ' • plusCXstar (3 + 1) K (by norm_num) = plusCX (3 + 1) K :=
    OmegaPilot.symmetryAut_lastPlaneVec_smul_plusCX (F := K)
  have hXX : plusCX (3 + 1) K ≠ plusCXstar (3 + 1) K (by norm_num) :=
    OmegaPilot.plusCX_ne_plusCXstar (3 + 1) K (by norm_num)
  have hO := coordinate_plus_pointFamily_orbit_subset (n := 3 + 1) (K := K) rfl
    (MulAction.mem_orbit (projectivePointFamily Q') δ)
  have hF : δ • projectivePointFamily Q' = projectivePointFamily Q' := by
    have hc : (δ * κ') • projectivePointFamily Q' = (κ' * δ) • projectivePointFamily Q' := by
      rw [hδκ]
    rw [mul_smul, mul_smul, hκF] at hc
    rcases hO with h | h | h
    · exact h
    · rw [h, hκX.1] at hc
      exact absurd hc hXX
    · rw [h, hκX.2] at hc
      exact absurd hc.symm hXX
  have hmem := (OmegaPilot.mem_image_iff_smul_pointFamily (n := 3 + 1) (by norm_num) δ).2 hF
  exact pd_eq_one_or_eq_kOmegaBetaC_three hK α hmem hfix

theorem spTwoOmegaMinusAlignInput_holds : SpTwoOmegaMinusAlignInput :=
  spTwoOmegaMinusAlignInput_of_twist omegaPlusOverlapTwist_three

end CFSG.SeitzReduction.SymplecticPilot
