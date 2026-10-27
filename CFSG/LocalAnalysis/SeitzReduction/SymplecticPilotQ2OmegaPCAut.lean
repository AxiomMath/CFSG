module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus
  regular_coordinateQuadPlus regular_coordinateQuadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL matrixLinearIso_symmetryGL
  symmetryGL_mem symmetryGL_mul_self)
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Pairs

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem isometry_of_similarityPairs_two (hK : Nat.card K = 2) (g : similarityPairs Q) :
    g.val.left ∈ matrixIsometries Q ∧ ∀ X : matrixDerived Q,
      (matrixDerivedConjugation Q g X).val = g.val.left * X.val * g.val.left⁻¹ := by
  have hr : g.val.right = 1 := q2RingEquiv_eq_one hK _
  have hm : (multiplier Q g : K) = 1 :=
    (eq_zero_or_eq_one_of_natCard_two hK _).resolve_left (Units.ne_zero _)
  refine ⟨(mem_matrixIsometries_iff Q _).2 fun v => ?_, fun X => ?_⟩
  · have h := multiplier_spec Q g v
    rw [coordinateSemilinearMap_apply, hr, hm, one_mul] at h
    exact h
  · rw [matrixDerivedConjugation_val, hr, map_one, MulAut.one_apply]

end Pairs

section Matrix

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem eq_one_or_eq_symmetry_of_fix_two (hK : Nat.card K = 2) (hQ : Q.polarBilin.Nondegenerate)
    (hd : 6 ≤ d) (htop : matrixProjectiveImage Q = ⊤) {v : Fin d → K} (hv : Q v = 1)
    (α : MulAut (matrixDerived Q))
    (hfix : ∀ X : matrixDerived Q, (X.val : Matrix (Fin d) (Fin d) K) *ᵥ v = v → α X = X) :
    α = 1 ∨ ∀ X : matrixDerived Q, (α X).val = symmetryGL Q v * X.val * symmetryGL Q v := by
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.AUTSL.exists_pair_of_aut
    ⟨v, by rw [hv]; exact one_ne_zero⟩ htop α
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

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2] {d : ℕ}

theorem eq_one_or_eq_omegaSymmetryAut_of_fix_two (hK : Nat.card K = 2) (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥)
    (hnd : (reindexQuadraticForm eI Q).polarBilin.Nondegenerate) (hd : 6 ≤ d)
    (htop : matrixProjectiveImage (reindexQuadraticForm eI Q) = ⊤) {v : ι → K} (hv : Q v = 1)
    (α : MulAut (StatedOmega Q0))
    (hfix : ∀ A : StatedOmega Q0, ((A : GL ι K) : Matrix ι ι K) *ᵥ v = v → α A = A) :
    α = 1 ∨ α = F4Pilot.omegaSymmetryAut eI Q hQ h v := by
  set Q' := reindexQuadraticForm eI Q with hQ'
  set θ := statedDerivedReindexEquiv eI Q hQ with hθ
  set v' := reindexVectorEquiv eI v with hv'def
  have hv' : Q' v' = 1 := by rw [F4Pilot.reindexQuadraticForm_reindexVectorEquiv, hv]
  set α' : MulAut (matrixDerived Q') := (θ.symm.trans α).trans θ with hα'
  have hα'app : ∀ A, α' (θ A) = θ (α A) := fun A => by
    rw [hα', MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hfix' : ∀ X : matrixDerived Q', (X.val : Matrix (Fin d) (Fin d) K) *ᵥ v' = v' →
      α' X = X := by
    intro X hX
    obtain ⟨A, rfl⟩ := θ.surjective X
    have hA : ((A : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
      apply (reindexVectorEquiv (K := K) eI).injective
      rw [← F4Pilot.statedDerivedReindexEquiv_mulVec eI Q hQ]
      exact hX
    rw [hα'app, hfix A hA]
  rcases eq_one_or_eq_symmetry_of_fix_two hK hnd hd htop hv' α' hfix' with h1 | h1
  · left
    refine MulEquiv.ext fun A => θ.injective ?_
    rw [← hα'app, h1]
    rfl
  · right
    refine MulEquiv.ext fun A => (F4Pilot.omegaProjEquiv eI Q hQ h).injective ?_
    rw [F4Pilot.omegaProjEquiv_omegaSymmetryAut, F4Pilot.omegaProjEquiv_apply,
      F4Pilot.omegaProjEquiv_apply]
    change _ = matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' (θ A))
    rw [matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    rw [← CFSG.RankThree.PartOne.AUTSL.conjAct_apply,
      CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_val, ← hα'app, h1,
      inv_eq_of_mul_eq_one_right (symmetryGL_mul_self Q' v')]

end Stated

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_or_eq_kOmegaBetaC_of_fix (hK : Nat.card K = 2) {r : ℕ} (hr : 4 ≤ r)
    (α : MulAut (StatedOmega (StatedQuadPlus (r + 1) K)))
    (hfix : ∀ g ∈ fixedSubgroup (kOmegaBetaC K r), α g = g) :
    α = 1 ∨ α = kOmegaBetaC K r :=
  eq_one_or_eq_omegaSymmetryAut_of_fix_two hK (plusIndexEquiv (r + 1)) (quadPlus (r + 1) K)
    (coe_quadPlus (r + 1) K) (kOmega_matrixDerivedScalars_eq_bot K r)
    (regular_coordinateQuadPlus (r + 1) K (by omega)).1 (by omega)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K (r + 1)
      (by omega))
    (kOmega_quadPlus_vec K r) α fun A hA =>
      hfix A ((mem_fixedSubgroup_kOmegaBetaC_iff K (by omega) A).2 hA)

theorem eq_one_or_eq_kOmMBetaC_of_fix (hK : Nat.card K = 2) {r : ℕ} (hr : 3 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (StatedOmega (StatedQuadMinus (r + 1) K b c)))
    (hfix : ∀ g ∈ fixedSubgroup (kOmMBetaC K r b c), α g = g) :
    α = 1 ∨ α = kOmMBetaC K r b c :=
  eq_one_or_eq_omegaSymmetryAut_of_fix_two hK (minusIndexEquiv (r + 1) (by omega))
    (quadMinus (r + 1) K b c) (coe_quadMinus (r + 1) K b c)
    (kOmM_matrixDerivedScalars_eq_bot K r b c)
    (regular_coordinateQuadMinus (r + 1) K b c (by omega) hirr).1 (by omega)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K (r + 1)
      (by omega) b c hirr)
    (kOmM_quadMinus_vec K r) α fun A hA =>
      hfix A ((mem_fixedSubgroup_kOmMBetaC_iff K hr hirr A).2 hA)

end Models

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r + 1) K} {t : G} {k : Fin (r + 1)}

theorem IsNsOmPlusParam.comp_betaC {hr : 2 ≤ r} {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) :
    IsNsOmPlusParam hK hr hr3 e t k ((kOmegaBetaC K r).trans Φ) := by
  refine ⟨fun g => hΦ.1 (kOmegaBetaC K r g), fun x => ?_⟩
  have hmem : q2OmIota hr hK hr3 x ∈ fixedSubgroup (kOmegaBetaC K r) := by
    rw [← range_q2OmIota hr hK hr3]
    exact ⟨x, rfl⟩
  have hfx : kOmegaBetaC K r (q2OmIota hr hK hr3 x) = q2OmIota hr hK hr3 x := hmem
  rw [MulEquiv.trans_apply, hfx]
  exact hΦ.2 x

theorem IsNsOmMinusParam.comp_betaC {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmMinusParam hK hr3 e t k Φ) :
    IsNsOmMinusParam hK hr3 e t k ((kOmMBetaC K r 1 1).trans Φ) := by
  refine ⟨fun g => hΦ.1 (kOmMBetaC K r 1 1 g), fun x => ?_⟩
  have hmem : q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK x ∈
      fixedSubgroup (kOmMBetaC K r 1 1) := by
    rw [← range_q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK]
    exact ⟨x, rfl⟩
  have hfx : kOmMBetaC K r 1 1 (q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK x) =
      q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK x := hmem
  rw [MulEquiv.trans_apply, hfx]
  exact hΦ.2 x

end Param

end CFSG.SeitzReduction.SymplecticPilot
