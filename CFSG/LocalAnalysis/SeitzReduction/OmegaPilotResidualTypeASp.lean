module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeALevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviKernel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSympChart

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank Matrix
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis)

section Fix

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem mem_autFixSubgroup_of_commute (hQ : ∃ v, Q v ≠ 0) (s : matrixIsometries Q)
    {x : matrixProjectiveDerived Q}
    (h : ∀ v, projLift hQ x (matrixLinearEquiv s.val v) =
      matrixLinearEquiv s.val (projLift hQ x v)) :
    x ∈ autFixSubgroup (isometryConjugationHom Q s) := by
  change isometryConjugationHom Q s x = x
  apply projLiftHom_injective hQ
  rw [projLiftHom_apply, projLiftHom_apply]
  refine LinearEquiv.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (matrixLinearEquiv s.val).surjective w
  have hk := projLift_kappa_apply hQ (matrixIsometryInclusion Q s) x v
  exact hk.trans (h v).symm

end Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ) {r : ℕ}
  (b : Basis (Fin r ⊕ Fin r) K (LinearMap.range (lowNil (K := K) P)))

@[expose] noncomputable def matrixToAut :
    GL (Fin r ⊕ Fin r) K →* (LinearMap.range (lowNil (K := K) P) ≃ₗ[K]
      LinearMap.range (lowNil (K := K) P)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).toMonoidHom.comp
    (Units.map (Matrix.toLinAlgEquiv b).toRingEquiv.toMonoidHom)

@[expose] noncomputable def spLevi :
    StatedSp r K →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
  (leviHom P).comp ((matrixToAut P b).comp (StatedSp r K).subtype)

omit [Finite K] [CharP K 2] in
theorem spLevi_apply (A : StatedSp r K) (v : Fin (2 * n) → K) :
    spLevi P b A v = leviLin P (matrixToAut P b A).toLinearMap v :=
  rfl

omit [Finite K] [CharP K 2] in
theorem statedSp_transpose_mul_J_mul (A : StatedSp r K) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0 * ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
  have h1 : (A : GL (Fin r ⊕ Fin r) K) ∈ TauCeti.GLSymplectic (Fin r) K :=
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := K) ▸ A.2
  rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup] at h1
  exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr h1

variable {P b}

omit [Finite K] in
theorem spLevi_mem_orthogonalGroup
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (A : StatedSp r K) :
    spLevi P b A ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [spLevi_apply]
  refine coordinateQuadPlus_leviLin _ (fun u u' => ?_) v
  rw [← wallForm_eq_lowForm, ← wallForm_eq_lowForm]
  exact toLin_isometry_of_mem (wallForm_isAlt _ _ _ fun x => by
    rw [polar_lowNil_left, QuadraticMap.polarBilin_apply_apply]
    exact polar_lowNil_self P x) hb (statedSp_transpose_mul_J_mul A) u u'

omit [Finite K] in
theorem spLevi_commute (A : StatedSp r K) (v : Fin (2 * n) → K) :
    spLevi P b A (matrixLinearEquiv (lowRep P).val v) =
      matrixLinearEquiv (lowRep P).val (spLevi P b A v) := by
  change spLevi P b A (matrixLinearEquiv (lowRepGL P) v) = matrixLinearEquiv (lowRepGL P) _
  rw [matrixLinearEquiv_lowRepGL, matrixLinearEquiv_lowRepGL, map_add, spLevi_apply,
    spLevi_apply, leviLin_lowNil]

variable (K P) in
noncomputable abbrev typeACore : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  perfectCore (autFixSubgroup (isometryConjugationHom (coordinateQuadPlus n K) (lowRep P)))

omit [Finite K] in
theorem projLift_lowNil_of_mem_core (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} (hx : x ∈ typeACore K P)
    (v : Fin (2 * n) → K) : projLift hQ x (lowNil P v) = lowNil P (projLift hQ x v) := by
  have h := projLift_sNil_of_mem_core hQ (lowRep P) hx v
  rwa [sNil_lowRep] at h

theorem isPerfect_statedSp (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    Group.IsPerfect (StatedSp r K) := by
  have := (simple_perfect_statedProj_of_one_le hq4 hr).2
  exact Group.IsPerfect.ofSurjective (f := (spProjEquivCharTwo K r).toMonoidHom)
    (spProjEquivCharTwo K r).surjective

theorem commutator_range_spLevi (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    ⁅(spLevi P b).range, (spLevi P b).range⁆ = (spLevi P b).range := by
  have := isPerfect_statedSp (K := K) hq4 hr
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (spLevi P b))

theorem range_spLevi_le
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    (spLevi P b).range ≤ orthDerived (coordinateQuadPlus n K) := by
  rw [← commutator_range_spLevi hq4 hr]
  have hO : (spLevi P b).range ≤ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) := by
    rintro _ ⟨A, rfl⟩
    exact spLevi_mem_orthogonalGroup hb A
  exact Subgroup.commutator_mono hO hO

variable (P b) in
@[expose] noncomputable def spLeviP
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    StatedSp r K →* matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (projHom _).comp ((spLevi P b).codRestrict _ fun A => range_spLevi_le hb hq4 hr ⟨A, rfl⟩)

theorem projLift_spLeviP (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) (A : StatedSp r K) :
    projLift hQ (spLeviP P b hb hq4 hr A) = spLevi P b A :=
  projLift_projHom hQ _

theorem range_spLeviP_le (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    (spLeviP P b hb hq4 hr).range ≤ typeACore K P := by
  have := isPerfect_statedSp (K := K) hq4 hr
  refine le_perfectCore_of_perfect ?_
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (spLeviP P b hb hq4 hr)))
  rintro _ ⟨A, rfl⟩
  refine mem_autFixSubgroup_of_commute hQ (lowRep P) fun v => ?_
  rw [projLift_spLeviP hQ]
  exact spLevi_commute A v

variable (P b) in
@[expose] noncomputable def spLeviX (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) :
    StatedSp r K →* typeACore K P :=
  (spLeviP P b hb hq4 hr).codRestrict _ fun A => range_spLeviP_le hQ hb hq4 hr ⟨A, rfl⟩

theorem projLift_spLeviX (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) (A : StatedSp r K) :
    projLift hQ ((spLeviX P b hQ hb hq4 hr A : typeACore K P) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) = spLevi P b A :=
  projLift_spLeviP hQ hb hq4 hr A

theorem rangeRestrictHom_spLeviX (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (hb : IsSymplecticBasis (wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K))
      (lowNil P) (polar_lowNil_left P)) b) (hq4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) (A : StatedSp r K) :
    rangeRestrictHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) (spLeviX P b hQ hb hq4 hr A) =
        Matrix.toLin b b
          ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  change projLift hQ ((spLeviX P b hQ hb hq4 hr A : typeACore K P) :
    matrixProjectiveDerived (coordinateQuadPlus n K)) (u : Fin (2 * n) → K) = _
  rw [projLift_spLeviX, spLevi_apply, leviLin_apply_of_mem]
  rfl

end CFSG.SeitzReduction.OmegaPilot
