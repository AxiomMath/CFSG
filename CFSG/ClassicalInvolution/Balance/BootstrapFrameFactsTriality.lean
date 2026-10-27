module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsNine
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Untwist

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

variable (p : ℕ) [Fact p.Prime]

theorem exists_conj_trialityD4Phi_eq_rootDiagUnit (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {x : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)} (hx : x * x = 1)
    (hx1 : x ≠ 1) :
    ∃ y : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      CFSG.ClassicalInvolution.ModelFacts.trialityD4Phi p e
          (AlgebraicClosure (GaloisField p (3 * e))) (y * x * y⁻¹) =
        rootDiagUnit TwistTag.D4.tag
          (signMaskTuple TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) 4) := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hchar : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set Φ := CFSG.ClassicalInvolution.ModelFacts.trialityD4Phi p e k with hΦ
  have hΦx : Φ x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) :=
    CFSG.ClassicalInvolution.ModelFacts.trialityD4Phi_mem_fixedPointsIn p e hp2 he x
  have hΦx2 : (Φ x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hx, map_one]
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, -⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_twisted_toral_reduction p TwistTag.D4 hp2 he
      d4SignDiagramReps h4.permChar_eq h4.exists_rep
      (CFSG.ClassicalInvolution.ModelFacts.untwistAt_d4 p hp2 e) hΦx hΦx2
  have hr' : r.mask = 0 ∨ r.mask = 4 := by
    rcases List.mem_cons.1 hr with h | h
    · exact Or.inl (congrArg SignRep.mask h)
    · exact Or.inr (congrArg SignRep.mask (List.mem_singleton.1 h))
  rcases hr' with h | h
  ·
    exfalso
    apply hx1
    have h0 : signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask) = 1 := by
      rw [h, signCharTuple_signMaskChar]
      funext j
      simp [signMaskTuple]
    rw [h0, rootDiagUnit_one, mul_inv_eq_one] at hg₁x
    have hΦ1 : Φ x = 1 := mul_left_cancel (hg₁x.trans (mul_one g₁).symm)
    exact CFSG.ClassicalInvolution.ModelFacts.trialityD4Phi_injective p e k
      (hΦ1.trans (map_one Φ).symm)
  ·
    have h4' : signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask) =
        signMaskTuple TwistTag.D4.tag k 4 := by
      rw [h, signCharTuple_signMaskChar]
    rw [h4'] at hg₁x
    have hg₁R : g₁ ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) :=
      mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩
    obtain ⟨u, hu, -, y, hy⟩ :=
      CFSG.ClassicalInvolution.ModelFacts.exists_torus_mul_of_mem_fixedPointsIn_d4 p e hp2 he hg₁R
    refine ⟨y, ?_⟩
    have hΦy : Φ y = u⁻¹ * g₁ := (inv_mul_eq_iff_eq_mul.2 hy).symm
    have hcomm := rootDiagUnit_mul_comm_of_mem_torusGroup (K := k)
      (signMaskTuple TwistTag.D4.tag k 4) hu
    calc Φ (y * x * y⁻¹) = Φ y * Φ x * (Φ y)⁻¹ := by simp only [map_mul, map_inv]
      _ = u⁻¹ * (g₁ * Φ x * g₁⁻¹) * u := by
          rw [hΦy]
          group
      _ = u⁻¹ * rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) * u := by
          rw [hg₁x]
      _ = u⁻¹ * (rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) * u) :=
          mul_assoc _ _ _
      _ = u⁻¹ * (u * rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4)) := by
          rw [hcomm]
      _ = rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) :=
          inv_mul_cancel_left u _

variable {p}

theorem trialityD4_involutions_conj (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {x x' : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)} (hx : x * x = 1)
    (hx' : x' * x' = 1) (hx1 : x ≠ 1) (hx1' : x' ≠ 1) :
    ∃ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), g * x * g⁻¹ = x' := by
  obtain ⟨y, hy⟩ := exists_conj_trialityD4Phi_eq_rootDiagUnit p hp2 he hx hx1
  obtain ⟨y', hy'⟩ := exists_conj_trialityD4Phi_eq_rootDiagUnit p hp2 he hx' hx1'
  have h := CFSG.ClassicalInvolution.ModelFacts.trialityD4Phi_injective p e
    (AlgebraicClosure (GaloisField p (3 * e))) (hy.trans hy'.symm)
  refine ⟨y'⁻¹ * y, ?_⟩
  calc y'⁻¹ * y * x * (y'⁻¹ * y)⁻¹ = y'⁻¹ * (y * x * y⁻¹) * y' := by group
    _ = y'⁻¹ * (y' * x' * y'⁻¹) * y' := by rw [h]
    _ = x' := by group

theorem fundInvolutionsConj_trialityD4 {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 n p e) : FundInvolutionsConj p .trialityD4 n e := by
  intro _ _ _ _ r _ r' _ hrr hrr' hr1 hr1' _ _
  exact trialityD4_involutions_conj hp2 hadm.2.1 hrr hrr' hr1 hr1'

variable (p) in
theorem trialityD4InvolutionsConj : TrialityD4InvolutionsConj p :=
  fun _ _ hp2 hadm => fundInvolutionsConj_trialityD4 hp2 hadm

variable (p) in
theorem twoClassInvolutionsConj : TwoClassInvolutionsConj p :=
  twoClassInvolutionsConj_of_trialityD4 (trialityD4InvolutionsConj p)

theorem bootTriple_of_model_noFrameMF1 {f : ℕ} (h9 : p ^ f ≠ 9) (h27 : p ^ f ≠ 27)
    (hmodel : Balance.LayerGenerationModel)
    (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f) : Generic.CoreAssembly.BootTriple p f :=
  bootTriple_of_model' h9 h27 hmodel (twoClassInvolutionsConj p) hcover

theorem bootTriple_of_model_nine_noFrameMF1 {f : ℕ} (h27 : p ^ f ≠ 27)
    (hmodel : Balance.LayerGenerationModel) (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f)
    (hlevi : FrameLevi p f) : Generic.CoreAssembly.BootTriple p f :=
  bootTriple_of_model_nine' h27 hmodel (twoClassInvolutionsConj p) hcover hlevi

end CFSG.ClassicalInvolution.Balance.Bootstrap
