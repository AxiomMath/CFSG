module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieComp
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

namespace P58b3

variable {K : Type} [Field K] [Finite K]

abbrev rhoL : SL(2, K) →* DeterminantIsometries K :=
  specialRho.comp (MonoidHom.inl _ _)

abbrev rhoR : SL(2, K) →* DeterminantIsometries K :=
  specialRho.comp (MonoidHom.inr _ _)

omit [Finite K] in
theorem rhoL_apply (g : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    (rhoL g).val X = (g : Matrix (Fin 2) (Fin 2) K) * X := by
  rw [MonoidHom.comp_apply, specialRho_apply]
  simp

omit [Finite K] in
theorem rhoR_apply (g : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    (rhoR g).val X = X * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [MonoidHom.comp_apply, specialRho_apply]
  simp

omit [Finite K] in
theorem rhoL_injective : Function.Injective (rhoL (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := congrArg (fun φ : DeterminantIsometries K => φ.val 1) hg
  simp only [rhoL_apply, Matrix.mul_one] at h
  exact Subtype.ext h

omit [Finite K] in
theorem rhoR_injective : Function.Injective (rhoR (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := congrArg (fun φ : DeterminantIsometries K => φ.val 1) hg
  simp only [rhoR_apply, Matrix.one_mul] at h
  have h1 : g⁻¹ = 1 := Subtype.ext h
  rw [← inv_inv g, h1, inv_one]

omit [Finite K] in
theorem specialRho_eq_mul (A B : SL(2, K)) : specialRho (A, B) = rhoL A * rhoR B := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
  congr 1
  simp

omit [Finite K] in
theorem rhoL_mul_rhoR (A B : SL(2, K)) : rhoL A * rhoR B = rhoR B * rhoL A := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  simp

omit [Finite K] in
theorem rhoR_neg_one : rhoR (-1 : SL(2, K)) = rhoL (-1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [rhoR_apply, rhoL_apply]
  have h : (-1 : SL(2, K))⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)
  rw [h]
  simp

omit [Finite K] in
theorem rhoL_neg_one_apply (X : Matrix (Fin 2) (Fin 2) K) : (rhoL (-1 : SL(2, K))).val X = -X := by
  rw [rhoL_apply]
  simp

omit [Finite K] in
theorem rhoL_neg_one_mem_center : rhoL (-1 : SL(2, K)) ∈ center (DeterminantIsometries K) := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change g.val ((rhoL (-1 : SL(2, K))).val X) = (rhoL (-1 : SL(2, K))).val (g.val X)
  rw [rhoL_neg_one_apply, rhoL_neg_one_apply, map_neg]

omit [Finite K] in
theorem orderOf_rhoL_neg_one (h2 : (2 : K) ≠ 0) : orderOf (rhoL (-1 : SL(2, K))) = 2 := by
  have hne : rhoL (-1 : SL(2, K)) ≠ 1 := by
    intro h
    have h1 := congrArg (fun φ : DeterminantIsometries K => φ.val 1) h
    simp only [rhoL_neg_one_apply] at h1
    have h00 := congrFun (congrFun h1 0) 0
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h00
    change (-1 : K) = 1 at h00
    exact h2 (by linear_combination -h00)
  refine orderOf_eq_prime ?_ hne
  rw [← map_pow]
  have h : (-1 : SL(2, K)) ^ 2 = 1 := by rw [pow_two]; simp
  rw [h, map_one]

omit [Finite K] in
theorem range_rhoL_le : (rhoL (K := K)).range ≤ leftRightImage K := by
  rintro _ ⟨g, rfl⟩
  exact specialImage_le_leftRightImage ⟨_, rfl⟩

omit [Finite K] in
theorem range_rhoR_le : (rhoR (K := K)).range ≤ leftRightImage K := by
  rintro _ ⟨g, rfl⟩
  exact specialImage_le_leftRightImage ⟨_, rfl⟩

omit [Finite K] in
theorem normal_range_rhoL : ((rhoL (K := K)).range.subgroupOf (leftRightImage K)).Normal := by
  rw [normal_subgroupOf_iff range_rhoL_le]
  rintro _ _ ⟨a, rfl⟩ ⟨z, rfl⟩
  have hdet : ((z.val.1 : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K) *
      ((z.val.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, a.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]
  refine ⟨⟨_, hdet⟩, ?_⟩
  change rho (specialPairs (_, 1)) = rho z * rho (specialPairs (a, 1)) * (rho z)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    simp [specialPairs]
    rfl
  · simp [specialPairs]

omit [Finite K] in
theorem normal_range_rhoR : ((rhoR (K := K)).range.subgroupOf (leftRightImage K)).Normal := by
  rw [normal_subgroupOf_iff range_rhoR_le]
  rintro _ _ ⟨a, rfl⟩ ⟨z, rfl⟩
  have hdet : ((z.val.2 : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K) *
      ((z.val.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, a.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]
  refine ⟨⟨_, hdet⟩, ?_⟩
  change rho (specialPairs (1, _)) = rho z * rho (specialPairs (1, a)) * (rho z)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · simp [specialPairs]
  · apply Units.ext
    simp [specialPairs]
    rfl

theorem units_sq_eq_one (hK : Nat.card K = 3) (u : Kˣ) : u ^ 2 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  rw [← hcard]
  exact pow_card_eq_one'

omit [Finite K] in
theorem eq_one_or_neg_one_of_toGL_eq_scalar {A : SL(2, K)} {c : Kˣ}
    (hA : Matrix.SpecialLinearGroup.toGL A = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (hc : c ^ 2 = 1) : A = 1 ∨ A = -1 := by
  have hc' : (c : K) * c = 1 := by
    rw [← Units.val_mul, ← pow_two, hc, Units.val_one]
  have hval : (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (c : K) := by
    have h := congrArg Units.val hA
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h
    exact h
  rcases mul_self_eq_one_iff.mp hc' with h | h
  · left
    apply Subtype.ext
    rw [hval, h]
    simp
  · right
    apply Subtype.ext
    rw [hval, h]
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem exists_sl_of_rho_pow_three (hK : Nat.card K = 3) (z : equalDeterminants K)
    (hz : rho z ^ 3 = 1) :
    ∃ A B : SL(2, K), rho z = rhoL A * rhoR B ∧ (A ^ 3 = 1 ∨ A ^ 3 = -1) ∧
      (B ^ 3 = 1 ∨ B ^ 3 = -1) := by
  rw [← map_pow, rho_eq_one_iff] at hz
  obtain ⟨c, hc⟩ := hz
  have hc2 := units_sq_eq_one hK c
  have h1 : z.val.1 ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    have h := congrArg (fun w : equalDeterminants K => w.val.1) hc
    simpa [scalarPair] using h
  have h2 : z.val.2 ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    have h := congrArg (fun w : equalDeterminants K => w.val.2) hc
    simpa [scalarPair] using h
  have hdet3 : Matrix.GeneralLinearGroup.det (z.val.1 ^ 3) = c ^ 2 := by
    rw [h1]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_pow_eq_pow_val]
  have hd : Matrix.GeneralLinearGroup.det z.val.1 = 1 := by
    have hu := units_sq_eq_one hK (Matrix.GeneralLinearGroup.det z.val.1)
    rw [map_pow, hc2] at hdet3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hu, one_mul] at hdet3
    exact hdet3
  have hd₁ : (z.val.1 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h := congrArg Units.val hd
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
  have hd₂ : (z.val.2 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← (mem_equalDeterminants z.val.1 z.val.2).mp z.property]
    exact hd₁
  set A : SL(2, K) := ⟨z.val.1, hd₁⟩ with hAdef
  set B : SL(2, K) := ⟨z.val.2, hd₂⟩ with hBdef
  have hAz : Matrix.SpecialLinearGroup.toGL A = z.val.1 := Units.ext rfl
  have hBz : Matrix.SpecialLinearGroup.toGL B = z.val.2 := Units.ext rfl
  refine ⟨A, B, ?_, ?_, ?_⟩
  · rw [← specialRho_eq_mul]
    change rho z = rho (specialPairs (A, B))
    congr 1
    apply Subtype.ext
    exact Prod.ext hAz.symm hBz.symm
  · have h := eq_one_or_neg_one_of_toGL_eq_scalar (A := A ^ 3) (by rw [map_pow, hAz, h1]) hc2
    exact h
  · have h := eq_one_or_neg_one_of_toGL_eq_scalar (A := B ^ 3) (by rw [map_pow, hBz, h2]) hc2
    exact h

omit [Finite K] in
theorem sq_eq_neg_one_of_pow_four (h2 : (2 : K) ≠ 0) {g : SL(2, K)} (h4 : g ^ 4 = 1)
    (h2' : g ^ 2 ≠ 1) : g ^ 2 = -1 := by
  have h := Burgoyne.C.eq_one_or_eq_neg_one h2 (g ^ 2) (by
    rw [← pow_add]
    exact h4)
  exact h.resolve_left h2'

theorem rhoL_neg_one_mem (hK : Nat.card K = 3) {H : Subgroup (DeterminantIsometries K)}
    (hHC : H ≤ leftRightImage K) (hH : (H.subgroupOf (leftRightImage K)).IsSubnormal)
    {r : DeterminantIsometries K} (hr : r ∈ H) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    rhoL (-1 : SL(2, K)) ∈ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  obtain ⟨z, rfl⟩ := hHC hr
  obtain ⟨A, B, hAB, hA3, hB3⟩ := exists_sl_of_rho_pow_three hK z hr3
  by_cases hA : A = 1 ∨ A = -1
  · by_cases hB : B = 1 ∨ B = -1
    ·
      exfalso
      apply hr1
      have hsq : rho z ^ 2 = 1 := by
        rw [hAB, Commute.mul_pow (rhoL_mul_rhoR A B), ← map_pow, ← map_pow]
        have hA2 : A ^ 2 = 1 := by rcases hA with rfl | rfl <;> simp [pow_two]
        have hB2 : B ^ 2 = 1 := by rcases hB with rfl | rfl <;> simp [pow_two]
        rw [hA2, hB2, map_one, map_one, mul_one]
      calc rho z = rho z ^ 3 * (rho z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hr3, hsq, inv_one, mul_one]
    ·
      rw [not_or] at hB
      have hxa : rho z = rhoR B * rhoL A := by rw [hAB, rhoL_mul_rhoR]
      obtain ⟨k, ⟨hkH, g, rfl⟩, hk4, hk2⟩ := exists_mem_inf_of_noncentral hK rhoR rhoR_injective
        range_rhoR_le normal_range_rhoR hHC hH hr hr3 ⟨B, rfl⟩
        (fun s hs => by
          obtain ⟨b, rfl⟩ := hs
          exact (rhoL_mul_rhoR A b).symm)
        hxa (by
          rcases hB3 with h | h
          · left
            rw [← map_pow, h, map_one]
          · right
            rw [← map_pow, h])
        (fun h => hB.1 (rhoR_injective (h.trans (map_one _).symm)))
        (fun h => hB.2 (rhoR_injective h))
      have hg4 : g ^ 4 = 1 := rhoR_injective (by rw [map_pow, hk4, map_one])
      have hg2 : g ^ 2 ≠ 1 := fun h => hk2 (by rw [← map_pow, h, map_one])
      have hgsq := sq_eq_neg_one_of_pow_four h2 hg4 hg2
      rw [← rhoR_neg_one, ← hgsq, map_pow]
      exact pow_mem hkH 2
  ·
    rw [not_or] at hA
    obtain ⟨k, ⟨hkH, g, rfl⟩, hk4, hk2⟩ := exists_mem_inf_of_noncentral hK rhoL rhoL_injective
      range_rhoL_le normal_range_rhoL hHC hH hr hr3 ⟨A, rfl⟩
      (fun s hs => by
        obtain ⟨a, rfl⟩ := hs
        exact rhoL_mul_rhoR a B)
      hAB (by
        rcases hA3 with h | h
        · left
          rw [← map_pow, h, map_one]
        · right
          rw [← map_pow, h])
      (fun h => hA.1 (rhoL_injective (h.trans (map_one _).symm)))
      (fun h => hA.2 (rhoL_injective h))
    have hg4 : g ^ 4 = 1 := rhoL_injective (by rw [map_pow, hk4, map_one])
    have hg2 : g ^ 2 ≠ 1 := fun h => hk2 (by rw [← map_pow, h, map_one])
    have hgsq := sq_eq_neg_one_of_pow_four h2 hg4 hg2
    rw [← hgsq, map_pow]
    exact pow_mem hkH 2

omit [Finite K] in
theorem commutator_le_leftRightImage :
    commutator (DeterminantIsometries K) ≤ leftRightImage K := by
  refine Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top ?_ ?_
    (H := zpowers (tau (K := K)))
  · rw [eq_top_iff]
    intro g _
    obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion g
    · exact mem_sup_left ⟨z, rfl⟩
    · exact mul_mem_sup ⟨z, rfl⟩ (mem_zpowers _)
  · infer_instance

open Burgoyne.PSL (isoOrthGL trans_commutator isQuasisimple_trans map_commutator_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial
  (orthogonal_low_dimensional_fixed_derived_component_coverage)

theorem exists_central_involution_of_omegaR_four (hK : Nat.card K = 3) {m : ℕ} (hm : m = 4)
    (R : GL (Fin m) K) (hR : (R : Matrix (Fin m) (Fin m) K)ᵀ = R)
    (hq : ¬ IsQuasisimple (Burgoyne.C.omegaR R)) {H : Subgroup ↥(Burgoyne.C.omegaR R)}
    (hH : H.IsSubnormal) {r : ↥(Burgoyne.C.omegaR R)} (hr : r ∈ H) (hr3 : r ^ 3 = 1)
    (hr1 : r ≠ 1) :
    ∃ s ∈ H, s ∈ center ↥(Burgoyne.C.omegaR R) ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK2 R hR
  have hdim : Module.finrank K (Fin m → K) = 4 := by rw [Module.finrank_fin_fun, hm]
  set e₁ := isoOrthGL hK2 R hR with he₁
  obtain ⟨S, hS2, hSQ⟩ : ∃ S : Submodule K (Fin m → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, Q x = 0 := by
    by_contra hS
    obtain ⟨-, -, -, -, h4n, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, -, -, -, -, -, -, -, hq'⟩ := h4n hodd hdim hS
    apply hq
    have h := isQuasisimple_trans e₁ hq'
    rwa [trans_commutator] at h
  obtain ⟨-, e₂, -, -, -⟩ := split_four_determinant_form_isometry Q hQnd hdim S hS2 hSQ
  let Φ₁ : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ≃* ↥(Burgoyne.C.omegaR R) :=
    (((commutator _).equivMapOfInjective _ e₁.injective).trans
      (((commutator _).map e₁.toMonoidHom).equivMapOfInjective _
        (Subgroup.subtype_injective _))).trans (MulEquiv.subgroupCongr (trans_commutator e₁))
  let Φ₂ : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ≃*
      ↥(commutator (DeterminantIsometries K)) :=
    ((commutator _).equivMapOfInjective _ e₂.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_mulEquiv e₂))
  let Φ : ↥(Burgoyne.C.omegaR R) ≃* ↥(commutator (DeterminantIsometries K)) := Φ₁.symm.trans Φ₂
  set N := commutator (DeterminantIsometries K) with hNdef
  set H' : Subgroup (DeterminantIsometries K) := (H.map Φ.toMonoidHom).map N.subtype with hH'
  have hH'N : H' ≤ N := map_subtype_le _
  have hH's : H'.IsSubnormal := by
    refine IsSubnormal.trans hH'N ?_ (Subgroup.Normal.isSubnormal inferInstance)
    rw [hH', show ((H.map Φ.toMonoidHom).map N.subtype).subgroupOf N = H.map Φ.toMonoidHom from
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _]
    exact hH.map Φ.surjective
  have hH'C : H' ≤ leftRightImage K := hH'N.trans commutator_le_leftRightImage
  have hrm : ((Φ r : N) : DeterminantIsometries K) ∈ H' := ⟨Φ r, ⟨r, hr, rfl⟩, rfl⟩
  have hneg := rhoL_neg_one_mem hK hH'C hH's.subgroupOf hrm
    (by rw [← Subgroup.coe_pow, ← map_pow, hr3, map_one, Subgroup.coe_one])
    (fun h => hr1 (Φ.injective (by rw [map_one]; exact Subtype.ext h)))
  obtain ⟨s', ⟨s, hs, rfl⟩, hs'⟩ := hneg
  have hs'' : ((Φ s : N) : DeterminantIsometries K) = rhoL (-1 : SL(2, K)) := hs'
  have hcen : Φ s ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs'']
    exact mem_center_iff.mp rhoL_neg_one_mem_center (g : DeterminantIsometries K)
  refine ⟨s, hs, ?_, ?_⟩
  · rw [mem_center_iff]
    intro g
    apply Φ.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hcen (Φ g)
  · rw [← MulEquiv.orderOf_eq Φ, ← Subgroup.orderOf_coe, hs'', orderOf_rhoL_neg_one h2]

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)

theorem exists_central_involution_of_le_blockP (hK : Nat.card K = 3) {d : ℕ} {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hI4 : I.card = 4) (hIc : Iᶜ.Nonempty)
    (hq : ¬ IsQuasisimple (Burgoyne.C.blockP K hw I))
    {H : Subgroup (Assembly.LowTwoRank.StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hHI : H ≤ Burgoyne.C.blockP K hw I)
    (hH : (H.subgroupOf (Burgoyne.C.blockP K hw I)).IsSubnormal) {r} (hr : r ∈ H)
    (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∃ s ∈ H, (∀ g ∈ Burgoyne.C.blockP K hw I, g * s = s * g) ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  obtain ⟨e⟩ := Burgoyne.C.nonempty_projBlock_equiv hw h2 hIc (le_refl (Burgoyne.C.omegaI hw I))
  rw [← Burgoyne.C.blockP_eq_projBlock] at e
  have hq' : ¬ IsQuasisimple (Burgoyne.C.omegaI hw I) := fun h =>
    hq (LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  set H₀ := (H.subgroupOf (Burgoyne.C.blockP K hw I)).map e.toMonoidHom with hH₀
  set r₀ : ↥(Burgoyne.C.blockP K hw I) := ⟨r, hHI hr⟩ with hr₀
  have hr₀1 : r₀ ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
  obtain ⟨s₀, ⟨t, ht, rfl⟩, hs₀c, hs₀2⟩ := exists_central_involution_of_omegaR_four hK hI4
    (diagGL (wRes_ne_zero hw I)) (diagGL_transpose (wRes_ne_zero hw I)) hq'
    (hH.map e.surjective) (r := e r₀)
    (by exact Subgroup.mem_map_of_mem e.toMonoidHom (mem_subgroupOf.mpr hr))
    (by rw [← map_pow, show r₀ ^ 3 = 1 from Subtype.ext (by simpa using hr3), map_one])
    (fun h => hr₀1 (e.injective (h.trans (map_one e).symm)))
  refine ⟨t, mem_subgroupOf.mp ht, fun g hg => ?_, ?_⟩
  · have h := mem_center_iff.mp hs₀c (e ⟨g, hg⟩)
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e]
    exact hs₀2

theorem false_of_psl23_le_blockP (hK : Nat.card K = 3) {d : ℕ} {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hI4 : I.card = 4) (hIc : Iᶜ.Nonempty)
    (hq : ¬ IsQuasisimple (Burgoyne.C.blockP K hw I))
    {H : Subgroup (Assembly.LowTwoRank.StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hHI : H ≤ Burgoyne.C.blockP K hw I)
    (hH : (H.subgroupOf (Burgoyne.C.blockP K hw I)).IsSubnormal)
    (eH : ↥H ⧸ pPrimeCore 2 ↥H ≃* PSL(2, ZMod 3)) : False := by
  have hF : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have hPSL : Nat.card PSL(2, ZMod 3) = 12 := by
    have h := Burgoyne.C.card_PSL_mul_two hF
    rw [GorensteinWalter.sl2_card_formula, Nat.card_zmod] at h
    omega
  have h3 : 3 ∣ Nat.card ↥H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥H),
      Nat.card_congr eH.toEquiv, hPSL]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3
  obtain ⟨s, hs, hsc, hs2⟩ := exists_central_involution_of_le_blockP hK hw hI4 hIc hq hHI hH
    (r := (r : Assembly.LowTwoRank.StatedProj (matrixDerived (oQ (diagGL hw))))) r.2
    (by rw [← Subgroup.coe_pow, ← hr, pow_orderOf_eq_one, Subgroup.coe_one])
    (fun h => by
      have h1 : r = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hr
      exact absurd hr (by norm_num))
  refine P58b.OLie.false_of_mem_center_psl2 eH (x := ⟨s, hs⟩) ?_ (by
    rw [Subgroup.orderOf_mk]; exact hs2)
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (hsc g (hHI g.2))

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
