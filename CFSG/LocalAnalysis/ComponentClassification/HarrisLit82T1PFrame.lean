module

public import CFSG.LieType.HighestRoot.CentSpinThree
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (fr : Frame Q)

theorem La_upperSL2_sub (c : K) (v : V) :
    fr.La (upperSL2 c) v - v = c • (fr.La (upperSL2 1) v - v) := by
  have hU : ∀ a : K, (upperSL2 a : Matrix (Fin 2) (Fin 2) K) = 1 + a • !![0, 1; 0, 0] := by
    intro a
    rw [coe_upperSL2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Frame.La_apply, Frame.La_apply, add_sub_cancel_left, add_sub_cancel_left, ← map_smul, hU, hU,
    Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, one_smul,
    add_sub_cancel_left, add_sub_cancel_left]

theorem eq_of_commute_La_upperSL2 {σ : K ≃+* K} {F : V ≃+ V}
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (hc : ∀ (c : K) (v : V), F (fr.La (upperSL2 c) v) = fr.La (upperSL2 c) (F v)) (c : K) :
    σ c = c := by
  obtain ⟨v, hv⟩ : ∃ v : V, v = fr.incl !![0, 0; 1, 0] := ⟨_, rfl⟩
  have hw0 : fr.La (upperSL2 1) v - v ≠ 0 := by
    intro h
    have h1 := congrArg (fun x => fr.coords x 0 0) h
    simp only [hv, map_sub, Frame.La_apply_incl, Frame.coords_incl, map_zero] at h1
    simp at h1
  have e1 := sub_eq_iff_eq_add'.mp (La_upperSL2_sub fr c v)
  have e2 := sub_eq_iff_eq_add'.mp (La_upperSL2_sub fr c (F v))
  have hFw : F (fr.La (upperSL2 1) v - v) = fr.La (upperSL2 1) (F v) - F v := by
    rw [map_sub, hc]
  have h1 := hc c v
  rw [e1, e2, map_add, hF, ← hFw, add_right_inj] at h1
  have h3 : (σ c - c) • F (fr.La (upperSL2 1) v - v) = 0 := by rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right
    fun h => hw0 ((map_eq_zero_iff F F.injective).mp h))

theorem exists_smul_incl_of_commute (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hL : ∀ A : SL(2, K), g * fr.La A = fr.La A * g)
    (hR : ∀ A : SL(2, K), g * fr.swap.La A = fr.swap.La A * g) :
    ∃ a : K, ∀ X, g (fr.incl X) = a • fr.incl X := by
  have hg : g * fr.La (-1) = fr.La (-1) * g := hL (-1)
  have hTB : ∀ (X : Matrix (Fin 2) (Fin 2) K) (B : SL(2, K)),
      fr.transport g (X * B) = fr.transport g X * B := by
    intro X B
    have hcomm := LinearEquiv.congr_fun (hR (Frame.sigmaSL B)) (fr.incl X)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, CFSG.LieType.HighestRoot.swap_La_incl,
      ← Frame.incl_transport h2 hg, ← Frame.incl_transport h2 hg,
      CFSG.LieType.HighestRoot.swap_La_incl, Frame.coe_sigmaSL, sigmaLin_sigmaLin] at hcomm
    have h := congrArg fr.coords hcomm
    rwa [Frame.coords_incl, Frame.coords_incl] at h
  have hTX := CFSG.LieType.HighestRoot.eq_mul_of_forall_specialLinear
    (T := fr.transport g) (A := fr.transport g 1)
    (fun B => by simpa only [Matrix.one_mul] using hTB 1 B)
  have hTA : ∀ A : SL(2, K), fr.transport g (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * fr.transport g 1 := by
    intro A
    have hcomm := LinearEquiv.congr_fun (hL A) (fr.incl 1)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply_incl,
      ← Frame.incl_transport h2 hg, ← Frame.incl_transport h2 hg, Frame.La_apply_incl,
      Matrix.mul_one] at hcomm
    have h := congrArg fr.coords hcomm
    rwa [Frame.coords_incl, Frame.coords_incl] at h
  have hcomm : ∀ A : SL(2, K), fr.transport g 1 * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * fr.transport g 1 := fun A => (hTX A).symm.trans (hTA A)
  have hU := hcomm (upperSL2 1)
  have hLo := hcomm (lowerSL2 1)
  rw [coe_upperSL2] at hU
  rw [coe_lowerSL2] at hLo
  have e1 := congrFun (congrFun hU 0) 0
  have e2 := congrFun (congrFun hU 0) 1
  have e3 := congrFun (congrFun hLo 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e1 e2 e3
  have hC : fr.transport g 1 = fr.transport g 1 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h10 : fr.transport g 1 1 0 = 0 := by linear_combination -e1
    have h01 : fr.transport g 1 0 1 = 0 := by linear_combination e3
    have h11 : fr.transport g 1 1 1 = fr.transport g 1 0 0 := by linear_combination -e2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]
  obtain ⟨a, ha⟩ : ∃ a : K, fr.transport g 1 = a • (1 : Matrix (Fin 2) (Fin 2) K) := ⟨_, hC⟩
  refine ⟨a, fun X => ?_⟩
  rw [← Frame.incl_transport h2 hg, hTX X, ha, Matrix.smul_mul, Matrix.one_mul, map_smul]

end Frame

section Seven

variable {K : Type} [Field K]

theorem oddVec_two_mem_perp (h2 : (2 : K) ≠ 0) (s : Bool) :
    oddVec 3 K 2 s ∈ (frame01 K).perp := by
  rw [(frame01 K).mem_perp_iff_fix h2]
  cases s
  · exact La_neg_one_apply_f2
  · exact La_neg_one_apply_e2

theorem oddZ_mem_perp (h2 : (2 : K) ≠ 0) : oddZ 3 K ∈ (frame01 K).perp :=
  ((frame01 K).mem_perp_iff_fix h2).mpr La_neg_one_apply_z

theorem eq_smul_oddZ_of_mem_perp (h2 : (2 : K) ≠ 0) {w : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hw : w ∈ (frame01 K).perp) (he : polar (quadOdd 3 K) (oddVec 3 K 2 true) w = 0)
    (hf : polar (quadOdd 3 K) (oddVec 3 K 2 false) w = 0) :
    w = w (.inr (.inr ())) • oddZ 3 K := by
  have hw' := eq_of_La_neg_one_apply_eq h2 (((frame01 K).mem_perp_iff_fix h2).mp hw)
  rw [polar_comm, oddVec_true, polar_quadOdd_single_inl] at he
  rw [polar_comm, oddVec_false, polar_quadOdd_single_inr_inl] at hf
  rw [he, hf, zero_smul, zero_smul, zero_add, zero_add] at hw'
  exact hw'

theorem exists_smul_perp_of_commute (h2 : (2 : K) ≠ 0)
    (M : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K))
    (hS : ∀ (s : Bool) (c : K) v,
      M (spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) v) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) (M v)) :
    ∃ l : K, ∀ w ∈ (frame01 K).perp, M w = l • w := by
  let P : HypPair (quadOdd 3 K) := ⟨oddVec 3 K 2 true, oddVec 3 K 2 false,
    quadOdd_oddVec 3 K 2 true, quadOdd_oddVec 3 K 2 false, by
      rw [polar_quadOdd_oddVec]
      simp⟩
  have hzP : oddZ 3 K ∈ P.perp := HypPair.mem_perp.mpr
    ⟨polar_quadOdd_oddVec_oddZ 3 K 2 true, polar_quadOdd_oddVec_oddZ 3 K 2 false⟩
  have hc1 : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  refine CFSG.LieType.HighestRoot.exists_smul_of_commute_eichler (U := (frame01 K).perp) P
    (oddVec_two_mem_perp h2 true) (oddVec_two_mem_perp h2 false) (oddZ_mem_perp h2) hzP
    (by rw [quadOdd_oddZ]; exact one_ne_zero) (neg_ne_zero.mpr one_ne_zero) hc1 M ?_
  intro u hu w hwU hwP a x
  obtain ⟨b, rfl⟩ : ∃ b : K, w = b • oddZ 3 K :=
    ⟨_, eq_smul_oddZ_of_mem_perp h2 hwU (HypPair.mem_perp.mp hwP).1 (HypPair.mem_perp.mp hwP).2⟩
  obtain ⟨s, rfl⟩ : ∃ s, u = oddVec 3 K 2 s := by
    rcases hu with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  have hE : ∀ y, y + polar (quadOdd 3 K) y (oddVec 3 K 2 s) • (a • b • oddZ 3 K) -
      polar (quadOdd 3 K) y (a • b • oddZ 3 K) • oddVec 3 K 2 s -
      (quadOdd 3 K (a • b • oddZ 3 K) * polar (quadOdd 3 K) y (oddVec 3 K 2 s)) •
        oddVec 3 K 2 s =
      spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd (a * b))) y := by
    intro y
    rw [OddFrame.spinAction_shortRoot]
    simp only [oddFrame_vec, oddFrame_z, polar_smul_right, QuadraticMap.map_smul, quadOdd_oddZ,
      smul_eq_mul, mul_one]
    module
  rw [hE, hE, hS]

theorem eq_smul_or_eq_smul_La_of_commute (h2 : (2 : K) ≠ 0) {σ : K ≃+* K}
    {F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hF : ∀ (c : K) v, F (c • v) = σ c • F v) {μ : K}
    (hQ : ∀ v, quadOdd 3 K (F v) = μ * σ (quadOdd 3 K v))
    (hL : ∀ (A : SL(2, K)) v, F ((frame01 K).La A v) = (frame01 K).La A (F v))
    (hR : ∀ (A : SL(2, K)) v, F ((frame01 K).swap.La A v) = (frame01 K).swap.La A (F v))
    (hS : ∀ (s : Bool) (c : K) v,
      F (spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) v) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) (F v)) :
    (∀ c, σ c = c) ∧ ∃ c : K, c ≠ 0 ∧
      ((∀ v, F v = c • v) ∨ ∀ v, F v = c • (frame01 K).La (-1) v) := by
  have hσ : ∀ c, σ c = c := eq_of_commute_La_upperSL2 (frame01 K) hF fun c v => hL _ v
  refine ⟨hσ, ?_⟩
  obtain ⟨Fl, hFl⟩ : ∃ Fl : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K),
      ∀ v, Fl v = F v := ⟨F.toLinearEquiv fun c v => by rw [hF, hσ], fun v => rfl⟩
  have hL' : ∀ A : SL(2, K), Fl * (frame01 K).La A = (frame01 K).La A * Fl := fun A =>
    LinearEquiv.ext fun v => by simp only [LinearEquiv.mul_apply, hFl]; exact hL A v
  have hR' : ∀ A : SL(2, K), Fl * (frame01 K).swap.La A = (frame01 K).swap.La A * Fl := fun A =>
    LinearEquiv.ext fun v => by simp only [LinearEquiv.mul_apply, hFl]; exact hR A v
  obtain ⟨a, ha⟩ := exists_smul_incl_of_commute (frame01 K) h2 hL' hR'
  obtain ⟨l, hl⟩ := exists_smul_perp_of_commute h2 (Fl : _ →ₗ[K] _) fun s c v => by
    simp only [LinearEquiv.coe_coe, hFl]
    exact hS s c v
  have ha' : ∀ X, F ((frame01 K).incl X) = a • (frame01 K).incl X := fun X => by
    rw [← hFl]
    exact ha X
  have hl' : ∀ w ∈ (frame01 K).perp, F w = l • w := fun w hw => by
    rw [← hFl]
    exact hl w hw
  have hQ' : ∀ v, quadOdd 3 K (F v) = μ * quadOdd 3 K v := fun v => by rw [hQ, hσ]
  have hμa : μ = a ^ 2 := by
    have h := hQ' ((frame01 K).incl 1)
    rw [ha', QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one, smul_eq_mul] at h
    linear_combination -h
  have hμl : μ = l ^ 2 := by
    have h := hQ' (oddZ 3 K)
    rw [hl' _ (oddZ_mem_perp h2), QuadraticMap.map_smul, quadOdd_oddZ, smul_eq_mul] at h
    linear_combination -h
  have hla : (l - a) * (l + a) = 0 := by linear_combination hμl.symm.trans hμa
  have ha0 : a ≠ 0 := by
    intro h0
    have h := ha' 1
    rw [h0, zero_smul] at h
    have h' := congrArg (frame01 K).coords ((map_eq_zero_iff F F.injective).mp h)
    rw [Frame.coords_incl, map_zero] at h'
    exact one_ne_zero h'
  have hdec : ∀ v, F v = a • (frame01 K).incl ((frame01 K).coords v) +
      l • (v - (frame01 K).incl ((frame01 K).coords v)) := by
    intro v
    have hr : v - (frame01 K).incl ((frame01 K).coords v) ∈ (frame01 K).perp := by
      rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    have hv : v = (frame01 K).incl ((frame01 K).coords v) +
        (v - (frame01 K).incl ((frame01 K).coords v)) := by abel
    conv_lhs => rw [hv]
    rw [map_add, ha', hl' _ hr]
  rcases mul_eq_zero.mp hla with h | h
  · refine ⟨a, ha0, Or.inl fun v => ?_⟩
    rw [hdec v, sub_eq_zero.mp h]
    module
  · refine ⟨-a, neg_ne_zero.mpr ha0, Or.inr fun v => ?_⟩
    rw [hdec v, eq_neg_of_add_eq_zero_left h, Frame.La_neg_one_apply]
    module

end Seven

end CFSG.ComponentClassification.HarrisLit.T1
