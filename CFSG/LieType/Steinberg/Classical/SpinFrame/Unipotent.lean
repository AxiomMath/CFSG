module

public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic
public import CFSG.LieType.Steinberg.GradedUnipotent

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinFrame

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.Graded QuadraticMap Matrix

section Level

variable {n : ℕ}

theorem exists_levelFun (T : (Fin n → ℤ) →+ (Fin n → ℤ)) (hT : Function.Injective T) (N : ℤ)
    (hN : ∀ a : Fin n, ∃ v, T v = N • Pi.single a 1) (f : (Fin n → ℤ) →+ ℤ) :
    ∃ μ : (Fin n → ℤ) →+ ℤ, ∀ v, μ (T v) = N * f v := by
  choose w hw using hN
  let μ : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun e => ∑ a, e a * f (w a)
      map_zero' := by simp
      map_add' := fun e e' => by simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨μ, fun v => ?_⟩
  have hsum : ∑ a, T v a • w a = N • v := by
    apply hT
    rw [map_sum, map_zsmul]
    simp only [map_zsmul, hw, smul_comm (T v _) N]
    rw [← Finset.smul_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single (T v)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  change ∑ a, T v a * f (w a) = N * f v
  have := congrArg f hsum
  rw [map_sum, map_zsmul] at this
  simp only [map_zsmul, smul_eq_mul] at this
  exact this

end Level

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {Q : QuadraticForm K (σ → K)} {n : ℕ} (F : HypFrame Q n) (idx : Fin n → Bool → σ)

structure IsCoordFrame : Prop where
  vec_eq : ∀ m r, F.vec m r = Pi.single (idx m r) 1
  polar_eq : ∀ (v : σ → K) m r, polar Q v (F.vec m r) = v (idx m (!r))

variable (K) in
@[expose] def longMat (i j : Fin n) (s t : Bool) : Matrix σ σ K :=
  Matrix.single (idx i s) (idx j (!t)) 1 - Matrix.single (idx j t) (idx i (!s)) 1

variable {F idx}

theorem spinMatrix_apply (g : spinGroup Q) (a b : σ) :
    (spinMatrix Q g : Matrix σ σ K) a b = spinAction Q g (Pi.single b 1) a := by
  rw [← spinMatrix_mulVec, Matrix.mulVec_single_one, Matrix.col_apply]

theorem coe_spinMatrix_longRoot (hF : IsCoordFrame F idx) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (c : K) :
    (spinMatrix Q (F.longRoot hij s t (.ofAdd c)) : Matrix σ σ K) =
      1 + c • longMat K idx i j s t := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [spinMatrix_mulVec, F.spinAction_longRoot, hF.polar_eq, hF.polar_eq, hF.vec_eq, hF.vec_eq,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, longMat, Matrix.sub_mulVec,
    Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  module

variable (F) in
@[expose] def rootMat (e : Fin n → ℤ) : Matrix σ σ K :=
  (spinMatrix Q (rootElt F e 1) : Matrix σ σ K) - 1

theorem rootMat_eq (hF : IsCoordFrame F idx) {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    {s t : Bool} (he : e = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    rootMat F e = (repSign i j s t : K) • longMat K idx i j s t := by
  rw [rootMat, rootElt_eq F hij he, coe_spinMatrix_longRoot hF, mul_one, add_sub_cancel_left]

theorem rootMat_of_not {e : Fin n → ℤ} (he : ¬IsLong e) : rootMat F e = (0 : Matrix σ σ K) := by
  rw [rootMat, rootElt_of_not F he, map_one, Units.val_one, sub_self]

theorem coe_spinMatrix_rootElt (hF : IsCoordFrame F idx) (e : Fin n → ℤ) (c : K) :
    (spinMatrix Q (rootElt F e c) : Matrix σ σ K) = 1 + c • rootMat F e := by
  by_cases he : IsLong e
  · obtain ⟨i, j, hij, s, t, he⟩ := he
    rw [rootMat_eq hF hij he, rootElt_eq F hij he, coe_spinMatrix_longRoot hF, smul_smul,
      mul_comm]
  · rw [rootMat_of_not he, rootElt_of_not F he, smul_zero, add_zero, map_one, Units.val_one]

omit [Fintype σ] in
theorem idx_ne (hF : IsCoordFrame F idx) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    idx i s ≠ idx j t := by
  intro h
  have h1 := F.polar_vec_of_ne hij s (!t)
  rw [hF.polar_eq, Bool.not_not, hF.vec_eq, h, Pi.single_eq_same] at h1
  exact one_ne_zero h1

theorem rootMat_ne_zero (hF : IsCoordFrame F idx) {e : Fin n → ℤ} (he : IsLong e) :
    rootMat F e ≠ (0 : Matrix σ σ K) := by
  obtain ⟨i, j, hij, s, t, he⟩ := he
  rw [rootMat_eq hF hij he]
  intro h
  have h' := congrFun (congrFun h (idx i s)) (idx j (!t))
  simp only [longMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, and_self,
    ite_true, Matrix.zero_apply, smul_eq_mul] at h'
  rw [ite_eq_right (fun h => idx_ne hF hij s t h.1.symm), sub_zero, mul_one] at h'
  exact intCast_ne_zero_of_sq (repSign_eq_one_or_eq_neg_one i j s t) h'

theorem shifts_rootMat (hF : IsCoordFrame F idx) (wt : σ → Fin n → ℤ)
    (hwt : ∀ m r, wt (idx m r) = Pi.single m (boolSign r)) (e : Fin n → ℤ) :
    Shifts wt (rootMat F e) e := by
  by_cases he : IsLong e
  · obtain ⟨i, j, hij, s, t, he⟩ := he
    intro a b hab
    rw [rootMat_eq hF hij he] at hab
    simp only [longMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
      smul_eq_mul] at hab
    by_cases h1 : idx i s = a ∧ idx j (!t) = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hwt, hwt, he, boolSign_not, Pi.single_neg, sub_neg_eq_add]
    · by_cases h2 : idx j t = a ∧ idx i (!s) = b
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hwt, hwt, he, boolSign_not, Pi.single_neg, sub_neg_eq_add, add_comm]
      · rw [ite_eq_right h1, ite_eq_right h2, sub_self, mul_zero] at hab
        exact absurd rfl hab
  · rw [rootMat_of_not he]
    intro a b hab
    exact absurd rfl hab

theorem coe_spinMatrix_rootElt_eq_elt (hF : IsCoordFrame F idx) (e : Fin n → ℤ) (c : K) :
    (spinMatrix Q (rootElt F e c) : Matrix σ σ K) =
      Graded.elt 1 (fun k => if k = 1 then rootMat F e else 0) c := by
  rw [coe_spinMatrix_rootElt hF, Graded.elt, Finset.Icc_self, Finset.sum_singleton,
    ite_eq_left rfl, pow_one]

theorem eq_of_prod_rootElt_eq (hF : IsCoordFrame F idx) (wt : σ → Fin n → ℤ)
    (hwt : ∀ m r, wt (idx m r) = Pi.single m (boolSign r)) (μ : (Fin n → ℤ) →+ ℤ) {Λ : Type*}
    (root : Λ → Fin n → ℤ) (L : List Λ) (hL : L.Nodup) (hlong : ∀ γ ∈ L, IsLong (root γ))
    (hinj : ∀ γ ∈ L, ∀ δ ∈ L, root γ = root δ → γ = δ) (hpos : ∀ γ ∈ L, 0 < μ (root γ))
    (hsort : L.Pairwise fun γ δ => μ (root γ) ≤ μ (root δ)) (c d : Λ → K)
    (h : (L.map fun γ => rootElt F (root γ) (c γ)).prod =
      (L.map fun γ => rootElt F (root γ) (d γ)).prod) :
    ∀ γ ∈ L, c γ = d γ := by
  set D : Λ → ℕ → Matrix σ σ K := fun γ k => if k = 1 then rootMat F (root γ) else 0
  have hmat : ∀ e : Λ → K, ((spinMatrix Q (L.map fun γ => rootElt F (root γ) (e γ)).prod :
      GL σ K) : Matrix σ σ K) = (L.map fun γ => Graded.elt 1 (D γ) (e γ)).prod := by
    intro e
    rw [map_list_prod, ← Units.coeHom_apply, map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun γ _ =>
      coe_spinMatrix_rootElt_eq_elt hF (root γ) (e γ))
  refine Graded.eq_of_prod_eq (wt := wt) le_rfl root D μ (fun γ k hk => ?_) L hL hinj hpos
    (fun γ hγ => ?_) hsort (fun γ _ e => ?_) c d ?_
  · by_cases hk1 : k = 1
    · subst hk1
      simp only [D, ite_eq_left rfl, one_nsmul]
      exact shifts_rootMat hF wt hwt (root γ)
    · simp only [D, ite_eq_right hk1]
      intro a b hab
      exact absurd rfl hab
  · simp only [D, ite_eq_left rfl]
    exact rootMat_ne_zero hF (hlong γ hγ)
  · rw [← coe_spinMatrix_rootElt_eq_elt hF]
    exact Units.isUnit _
  · rw [← hmat, ← hmat, h]

end CFSG.LieType.Steinberg.SpinFrame
