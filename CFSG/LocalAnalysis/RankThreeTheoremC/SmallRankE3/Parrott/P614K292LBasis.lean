module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292L

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292
open scoped Pointwise

variable {K : Type} [Field K]

section Bases

theorem colMat_mulVec_single (b : Fin 3 → Fin 3 → K) (i : Fin 3) (c : K) :
    colMat b *ᵥ Pi.single i c = c • b i := by
  ext r
  simp [colMat, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem mul_colMat (M : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → Fin 3 → K) :
    M * colMat b = colMat fun i => M *ᵥ b i := by
  ext r i
  rw [mul_colMat_apply]
  rfl

theorem ne_zero_of_isUnit_colMat {b : Fin 3 → Fin 3 → K} (hb : IsUnit (colMat b)) (i : Fin 3) :
    b i ≠ 0 := by
  intro h0
  have hd : IsUnit (colMat b).det := (Matrix.isUnit_iff_isUnit_det _).mp hb
  have h := congrArg (fun w => (colMat b)⁻¹ *ᵥ w) (colMat_mulVec_single b i 1)
  simp only [one_smul, h0, Matrix.mulVec_zero, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec] at h
  have := congrFun h i
  simp at this

theorem eq_of_forall_mulVec_eq {b : Fin 3 → Fin 3 → K} (hb : IsUnit (colMat b))
    {M N : Matrix (Fin 3) (Fin 3) K} (h : ∀ i, M *ᵥ b i = N *ᵥ b i) : M = N := by
  have h' : M * colMat b = N * colMat b := by
    rw [mul_colMat, mul_colMat]
    exact congrArg colMat (funext h)
  exact hb.mul_left_inj.mp h'

theorem isUnit_colMat_mulVec {b : Fin 3 → Fin 3 → K} (hb : IsUnit (colMat b))
    {M : Matrix (Fin 3) (Fin 3) K} (hM : IsUnit M) : IsUnit (colMat fun i => M *ᵥ b i) := by
  rw [← mul_colMat]
  exact hM.mul hb

theorem pow_mulVec_of_mulVec_eq {M : Matrix (Fin 3) (Fin 3) K} {u : Fin 3 → K} {c : K}
    (h : M *ᵥ u = c • u) (n : ℕ) : (M ^ n) *ᵥ u = c ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

theorem pow_three_eq_one_of_mulVec_eq {g : GL (Fin 3) K} (hg : g ^ 3 = 1) {u : Fin 3 → K}
    (hu : u ≠ 0) {c : K} (h : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u = c • u) : c ^ 3 = 1 := by
  have h3 := pow_mulVec_of_mulVec_eq h 3
  rw [← Units.val_pow_eq_pow_val, hg, Units.val_one, Matrix.one_mulVec] at h3
  by_contra hc
  apply hu
  have h0 : (c ^ 3 - 1) • u = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem isUnit_colMat_yFrame {y : GL (Fin 3) K} {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {v : Fin 3 → K} (hv : v ≠ 0) :
    IsUnit (colMat (yFrame y v)) := by
  rw [yFrame_eq]
  exact isUnit_colMat (linearIndependent_cyclic hℓ hy hv)

end Bases

section FrameGroups

theorem frameGroupOf_le_of_forall {n : ℕ} {b b' : Fin 3 → Fin 3 → K}
    (h : ∀ i, ∃ j, ∃ s : K, b' i = s • b j) : frameGroupOf n b ≤ frameGroupOf n b' := by
  rintro g ⟨hdet, hg⟩
  refine ⟨hdet, fun i => ?_⟩
  obtain ⟨j, s, hs⟩ := h i
  obtain ⟨c, hc, hgc⟩ := hg j
  exact ⟨c, hc, by rw [hs, Matrix.mulVec_smul, hgc, smul_comm]⟩

theorem mulVec_conj (a h : GL (Fin 3) K) (u : Fin 3 → K) :
    ((a * h * a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ u) =
      (a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
    inv_mul_cancel_right]

theorem det_conj_eq (a h : GL (Fin 3) K) :
    ((a * h * a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (h : Matrix (Fin 3) (Fin 3) K).det := by
  have h1 : (a : Matrix (Fin 3) (Fin 3) K).det * ((a⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (h : Matrix (Fin 3) (Fin 3) K).det * h1

theorem conj_smul_frameGroupOf_le (n : ℕ) (b : Fin 3 → Fin 3 → K) (a : GL (Fin 3) K) :
    MulAut.conj a • frameGroupOf n b ≤
      frameGroupOf n (fun i => (a : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by
  intro g hg
  obtain ⟨h, ⟨hdet, hh⟩, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hg
  refine ⟨?_, fun i => ?_⟩
  · change ((a * h * a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [det_conj_eq, hdet]
  · obtain ⟨c, hc, hhc⟩ := hh i
    refine ⟨c, hc, ?_⟩
    change ((a * h * a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) = _
    rw [mulVec_conj, hhc, Matrix.mulVec_smul]

theorem conj_smul_frameGroupOf (n : ℕ) (b : Fin 3 → Fin 3 → K) (a : GL (Fin 3) K) :
    MulAut.conj a • frameGroupOf n b =
      frameGroupOf n (fun i => (a : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by
  refine le_antisymm (conj_smul_frameGroupOf_le n b a) ?_
  rw [Subgroup.subset_pointwise_smul_iff, ← map_inv]
  refine (conj_smul_frameGroupOf_le n _ a⁻¹).trans (le_of_eq ?_)
  congr 1
  funext i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem threeFrame_smul (y : GL (Fin 3) K) (v : Fin 3 → K) {c : K} (hc : c ≠ 0) :
    threeFrame y (c • v) = threeFrame y v := by
  have h : ∀ i, yFrame y (c • v) i = c • yFrame y v i := fun i => by
    simp only [yFrame, Matrix.mulVec_smul]
  refine le_antisymm (frameGroupOf_le_of_forall fun i => ⟨i, c⁻¹, ?_⟩)
    (frameGroupOf_le_of_forall fun i => ⟨i, c, h i⟩)
  rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem threeFrame_mulVec_self {y : GL (Fin 3) K} {ℓ : K} (hℓ : ℓ ≠ 0)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) (v : Fin 3 → K) :
    threeFrame y ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = threeFrame y v := by
  set Y := (y : Matrix (Fin 3) (Fin 3) K) with hY
  have e0 : yFrame y (Y *ᵥ v) 0 = yFrame y v 1 := by
    simp [yFrame, hY]
  have e1 : yFrame y (Y *ᵥ v) 1 = yFrame y v 2 := by
    simp only [yFrame, Fin.val_one, Fin.val_two, pow_one, Matrix.mulVec_mulVec, hY, sq]
  have e2 : yFrame y (Y *ᵥ v) 2 = ℓ • yFrame y v 0 := by
    have h3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 2 * (y : Matrix (Fin 3) (Fin 3) K) = ℓ • 1 := by
      rw [← pow_succ]
      exact hy
    simp only [yFrame, Fin.val_two, Fin.val_zero, pow_zero, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, hY, h3, Matrix.smul_mulVec]
  refine le_antisymm (frameGroupOf_le_of_forall fun i => ?_)
    (frameGroupOf_le_of_forall fun i => ?_)
  · fin_cases i
    · exact ⟨2, ℓ⁻¹, by
        change yFrame y v 0 = ℓ⁻¹ • yFrame y (Y *ᵥ v) 2
        rw [e2, smul_smul, inv_mul_cancel₀ hℓ, one_smul]⟩
    · exact ⟨0, 1, by
        change yFrame y v 1 = (1 : K) • yFrame y (Y *ᵥ v) 0
        rw [e0, one_smul]⟩
    · exact ⟨1, 1, by
        change yFrame y v 2 = (1 : K) • yFrame y (Y *ᵥ v) 1
        rw [e1, one_smul]⟩
  · fin_cases i
    · exact ⟨1, 1, by
        change yFrame y (Y *ᵥ v) 0 = (1 : K) • yFrame y v 1
        rw [e0, one_smul]⟩
    · exact ⟨2, 1, by
        change yFrame y (Y *ᵥ v) 1 = (1 : K) • yFrame y v 2
        rw [e1, one_smul]⟩
    · exact ⟨0, ℓ, e2⟩

theorem conj_smul_threeFrame {y a : GL (Fin 3) K} (ha : a * y = y * a) (v : Fin 3 → K) :
    MulAut.conj a • threeFrame y v = threeFrame y ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
  have hm : (a : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
      (y : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ha, Units.val_mul]
  unfold threeFrame
  rw [conj_smul_frameGroupOf]
  congr 1
  funext i
  simp only [yFrame, Matrix.mulVec_mulVec, (Commute.pow_right hm (i : ℕ)).eq]

end FrameGroups

section Card

variable {π : Bool} {p f : ℕ}

theorem frameGroupOf_three_single :
    frameGroupOf 3 (fun i => (Pi.single i 1 : Fin 3 → K)) =
      ((rootsOfUnity 3 K).prod (rootsOfUnity 3 K)).map torusHom := by
  ext g
  constructor
  · rintro ⟨hdet, hg⟩
    choose c hc hgc using hg
    have hcol : ∀ r i, (g : Matrix (Fin 3) (Fin 3) K) r i = if r = i then c i else 0 := by
      intro r i
      have h := congrFun (hgc i) r
      rw [Matrix.mulVec_single_one] at h
      simpa [Pi.single_apply] using h
    have hgd : (g : Matrix (Fin 3) (Fin 3) K) = diagonal c := by
      ext r i
      rw [hcol, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · rfl
    have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
      have := hc i
      rw [h0, zero_pow (by norm_num)] at this
      exact zero_ne_one this
    have hprod : c 0 * c 1 * c 2 = 1 := by
      rw [← hdet, hgd, det_diagonal, Fin.prod_univ_three]
    refine ⟨(Units.mk0 (c 0) (hc0 0), Units.mk0 (c 1) (hc0 1)), ⟨?_, ?_⟩, ?_⟩
    · change Units.mk0 (c 0) (hc0 0) ∈ rootsOfUnity 3 K
      rw [mem_rootsOfUnity]
      exact Units.ext (by simp [hc 0])
    · change Units.mk0 (c 1) (hc0 1) ∈ rootsOfUnity 3 K
      rw [mem_rootsOfUnity]
      exact Units.ext (by simp [hc 1])
    · apply Units.ext
      rw [coe_torusHom, hgd]
      congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · have h2 : c 2 = (c 0 * c 1)⁻¹ := eq_inv_of_mul_eq_one_right hprod
        simp [h2]
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have ha3 : (a : K) ^ 3 = 1 := by
      have := congrArg Units.val ((mem_rootsOfUnity _ _).mp ha)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have hb3 : (b : K) ^ 3 = 1 := by
      have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hb)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have hd3 : ∀ i, (![(a : K), b, ((a * b)⁻¹ : Kˣ)] : Fin 3 → K) i ^ 3 = 1 := by
      intro i
      fin_cases i
      · exact ha3
      · exact hb3
      · change (((a * b)⁻¹ : Kˣ) : K) ^ 3 = 1
        rw [Units.val_inv_eq_inv_val, Units.val_mul, inv_pow, mul_pow, ha3, hb3, mul_one,
          inv_one]
    refine ⟨?_, fun i => ⟨(![(a : K), b, ((a * b)⁻¹ : Kˣ)] : Fin 3 → K) i, hd3 i, ?_⟩⟩
    · change ((torusHom (a, b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
      rw [coe_torusHom, det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · change ((torusHom (a, b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        Pi.single i 1 = (![(a : K), b, ((a * b)⁻¹ : Kˣ)] : Fin 3 → K) i • Pi.single i 1
      rw [coe_torusHom, Matrix.diagonal_mulVec_single, mul_one]
      ext r
      by_cases h : r = i
      · subst h
        simp
      · simp [Pi.single_apply, h]

theorem card_frameGroupOf_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {b : Fin 3 → Fin 3 → K} (hb : IsUnit (colMat b)) : Nat.card (frameGroupOf 3 b) = 9 := by
  have hconj : frameGroupOf 3 b =
      MulAut.conj hb.unit • frameGroupOf 3 (fun i => (Pi.single i 1 : Fin 3 → K)) := by
    rw [conj_smul_frameGroupOf]
    congr 1
    funext i
    rw [IsUnit.unit_spec, colMat_mulVec_single, one_smul]
  rw [hconj, ← Nat.card_congr (Subgroup.equivSMul _ _).toEquiv, frameGroupOf_three_single,
    Subgroup.card_map_of_injective torusHom_injective, card_mu3_prod hK hq]

end Card

section Step0

variable {p f : ℕ}

theorem threeFrame_mem_frameCands (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree true (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0) :
    threeFrame y v ∈ frameCands true (p ^ f) y := by
  obtain ⟨ℓ, hy, hℓ⟩ := hT.not_cube hK hq
  have hb := isUnit_colMat_yFrame hℓ hy hv
  have hb0 := ne_zero_of_isUnit_colMat hb
  refine ⟨fun g hg => (mem_slPi_true _).2 hg.1, ⟨?_, ?_⟩, card_frameGroupOf_three hK hq hb,
    ?_, ?_⟩
  · refine IsMulCommutative.of_comm fun g h => Subtype.ext (Units.ext ?_)
    obtain ⟨-, hg⟩ := g.2
    obtain ⟨-, hh⟩ := h.2
    refine eq_of_forall_mulVec_eq hb fun i => ?_
    obtain ⟨c, -, hgc⟩ := hg i
    obtain ⟨d, -, hhd⟩ := hh i
    simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hgc, hhd,
      Matrix.mulVec_smul, smul_smul, mul_comm c d]
  · intro g hg
    apply Units.ext
    refine eq_of_forall_mulVec_eq hb fun i => ?_
    obtain ⟨c, hc, hgc⟩ := hg.2 i
    rw [Units.val_pow_eq_pow_val, pow_mulVec_of_mulVec_eq hgc, hc, one_smul, Units.val_one,
      Matrix.one_mulVec]
  · rintro z ⟨⟨c, rfl⟩, hz⟩
    have hdet := (mem_slPi_true _).1 hz
    refine ⟨hdet, fun i => ⟨c, ?_, ?_⟩⟩
    · rw [det_scalar] at hdet
      exact hdet
    · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        Matrix.smul_mulVec, Matrix.one_mulVec]
  · intro g hg
    have h := conj_smul_threeFrame (y := y) (a := y) rfl v
    rw [threeFrame_mulVec_self ℓ.ne_zero hy] at h
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul g (MulAut.conj y) _ hg

end Step0

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292L
