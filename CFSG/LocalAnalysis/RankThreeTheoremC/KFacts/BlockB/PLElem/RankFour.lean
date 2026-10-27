module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven

theorem four_le_pRank_four_of_rotGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {e : Fin 4 ⊕ Fin 4 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have hne : ∀ a b : Fin 4 ⊕ Fin 4, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  have hc : ∀ k l : Fin 4, k ≠ l →
      Commute (rotGL (K := K) (e (.inl k)) (e (.inr k))) (rotGL (e (.inl l)) (e (.inr l))) :=
    fun k l hkl => rotGL_commute (hne _ _ (by simpa using hkl)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simpa using hkl))
  refine CFSG.HardMathSupport.Timmesfeld.DFour.four_le_pRank_statedProj (hH 0) (hH 1) (hH 2)
    (hH 3) (rotGL_pow_three _ _) (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    (rotGL_pow_three _ _) (hc 0 1 (by decide)) (hc 0 2 (by decide)) (hc 1 2 (by decide))
    (hc 0 3 (by decide)) (hc 1 3 (by decide)) (hc 2 3 (by decide))
    (fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n _ hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc)
    (fun n m _ hc => mul_scalar_ne (hne _ _ (by decide)) ?_ (rotMatrix_mulVec_left _ _) hc)
    (fun n m l _ hc => mul_scalar_ne (hne _ _ (by decide)) ?_ (rotMatrix_mulVec_left _ _) hc)
  · rw [Units.val_mul, ← mulVec_mulVec,
      rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m,
      rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n]
  · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
      rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) l,
      rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m,
      rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n]

theorem psl_four_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 8 ≤ n) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  four_le_pRank_four_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem psp_four_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
  four_le_pRank_four_of_rotGL ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)

section Orthogonal

open CFSG.SectionRank.ClassicalEven.OrthRot

variable {ι : Type} {K : Type} [Field K]

theorem four_le_pRank_of_planes [Fintype ι] [DecidableEq ι] [Finite K] [CharP K 2]
    {Q : (ι → K) → K} {P₀ P₁ P₂ P₃ : Plane Q} (h₀₁ : P₀.Orth P₁) (h₀₂ : P₀.Orth P₂)
    (h₀₃ : P₀.Orth P₃) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  refine CFSG.HardMathSupport.Timmesfeld.DFour.four_le_pRank_statedProj P₀.rot_mem P₁.rot_mem
    P₂.rot_mem P₃.rot_mem P₀.rot_pow_three P₁.rot_pow_three P₂.rot_pow_three P₃.rot_pow_three
    (Plane.rot_commute h₀₁) (Plane.rot_commute h₀₂) (Plane.rot_commute h₁₂)
    (Plane.rot_commute h₀₃) (Plane.rot_commute h₁₃) (Plane.rot_commute h₂₃)
    (fun hc => ?_) (fun m c hc h => ?_) (fun m k c hc h => ?_) (fun m k l c hc h => ?_)
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    exact P₀.b_ne_smul_a u (P₀.rot_a.symm.trans (hu P₀.a))
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₁.b_ne_smul_a u ?_
    rw [← P₁.rot_a, ← h, mul_mulVec, hu, mulVec_smul,
      pow_mulVec_of_fix (P₀.rot_fix h₀₁.f_a h₀₁.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₂.b_ne_smul_a u ?_
    rw [← P₂.rot_a, ← h]
    simp only [mul_mulVec, hu, mulVec_smul, pow_mulVec_of_fix (P₁.rot_fix h₁₂.f_a h₁₂.g_a),
      pow_mulVec_of_fix (P₀.rot_fix h₀₂.f_a h₀₂.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₃.b_ne_smul_a u ?_
    rw [← P₃.rot_a, ← h]
    simp only [mul_mulVec, hu, mulVec_smul, pow_mulVec_of_fix (P₂.rot_fix h₂₃.f_a h₂₃.g_a),
      pow_mulVec_of_fix (P₁.rot_fix h₁₃.f_a h₁₃.g_a),
      pow_mulVec_of_fix (P₀.rot_fix h₀₃.f_a h₀₃.g_a)]

variable [DecidableEq ι]

structure Frame4 (Q : (ι → K) → K) where
  X : Fin 4 → ι
  Y : Fin 4 → ι
  injX : Function.Injective X
  injY : Function.Injective Y
  X_ne_Y : ∀ i j, X i ≠ Y j
  isPolar_X : ∀ i, IsPolar Q (Pi.single (X i) 1) (LinearMap.proj (Y i)) 0
  isPolar_Y : ∀ i, IsPolar Q (Pi.single (Y i) 1) (LinearMap.proj (X i)) 0

namespace Frame4

variable {Q : (ι → K) → K} (F : Frame4 Q)

theorem Y_ne_X (i j : Fin 4) : F.Y j ≠ F.X i := (F.X_ne_Y i j).symm

theorem polar_X {u : ι → K} {φ : (ι → K) →ₗ[K] K} {q : K} (hu : IsPolar Q u φ q) (j : Fin 4) :
    φ (Pi.single (F.X j) 1) = u (F.Y j) :=
  ((F.isPolar_X j).symm hu).symm

def hyp (i : Fin 4) : ι → K := Pi.single (F.X i) 1 + Pi.single (F.Y i) 1

def hypF (i : Fin 4) : (ι → K) →ₗ[K] K :=
  (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + LinearMap.proj (F.X i)

theorem isPolar_hyp (i : Fin 4) : IsPolar Q (F.hyp i) (F.hypF i) 1 :=
  (F.isPolar_X i).add (F.isPolar_Y i) (by simp)

theorem hyp_Y {i j : Fin 4} (hij : i ≠ j) : F.hyp j (F.Y i) = 0 := by
  simp [hyp, F.injY.eq_iff, F.Y_ne_X, Ne.symm hij]

def plane (i j : Fin 4) (hij : i ≠ j) : Plane Q where
  a := F.hyp i
  b := Pi.single (F.X i) 1 + F.hyp j
  f := F.hypF i
  g := (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + F.hypF j
  isPolar_a := F.isPolar_hyp i
  isPolar_b := (F.isPolar_X i).add (F.isPolar_hyp j)
    (by rw [F.polar_X (F.isPolar_hyp j), F.hyp_Y hij, zero_add, add_zero])
  f_b := by simp [hypF, hyp, F.injX.eq_iff, F.injY.eq_iff, F.Y_ne_X, F.X_ne_Y, hij, Ne.symm hij]

theorem plane_orth {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) : (F.plane i j hij).Orth (F.plane k l hkl) where
  f_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hik,
    Ne.symm hik]
  f_b := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hik, hil,
    Ne.symm hik, Ne.symm hil]
  g_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hik, hjk,
    Ne.symm hik, Ne.symm hjk]
  g_b := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hik, hil,
    hjk, hjl, Ne.symm hik, Ne.symm hil, Ne.symm hjk, Ne.symm hjl]

variable [CharP K 2]

theorem plane_orth_swap {i j : Fin 4} (hij : i ≠ j) :
    (F.plane i j hij).Orth (F.plane j i (Ne.symm hij)) where
  f_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij,
    Ne.symm hij]
  f_b := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij,
    Ne.symm hij, CharTwo.add_self_eq_zero]
  g_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij,
    Ne.symm hij, CharTwo.add_self_eq_zero]
  g_b := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X, hij,
    Ne.symm hij, CharTwo.add_self_eq_zero]

include F in
theorem four_le_pRank [Fintype ι] [Finite K] :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) :=
  four_le_pRank_of_planes (P₀ := F.plane 0 1 (by decide)) (P₁ := F.plane 1 0 (by decide))
    (P₂ := F.plane 2 3 (by decide)) (P₃ := F.plane 3 2 (by decide))
    (F.plane_orth_swap (by decide))
    (F.plane_orth _ _ (by decide) (by decide) (by decide) (by decide))
    (F.plane_orth _ _ (by decide) (by decide) (by decide) (by decide))
    (F.plane_orth _ _ (by decide) (by decide) (by decide) (by decide))
    (F.plane_orth _ _ (by decide) (by decide) (by decide) (by decide))
    (F.plane_orth_swap (by decide))

end Frame4

def plusFrame4 {n : ℕ} (hn : 4 ≤ n) : Frame4 (StatedQuadPlus n K) where
  X i := Sum.inl (Fin.castLE hn i)
  Y i := Sum.inr (Fin.castLE hn i)
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inr_injective h)
  X_ne_Y _ _ := Sum.inl_ne_inr
  isPolar_X _ := isPolar_plus_inl _
  isPolar_Y _ := isPolar_plus_inr _

def minusFrame4 {n : ℕ} (hn : 5 ≤ n) (b c : K) : Frame4 (StatedQuadMinus n K b c) where
  X i := Sum.inl (Fin.castLE (by omega) i)
  Y i := Sum.inr (Sum.inl (Fin.castLE (by omega) i))
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inl_injective (Sum.inr_injective h))
  X_ne_Y _ _ := Sum.inl_ne_inr
  isPolar_X _ := isPolar_minus_inl b c _
  isPolar_Y _ := isPolar_minus_inr b c _

end Orthogonal

theorem omegaPlus_four_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  (plusFrame4 hn).four_le_pRank

theorem omegaMinus_four_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 5 ≤ n) (b c : K) :
    4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
  (minusFrame4 hn b c).four_le_pRank

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem
