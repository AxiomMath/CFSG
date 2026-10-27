module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidModule
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

section Frame

variable {K : Type} [Field K] {k : ℕ}

@[expose] def zIdx (j : Fin k) : Fin (2 + k) :=
  if hj : (j : ℕ) < 2 then finSumFinEquiv (.inl ⟨j, hj⟩) else finSumFinEquiv (.inr j)

theorem zIdx_injective : Function.Injective (zIdx (k := k)) := by
  intro j l hjl
  unfold zIdx at hjl
  split_ifs at hjl with hj hl hl
  · exact Fin.ext (Fin.mk.inj (Sum.inl_injective (finSumFinEquiv.injective hjl)))
  · exact absurd (finSumFinEquiv.injective hjl) Sum.inl_ne_inr
  · exact absurd (finSumFinEquiv.injective hjl) Sum.inr_ne_inl
  · exact Sum.inr_injective (finSumFinEquiv.injective hjl)

theorem zIdx_ne_inr (j : Fin k) {i : Fin k} (hi : (i : ℕ) < 2) :
    zIdx j ≠ finSumFinEquiv (.inr i) := by
  unfold zIdx
  split_ifs with hj
  · exact finSumFinEquiv.injective.ne Sum.inl_ne_inr
  · intro h1
    have h2 := Sum.inr_injective (finSumFinEquiv.injective h1)
    subst h2
    omega

theorem zIdx_of_two_le {j : Fin k} (hj : 2 ≤ (j : ℕ)) : zIdx j = finSumFinEquiv (.inr j) := by
  unfold zIdx
  rw [dite_eq_right (by omega)]

variable (hk : 2 ≤ k)

abbrev ix₀ : Fin (2 + k) := finSumFinEquiv (.inr ⟨0, by omega⟩)

abbrev ix₁ : Fin (2 + k) := finSumFinEquiv (.inr ⟨1, by omega⟩)

theorem ix₀_ne_ix₁ : ix₀ hk ≠ ix₁ hk := by
  simp [Fin.ext_iff]

theorem uv₀_eq : uv₀ (K := K) hk = Pi.single (ix₀ hk) 1 + Pi.single (ix₁ hk) 1 := rfl

@[expose] def uf₀ (s : K) : Fin (2 + k) → K :=
  s • Pi.single (ix₀ hk) 1 + (s + 1) • Pi.single (ix₁ hk) 1

@[expose] def uFrame (s : K) : Matrix (Fin (2 * 1 + k)) (HypIndex 1 k) K :=
  Matrix.of fun i a => match a with
    | .inl _ => uv₀ hk i
    | .inr (.inl j) => (Pi.single (zIdx j) (1 : K) : Fin (2 + k) → K) i
    | .inr (.inr _) => uf₀ hk s i

theorem uFrame_mulVec_hE (s : K) :
    uFrame hk s *ᵥ (Pi.single hE 1 : HypIndex 1 k → K) = uv₀ hk := by
  rw [mulVec_single_one]
  rfl

theorem uFrame_mulVec_hF (s : K) :
    uFrame hk s *ᵥ (Pi.single hF 1 : HypIndex 1 k → K) = uf₀ hk s := by
  rw [mulVec_single_one]
  rfl

theorem uFrame_mulVec_z (s : K) (j : Fin k) :
    uFrame hk s *ᵥ (Pi.single (.inr (.inl j)) 1 : HypIndex 1 k → K) =
      Pi.single (zIdx j) 1 := by
  rw [mulVec_single_one]
  rfl

end Frame

section Transport

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} (h : UnitaryFieldData 2 f K) (hk : 2 ≤ k)

omit [CharP K 2] in
theorem gram_apply_eq_hform {ι κ : Type} [Fintype ι] (σ : K →+* K) (R : Matrix ι κ K)
    (a b : κ) : ((R.map σ)ᵀ * R) a b = hform σ (fun i => R i a) (fun i => R i b) :=
  rfl

omit [CharP K 2] in
theorem single_ix_zIdx (j : Fin k) {i : Fin k} (hi : (i : ℕ) < 2) :
    (Pi.single (zIdx j) (1 : K) : Fin (2 + k) → K) (finSumFinEquiv (.inr i)) = 0 :=
  Pi.single_eq_of_ne (zIdx_ne_inr j hi).symm _

omit [CharP K 2] in
theorem uv₀_ix₀ : uv₀ (K := K) hk (ix₀ hk) = 1 := by
  rw [uv₀_eq, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (ix₀_ne_ix₁ hk), add_zero]

omit [CharP K 2] in
theorem uf₀_ix₀ (s : K) : uf₀ hk s (ix₀ hk) = s := by
  rw [uf₀, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (ix₀_ne_ix₁ hk), smul_zero, add_zero, smul_eq_mul, mul_one]

omit [CharP K 2] in
theorem uf₀_ix₁ (s : K) : uf₀ hk s (ix₁ hk) = s + 1 := by
  rw [uf₀, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (ix₀_ne_ix₁ hk).symm, smul_zero, zero_add, smul_eq_mul, mul_one]

theorem hform_uv₀_uf₀ (σ : K →+* K) (s : K) : hform σ (uv₀ hk) (uf₀ hk s) = 1 := by
  rw [uv₀_eq, hform_add_left, hform_single_one_left, hform_single_one_left, uf₀_ix₀, uf₀_ix₁,
    ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem hform_uf₀_uv₀ (s : K) : hform h.bar (uf₀ hk s) (uv₀ hk) = 1 := by
  rw [hform_comm h.bar_bar, hform_uv₀_uf₀, map_one]

theorem hform_uf₀_uf₀ {s : K} (hs : s + h.bar s = 1) : hform h.bar (uf₀ hk s) (uf₀ hk s) = 0 := by
  rw [uf₀, hform_add_left, hform_smul_left, hform_smul_left, hform_single_one_left,
    hform_single_one_left, ← uf₀, uf₀_ix₀, uf₀_ix₁, map_add, map_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (h.bar s * s + 1) * h2 + hs

omit [CharP K 2] in
theorem hform_uv₀_zIdx (σ : K →+* K) (l : Fin k) :
    hform σ (uv₀ hk) (Pi.single (zIdx l) 1) = 0 := by
  rw [uv₀_eq, hform_add_left, hform_single_one_left, hform_single_one_left,
    single_ix_zIdx l (by simp), single_ix_zIdx l (by simp), add_zero]

omit [CharP K 2] in
theorem hform_uf₀_zIdx (σ : K →+* K) (s : K) (l : Fin k) :
    hform σ (uf₀ hk s) (Pi.single (zIdx l) 1) = 0 := by
  rw [uf₀, hform_add_left, hform_smul_left, hform_smul_left, hform_single_one_left,
    hform_single_one_left, single_ix_zIdx l (by simp), single_ix_zIdx l (by simp), mul_zero,
    mul_zero, add_zero]

omit [CharP K 2] in
theorem hform_zIdx_zIdx (σ : K →+* K) (j l : Fin k) :
    hform σ (Pi.single (zIdx j) 1) (Pi.single (zIdx l) (1 : K)) = if j = l then 1 else 0 := by
  rw [hform_single_one_left]
  simp only [Pi.single_apply, zIdx_injective.eq_iff]

theorem isHypTransport_uFrame {s : K} (hs : s + h.bar s = 1) :
    IsHypTransport h (uFrame hk s) := by
  ext a b
  rw [gram_apply_eq_hform]
  rcases a with a | j | a <;> rcases b with b | l | b
  · rw [Fin.eq_zero a, Fin.eq_zero b, hypGram_inl_inl]
    exact hform_uv₀ h.bar hk
  · rw [hypGram_inl_inr_inl]
    exact hform_uv₀_zIdx hk h.bar l
  · rw [Fin.eq_zero a, Fin.eq_zero b, hypGram_inl_inr_inr, ite_eq_left rfl]
    exact hform_uv₀_uf₀ hk h.bar s
  · rw [hypGram_inr_inl_inl, hform_comm h.bar_bar]
    change h.bar (hform h.bar (uv₀ hk) (Pi.single (zIdx j) 1)) = 0
    rw [hform_uv₀_zIdx, map_zero]
  · rw [hypGram_inr_inl_inr_inl]
    exact hform_zIdx_zIdx h.bar j l
  · rw [hypGram_inr_inl_inr_inr, hform_comm h.bar_bar]
    change h.bar (hform h.bar (uf₀ hk s) (Pi.single (zIdx j) 1)) = 0
    rw [hform_uf₀_zIdx, map_zero]
  · rw [Fin.eq_zero a, Fin.eq_zero b, hypGram_inr_inr_inl, ite_eq_left rfl]
    exact hform_uf₀_uv₀ h hk s
  · rw [hypGram_inr_inr_inr_inl]
    exact hform_uf₀_zIdx hk h.bar s l
  · rw [Fin.eq_zero a, Fin.eq_zero b, hypGram_inr_inr_inr_inr]
    exact hform_uf₀_uf₀ h hk hs

end Transport

section Std

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} (h : UnitaryFieldData 2 f K)

omit [CharP K 2] in
theorem hypTransport_mulVec {R : Matrix (Fin (2 * 1 + k)) (HypIndex 1 k) K}
    (hR : IsHypTransport h R) (g : hypSU h 1 k) (v : HypIndex 1 k → K) :
    ((hypTransport h hR g : StatedSU (2 * 1 + k) (2 ^ f) K) : GL (Fin (2 * 1 + k)) K).val *ᵥ
      (R *ᵥ v) = R *ᵥ (((g : GL (HypIndex 1 k) K) :
        Matrix (HypIndex 1 k) (HypIndex 1 k) K) *ᵥ v) := by
  rw [coe_hypTransport, mulVec_mulVec, Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one,
    mulVec_mulVec]

omit [CharP K 2] in
theorem mulVec_eq_iff_hypTransport {R : Matrix (Fin (2 * 1 + k)) (HypIndex 1 k) K}
    (hR : IsHypTransport h R) (g : hypSU h 1 k) (v : HypIndex 1 k → K) :
    ((g : GL (HypIndex 1 k) K) : Matrix (HypIndex 1 k) (HypIndex 1 k) K) *ᵥ v = v ↔
      ((hypTransport h hR g : StatedSU (2 * 1 + k) (2 ^ f) K) : GL (Fin (2 * 1 + k)) K).val *ᵥ
        (R *ᵥ v) = R *ᵥ v := by
  rw [hypTransport_mulVec h hR]
  constructor
  · intro hv
    rw [hv]
  · intro hv
    have key : ∀ x : HypIndex 1 k → K, transportInv h R *ᵥ (R *ᵥ x) = x := fun x => by
      rw [mulVec_mulVec, transportInv_mul hR, one_mulVec]
    have h1 := congrArg (transportInv h R *ᵥ ·) hv
    simpa only [key] using h1

omit [CharP K 2] in
theorem blk_apply_fs (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K)
    (a b : Fin 2 ⊕ Fin k) :
    blk X S (finSumFinEquiv a) (finSumFinEquiv b) = fromBlocks X 0 0 S a b := by
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

omit [CharP K 2] in
theorem blk_one_mulVec_inr (X : Matrix (Fin 2) (Fin 2) K) (j : Fin k) :
    blk X 1 *ᵥ (Pi.single (finSumFinEquiv (.inr j)) 1 : Fin (2 + k) → K) =
      Pi.single (finSumFinEquiv (.inr j)) 1 := by
  ext i
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  rw [mulVec_single_one, col_apply, blk_apply_fs]
  rcases a with a | a
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply,
      Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr)]
  · rw [fromBlocks_apply₂₂, one_apply]
    simp only [Pi.single_apply, finSumFinEquiv.injective.eq_iff, Sum.inr.injEq]

omit [CharP K 2] in
include h in
theorem eq_blk_one_of_fix {T : StatedSU (2 + k) (2 ^ f) K}
    (hT : ∀ j : Fin k, (T : GL (Fin (2 + k)) K).val *ᵥ Pi.single (finSumFinEquiv (.inr j)) 1 =
      Pi.single (finSumFinEquiv (.inr j)) 1) :
    (T : GL (Fin (2 + k)) K).val =
      blk (Matrix.of fun i i' => (T : GL (Fin (2 + k)) K).val (finSumFinEquiv (.inl i))
        (finSumFinEquiv (.inl i'))) 1 := by
  have hrow : ∀ (j : Fin k) (v : Fin (2 + k) → K),
      ((T : GL (Fin (2 + k)) K).val *ᵥ v) (finSumFinEquiv (.inr j)) =
        v (finSumFinEquiv (.inr j)) := by
    intro j v
    rw [← hform_single_one_left (σ := h.bar) (finSumFinEquiv (.inr j))
      ((T : GL (Fin (2 + k)) K).val *ᵥ v), ← hT j, hform_mulVec_mulVec h T,
      hform_single_one_left]
  ext x y
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective y
  rw [blk_apply_fs]
  rcases a with a | a <;> rcases b with b | b
  · rw [fromBlocks_apply₁₁, of_apply]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    have h1 := congrFun (hT b) (finSumFinEquiv (.inl a))
    rwa [mulVec_single_one, col_apply,
      Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr)] at h1
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    have h1 := hrow a (Pi.single (finSumFinEquiv (.inl b)) 1)
    rwa [mulVec_single_one, col_apply,
      Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inr_ne_inl)] at h1
  · rw [fromBlocks_apply₂₂]
    have h1 := congrFun (hT b) (finSumFinEquiv (.inr a))
    rw [mulVec_single_one, col_apply] at h1
    simp only [Pi.single_apply, finSumFinEquiv.injective.eq_iff, Sum.inr.injEq] at h1
    rw [h1, one_apply]

end Std

section Corr

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} (h : UnitaryFieldData 2 f K) (hk : 2 ≤ k)

theorem single_ix₀_eq (s : K) :
    (Pi.single (ix₀ hk) 1 : Fin (2 + k) → K) = (s + 1) • uv₀ hk + uf₀ hk s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i
  simp only [uv₀_eq, uf₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(s * (Pi.single (ix₀ hk) (1 : K) : Fin (2 + k) → K) i +
    (s + 1) * (Pi.single (ix₁ hk) (1 : K) : Fin (2 + k) → K) i)) * h2

theorem single_ix₁_eq (s : K) :
    (Pi.single (ix₁ hk) 1 : Fin (2 + k) → K) = s • uv₀ hk + uf₀ hk s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i
  simp only [uv₀_eq, uf₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(s * ((Pi.single (ix₀ hk) (1 : K) : Fin (2 + k) → K) i +
    (Pi.single (ix₁ hk) (1 : K) : Fin (2 + k) → K) i))) * h2

theorem fix_inr_of_fix {T : Matrix (Fin (2 + k)) (Fin (2 + k)) K} {s : K}
    (he : T *ᵥ uv₀ hk = uv₀ hk) (hf : T *ᵥ uf₀ hk s = uf₀ hk s)
    (hz : ∀ j : Fin k, 2 ≤ (j : ℕ) → T *ᵥ Pi.single (zIdx j) 1 = Pi.single (zIdx j) 1)
    (j : Fin k) :
    T *ᵥ Pi.single (finSumFinEquiv (.inr j)) 1 = Pi.single (finSumFinEquiv (.inr j)) 1 := by
  by_cases hj : (j : ℕ) < 2
  · rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h0 | h1
    · have hj0 : (finSumFinEquiv (Sum.inr j) : Fin (2 + k)) = ix₀ hk :=
        congrArg (fun i => finSumFinEquiv (Sum.inr i)) (Fin.ext h0)
      rw [hj0, single_ix₀_eq hk s, mulVec_add, mulVec_smul, he, hf]
    · have hj1 : (finSumFinEquiv (Sum.inr j) : Fin (2 + k)) = ix₁ hk :=
        congrArg (fun i => finSumFinEquiv (Sum.inr i)) (Fin.ext h1)
      rw [hj1, single_ix₁_eq hk s, mulVec_add, mulVec_smul, he, hf]
  · rw [← zIdx_of_two_le (by omega)]
    exact hz j (by omega)

omit [CharP K 2] in
theorem fix_of_fix_inr {T : Matrix (Fin (2 + k)) (Fin (2 + k)) K} (s : K)
    (hT : ∀ j : Fin k, T *ᵥ Pi.single (finSumFinEquiv (.inr j)) 1 =
      Pi.single (finSumFinEquiv (.inr j)) 1) :
    T *ᵥ uv₀ hk = uv₀ hk ∧ T *ᵥ uf₀ hk s = uf₀ hk s ∧
      ∀ j : Fin k, 2 ≤ (j : ℕ) → T *ᵥ Pi.single (zIdx j) 1 = Pi.single (zIdx j) 1 := by
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [uv₀_eq, mulVec_add, hT, hT]
  · rw [uf₀, mulVec_add, mulVec_smul, mulVec_smul, hT, hT]
  · rw [zIdx_of_two_le hj]
    exact hT j

end Corr

section W

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} (h : UnitaryFieldData 2 f K) (hk : 2 ≤ k)
  {s : K} (hs : s + h.bar s = 1)

noncomputable abbrev tmat (g : hypSU h 1 k) : Matrix (Fin (2 + k)) (Fin (2 + k)) K :=
  ((hypTransport h (isHypTransport_uFrame h hk hs) g : StatedSU (2 * 1 + k) (2 ^ f) K) :
    GL (Fin (2 * 1 + k)) K).val

theorem mem_stdW_iff_fix (g : stabE (ε := k) h) :
    g ∈ stdW h ↔ ∀ j : Fin k, tmat h hk hs g *ᵥ Pi.single (finSumFinEquiv (.inr j)) 1 =
      Pi.single (finSumFinEquiv (.inr j)) 1 := by
  have hR := isHypTransport_uFrame h hk hs
  have hg := (mem_stabE h).mp g.2
  constructor
  · rintro ⟨hgf, hgz⟩
    refine fix_inr_of_fix hk (s := s) ?_ ?_ ?_
    · have h1 := (mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 k) _).mp hg
      rwa [uFrame_mulVec_hE] at h1
    · have h1 := (mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 k) _).mp hgf
      rwa [uFrame_mulVec_hF] at h1
    · intro j hj
      have h1 := (mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 k) _).mp (hgz j hj)
      rwa [uFrame_mulVec_z] at h1
  · intro hT
    obtain ⟨-, hf, hz⟩ := fix_of_fix_inr hk s hT
    refine ⟨(mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 k) _).mpr ?_, fun j hj =>
      (mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 k) _).mpr ?_⟩
    · rw [uFrame_mulVec_hF]
      exact hf
    · rw [uFrame_mulVec_z]
      exact hz j hj

theorem mem_stdW_iff_uBarW (g : stabE (ε := k) h) :
    g ∈ stdW h ↔
      uProj K (2 + k) f (hypTransport h (isHypTransport_uFrame h hk hs) g) ∈ uBarW K k f := by
  rw [mem_stdW_iff_fix h hk hs]
  constructor
  · intro hT
    obtain ⟨X, hX⟩ := mem_range_uW_of h
      (eq_blk_one_of_fix h (T := hypTransport h (isHypTransport_uFrame h hk hs) g) hT)
    exact ⟨X, by simp only [MonoidHom.comp_apply]; rw [hX]⟩
  · rintro ⟨X, hX⟩
    simp only [MonoidHom.comp_apply] at hX
    obtain ⟨c, hc⟩ := uProj_eq_uProj_iff.mp hX
    have hm : tmat h hk hs g =
        (c : K) • blk ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 := by
      have h1 := congrArg Units.val hc
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uW, scalar_apply,
        ← smul_eq_diagonal_mul] at h1
      exact h1
    have he : tmat h hk hs g *ᵥ uv₀ hk = uv₀ hk := by
      have h1 := (mulVec_eq_iff_hypTransport h (isHypTransport_uFrame h hk hs)
        (g : hypSU h 1 k) _).mp ((mem_stabE h).mp g.2)
      rwa [uFrame_mulVec_hE] at h1
    have hX1 : blk ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 *ᵥ uv₀ hk = uv₀ hk := by
      rw [uv₀_eq, mulVec_add, blk_one_mulVec_inr, blk_one_mulVec_inr]
    rw [hm, smul_mulVec, hX1] at he
    have hc1 : (c : K) = 1 := by
      have h1 := congrFun he (ix₀ hk)
      rwa [Pi.smul_apply, uv₀_ix₀, smul_eq_mul, mul_one] at h1
    intro j
    rw [hm, hc1, one_smul, blk_one_mulVec_inr]

end W

end CFSG.ComponentClassification.RankTwoClassical.URigid
