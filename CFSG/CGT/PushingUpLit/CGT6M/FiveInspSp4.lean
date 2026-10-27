module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveSpAlg
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLA
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspCover
public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisAlg
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix CFSG.Open
open scoped commutatorElement

section Neg

variable {K : Type} [Field K] [CharP K 5]

theorem psp4_neg (h : ↥(StatedSp 2 K))
    (hM : ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (-1 : K) • 1) :
    ∃ Φ : C55 →* StatedProj (StatedSp 2 K), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk h : StatedProj (StatedSp 2 K)) * Φ u *
        (QuotientGroup.mk h : StatedProj (StatedSp 2 K))⁻¹ = (Φ u)⁻¹ := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hMdef
  have hsymp : Mᵀ * spJ K * M = spJ K := symp_of_mem_statedSp h.2
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have : (1 : K) = 0 := by linear_combination 3 * h2 - h5
    exact one_ne_zero this
  obtain ⟨a₁, a₂, hLI, ha₁, ha₂⟩ := exists_two_eigen_sp hsymp hM
  have hne : (2 : K) * 2 ≠ 1 := by
    intro h22
    apply h2
    linear_combination h5 - h22
  have o12 : spLam a₁ ⬝ᵥ a₂ = 0 := spLam_eigen_zero hsymp ha₁ ha₂ hne
  have o21 : spLam a₂ ⬝ᵥ a₁ = 0 := spLam_eigen_zero hsymp ha₂ ha₁ hne
  have o11 : spLam a₁ ⬝ᵥ a₁ = 0 := spLam_dot_self h2 a₁
  have o22 : spLam a₂ ⬝ᵥ a₂ = 0 := spLam_dot_self h2 a₂
  set A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := vecMulVec a₁ (spLam a₁) with hA
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := vecMulVec a₂ (spLam a₂) with hB
  have hAA : A * A = 0 := by simp [hA, vecMulVec_mul_vecMulVec, o11]
  have hAB : A * B = 0 := by simp [hA, hB, vecMulVec_mul_vecMulVec, o12]
  have hBA : B * A = 0 := by simp [hA, hB, vecMulVec_mul_vecMulVec, o21]
  have hBB : B * B = 0 := by simp [hB, vecMulVec_mul_vecMulVec, o22]
  have hMA : M * A = -(A * M) := by
    have e1 := spLam_vecMul_eigen hsymp hM ha₁
    have e2 : M * A = (2 : K) • A := by
      rw [hA, Matrix.mul_vecMulVec, ha₁, smul_vecMulVec]
    have e3 : A * M = ((2 : K) * (-1)) • A := by
      rw [hA, Matrix.vecMulVec_mul, e1, vecMulVec_smul]
    rw [e2, e3, ← neg_smul]
    congr 1
    ring
  have hMB : M * B = -(B * M) := by
    have e1 := spLam_vecMul_eigen hsymp hM ha₂
    have e2 : M * B = (2 : K) • B := by
      rw [hB, Matrix.mul_vecMulVec, ha₂, smul_vecMulVec]
    have e3 : B * M = ((2 : K) * (-1)) • B := by
      rw [hB, Matrix.vecMulVec_mul, e1, vecMulVec_smul]
    rw [e2, e3, ← neg_smul]
    congr 1
    ring
  have hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ StatedSp 2 K := fun a b => by
    apply Subgroup.subset_closure
    have e : ((Tu hAA hAB hBA hBB (zi K a) (zi K b) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (1 + zi K a • A) * (1 + zi K b • B) := by
      show Tm A B (zi K a) (zi K b) = _
      simp only [Tm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero]
      abel_nf
    show ((Tu hAA hAB hBA hBB (zi K a) (zi K b) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ K *
      ((Tu hAA hAB hBA hBB (zi K a) (zi K b) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ K
    rw [e]
    exact symp_mul (spTransv_symp h2 a₁ _) (spTransv_symp h2 a₂ _)
  have hind : ∀ a b : ZMod 5, zi K a • A + zi K b • B = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hx : ∀ x : Fin 2 ⊕ Fin 2 → K,
        (zi K a * (spLam a₁ ⬝ᵥ x)) • a₁ + (zi K b * (spLam a₂ ⬝ᵥ x)) • a₂ = 0 := by
      intro x
      have := congrArg (fun N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => N *ᵥ x) hab
      simpa [hA, hB, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
        op_smul_eq_smul, smul_smul] using this
    rw [LinearIndependent.pair_iff] at hLI
    have ha₁0 : a₁ ≠ 0 := by
      intro h0
      have := hLI 1 0 (by simp [h0])
      exact one_ne_zero this.1
    have ha₂0 : a₂ ≠ 0 := by
      intro h0
      have := hLI 0 1 (by simp [h0])
      exact one_ne_zero this.2
    obtain ⟨x₁, hx₁⟩ := exists_spLam_ne ha₁0
    obtain ⟨x₂, hx₂⟩ := exists_spLam_ne ha₂0
    have e1 := (hLI _ _ (hx x₁)).1
    have e2 := (hLI _ _ (hx x₂)).2
    exact ⟨(zi K).injective (by rw [map_zero]; exact (mul_eq_zero.mp e1).resolve_right hx₁),
      (zi K).injective (by rw [map_zero]; exact (mul_eq_zero.mp e2).resolve_right hx₂)⟩
  exact inverted_c55_proj (StatedSp 2 K) (h : GL (Fin 2 ⊕ Fin 2) K) h.2 hAA hAB hBA hBB hMA hMB
    hH hind

end Neg

section Pos

variable {K : Type} [Field K] [CharP K 5]

theorem psp4_pos (h : ↥(StatedSp 2 K))
    (hM : ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (1 : K) • 1)
    (hnon : ∀ a : K, ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠
      a • 1) :
    HeisInv (StatedProj (StatedSp 2 K)) (QuotientGroup.mk h) := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hMdef
  have hsymp : Mᵀ * spJ K * M = spJ K := symp_of_mem_statedSp h.2
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have : (1 : K) = 0 := by linear_combination 3 * h2 - h5
    exact one_ne_zero this
  have hMMx : ∀ x : Fin 2 ⊕ Fin 2 → K, M *ᵥ (M *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hM, Matrix.smul_mulVec, one_smul, Matrix.one_mulVec]
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_not_scalar M hnon
  have hv' := LinearIndependent.pair_iff.mp hv
  obtain ⟨a, b, hMa, hMb, ha0, hb0⟩ : ∃ a b : Fin 2 ⊕ Fin 2 → K, M *ᵥ a = (1 : K) • a ∧
      M *ᵥ b = (-1 : K) • b ∧ a ≠ 0 ∧ b ≠ 0 := by
    refine ⟨v + M *ᵥ v, v - M *ᵥ v, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mulVec_add, hMMx, one_smul, add_comm]
    · rw [Matrix.mulVec_sub, hMMx]
      module
    · intro h0
      have := hv' 1 1 (by rw [one_smul, one_smul]; exact h0)
      exact one_ne_zero this.1
    · intro h0
      have := hv' 1 (-1) (by rw [one_smul, neg_smul, one_smul, ← sub_eq_add_neg]; exact h0)
      exact one_ne_zero this.1
  have hne : (1 : K) * (-1) ≠ 1 := by
    intro h1
    apply h2
    linear_combination -h1
  have o_ab : spLam a ⬝ᵥ b = 0 := spLam_eigen_zero hsymp hMa hMb hne
  obtain ⟨y, hy⟩ := exists_spLam_ne ha0
  obtain ⟨a', hMa', hσ⟩ : ∃ a' : Fin 2 ⊕ Fin 2 → K, M *ᵥ a' = (1 : K) • a' ∧
      spLam a ⬝ᵥ a' = 2 * (spLam a ⬝ᵥ y) := by
    refine ⟨y + M *ᵥ y, ?_, ?_⟩
    · rw [Matrix.mulVec_add, hMMx, one_smul, add_comm]
    · have e := spLam_symp hsymp a (M *ᵥ y)
      rw [hMa, hMMx, one_smul] at e
      rw [dotProduct_add, ← e]
      ring
  have hσ0 : spLam a ⬝ᵥ a' ≠ 0 := by rw [hσ]; exact mul_ne_zero h2 hy
  have o_a'b : spLam a' ⬝ᵥ b = 0 := spLam_eigen_zero hsymp hMa' hMb hne
  have o_ba : spLam b ⬝ᵥ a = 0 := by rw [spLam_dot_swap, o_ab, neg_zero]
  have o_ba' : spLam b ⬝ᵥ a' = 0 := by rw [spLam_dot_swap, o_a'b, neg_zero]
  have o_a'a : spLam a' ⬝ᵥ a = -(spLam a ⬝ᵥ a') := spLam_dot_swap a' a
  have o_aa : spLam a ⬝ᵥ a = 0 := spLam_dot_self h2 a
  have o_bb : spLam b ⬝ᵥ b = 0 := spLam_dot_self h2 b
  have o_a'a' : spLam a' ⬝ᵥ a' = 0 := spLam_dot_self h2 a'
  have hσdef : spLam a ⬝ᵥ a' = spLam a ⬝ᵥ a' := rfl
  generalize hσg : spLam a ⬝ᵥ a' = σ at hσ0 o_a'a hσ
  set A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    vecMulVec a (spLam b) + vecMulVec b (spLam a) with hA
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    vecMulVec a' (spLam b) + vecMulVec b (spLam a') with hB
  set C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := vecMulVec b (spLam b) with hC
  have hrel : HeisRel A B C σ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [hA, hB, hC, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul_vecMulVec, o_ab,
      o_a'b, o_ba, o_ba', o_a'a, o_aa, o_bb, o_a'a', hσg, vecMulVec_smul]
  have hMA : M * A = -(A * M) := by
    have eb := spLam_vecMul_eigen hsymp hM hMb
    have ea := spLam_vecMul_eigen hsymp hM hMa
    simp only [hA, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hMa,
      hMb, eb, ea, smul_vecMulVec, vecMulVec_smul]
    module
  have hXH : Hu hrel 1 0 0 ∈ StatedSp 2 K := by
    apply Subgroup.subset_closure
    have e : ((Hu hrel 1 0 0 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        1 + (1 : K) • (vecMulVec a (spLam b) + vecMulVec b (spLam a)) := by
      show Hm A B C 1 0 0 = _
      simp [Hm, hA]
    show ((Hu hrel 1 0 0 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      spJ K * ((Hu hrel 1 0 0 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ K
    rw [e]
    exact spS2_symp h2 a b o_ab 1
  have hYH : Hu hrel 0 1 0 ∈ StatedSp 2 K := by
    apply Subgroup.subset_closure
    have e : ((Hu hrel 0 1 0 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        1 + (1 : K) • (vecMulVec a' (spLam b) + vecMulVec b (spLam a')) := by
      show Hm A B C 0 1 0 = _
      simp [Hm, hB]
    show ((Hu hrel 0 1 0 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      spJ K * ((Hu hrel 0 1 0 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ K
    rw [e]
    exact spS2_symp h2 a' b o_a'b 1
  let Xh : ↥(StatedSp 2 K) := ⟨Hu hrel 1 0 0, hXH⟩
  let Yh : ↥(StatedSp 2 K) := ⟨Hu hrel 0 1 0, hYH⟩
  have hZ : (((⁅Yh, Xh⁆ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K)) =
      Hu hrel 0 0 (-2 * σ) := by
    rw [← comm_Hu hrel]
    exact map_commutatorElement (StatedSp 2 K).subtype Yh Xh
  have hXpow : Xh ^ 5 = 1 := Subtype.ext (by
    show (Hu hrel 1 0 0) ^ 5 = 1
    rw [Hu_x_pow]
    have : ((5 : ℕ) : K) * 1 = 0 := by simpa using h5
    rw [this]
    exact Hu_zero hrel)
  have hYpow : Yh ^ 5 = 1 := Subtype.ext (by
    show (Hu hrel 0 1 0) ^ 5 = 1
    rw [Hu_y_pow]
    have : ((5 : ℕ) : K) * 1 = 0 := by simpa using h5
    rw [this]
    exact Hu_zero hrel)
  have hcX : Commute ⁅Yh, Xh⁆ Xh := Subtype.ext (by
    show (((⁅Yh, Xh⁆ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K)) * Hu hrel 1 0 0 =
      Hu hrel 1 0 0 * (((⁅Yh, Xh⁆ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K))
    rw [hZ]
    exact Hu_central_comm hrel _ 1 0 0)
  have hcY : Commute ⁅Yh, Xh⁆ Yh := Subtype.ext (by
    show (((⁅Yh, Xh⁆ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K)) * Hu hrel 0 1 0 =
      Hu hrel 0 1 0 * (((⁅Yh, Xh⁆ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K))
    rw [hZ]
    exact Hu_central_comm hrel _ 0 1 0)
  have hCne : C ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_spLam_ne hb0
    intro hC0
    have : C *ᵥ x = 0 := by rw [hC0, Matrix.zero_mulVec]
    rw [hC, Matrix.vecMulVec_mulVec, op_smul_eq_smul] at this
    exact smul_ne_zero hx hb0 this
  have hZ1 : (QuotientGroup.mk ⁅Yh, Xh⁆ : StatedProj (StatedSp 2 K)) ≠ 1 := by
    intro h1
    obtain ⟨s, hs⟩ := scalar_of_mk_eq_one _ h1
    rw [hZ] at hs
    have e : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + (-2 * σ) • C = s • 1 := by
      have e0 : ((Hu hrel 0 0 (-2 * σ) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 + (-2 * σ) • C := by
        show Hm A B C 0 0 (-2 * σ) = _
        simp [Hm]
      rw [e0] at hs
      exact hs
    have hN : ((-2 * σ) • C) * ((-2 * σ) • C) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hrel.CC]
      simp
    have h0 := nilp_eq_zero_of_add_one_scalar hN e
    have hne2 : (-2 * σ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hσ0
    exact hCne ((smul_eq_zero.mp h0).resolve_left hne2)
  have hinv : h * Xh * h⁻¹ = Xh⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    show ((h : GL (Fin 2 ⊕ Fin 2) K)) * Hu hrel 1 0 0 = (Hu hrel 1 0 0)⁻¹ * ((h : GL _ K))
    rw [Hu_inv]
    apply Units.ext
    show M * Hm A B C 1 0 0 = Hm A B C (-1) (-0) (-0) * M
    simp only [Hm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, hMA]
    module
  refine ⟨QuotientGroup.mk Xh, QuotientGroup.mk Yh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hXpow, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, hYpow, QuotientGroup.mk_one]
  · have e : ⁅(QuotientGroup.mk Yh : StatedProj (StatedSp 2 K)), QuotientGroup.mk Xh⁆ =
        QuotientGroup.mk ⁅Yh, Xh⁆ :=
      (map_commutatorElement (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedSp 2 K))) Yh Xh).symm
    rw [e]
    exact hcX.map (QuotientGroup.mk' _)
  · have e : ⁅(QuotientGroup.mk Yh : StatedProj (StatedSp 2 K)), QuotientGroup.mk Xh⁆ =
        QuotientGroup.mk ⁅Yh, Xh⁆ :=
      (map_commutatorElement (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedSp 2 K))) Yh Xh).symm
    rw [e]
    exact hcY.map (QuotientGroup.mk' _)
  · have e : ⁅(QuotientGroup.mk Yh : StatedProj (StatedSp 2 K)), QuotientGroup.mk Xh⁆ =
        QuotientGroup.mk ⁅Yh, Xh⁆ :=
      (map_commutatorElement (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedSp 2 K))) Yh Xh).symm
    rw [e]
    exact hZ1
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hinv,
      QuotientGroup.mk_inv]

end Pos

section Main

theorem scalar_sq_eq_one {K : Type} [Field K] {c : K}
    (hc : (c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * spJ K * (c • 1) = spJ K) :
    c * c = 1 := by
  have h1 : (c * c) • spJ K = spJ K := by
    simpa [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] using hc
  have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
  simpa [spJ] using h2

theorem psp4_five_invData {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5)
    (z : StatedProj (StatedSp 2 K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    InvData (StatedProj (StatedSp 2 K)) z := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : CharP K 5 := charP_of_card_eq_prime hcard
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  have hsymp := symp_of_mem_statedSp h.2
  have hcc : c * c = 1 := by
    have h2 := symp_mul hsymp hsymp
    rw [hM] at h2
    exact scalar_sq_eq_one h2
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · right
    rw [h1] at hM
    exact psp4_pos h hM hnon
  · left
    rw [h1] at hM
    exact psp4_neg h hM

theorem five_not_dvd_center_psp4 (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 5 1) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  intro h5
  have hmod' : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 5 1 :=
    hmod
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod'
  rcases CFSG.RankThree.PartOne.prime_dvd_table Nat.prime_five (by norm_num) (h5.trans hd) with
    ⟨ht, -, -⟩ | ⟨ht, -, -⟩ <;> exact absurd ht (by decide)

theorem coverInv_psp4 (hGA : CFSG.Open.GriessAllModelsStatement) (Q : Type) [Group Q]
    (hQ : StatedClassicalModel Q .PSp 2 5 1) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hQ
  have hK5 : Nat.card K = 5 := by simpa using hKc
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    exact invData_of_equiv e (psp4_five_invData hK5 (e w) hew1 hew2)
  · have hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 5 1 :=
      ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e⟩⟩
    exact five_not_dvd_center_psp4 hGA (isQuasisimple_of_open hq) hmod

end Main

end CFSG.CGT.PushingUpLit.CGT6M
