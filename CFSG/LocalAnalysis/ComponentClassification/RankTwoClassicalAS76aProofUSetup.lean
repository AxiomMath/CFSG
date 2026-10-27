module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Transvection

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {σ : K →+* K}

omit [DecidableEq ι] in
theorem hform_single_one_left [DecidableEq ι] (b : ι) (v : ι → K) :
    hform σ (Pi.single b 1) v = v b := by
  rw [hform, dotProduct, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

theorem exists_hform_eq_one (hσ : ∀ x, σ (σ x) = x) {u : ι → K} (hu : u ≠ 0) :
    ∃ w : ι → K, hform σ u w = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, u b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  have hs : σ (u b) ≠ 0 := fun h0 => hb (by rw [← hσ (u b), h0, map_zero])
  refine ⟨(σ (u b))⁻¹ • Pi.single b 1, ?_⟩
  rw [hform_smul_right, hform_comm hσ, hform_single_one_left, inv_mul_cancel₀ hs]

theorem exists_hermitian_rank_one (hσ : ∀ x, σ (σ x) = x) {N : Matrix ι ι K}
    (hNh : adjM σ N = N) (hN : N * N = 0) (hr : N.rank = 1) :
    ∃ (u : ι → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧ σ c = c ∧ hform σ u u = 0 ∧
      ∀ v, N *ᵥ v = (c * hform σ u v) • u := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, N *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    have hN0 : N = 0 := by
      ext r t
      have := congrFun (h (Pi.single t 1)) r
      rwa [Matrix.mulVec_single_one, col_apply] at this
    rw [hN0, rank_zero] at hr
    exact zero_ne_one hr
  set u := N *ᵥ v₀ with hu
  have hline : ∀ v, ∃ a : K, N *ᵥ v = a • u := by
    have hle : (K ∙ u) ≤ LinearMap.range N.mulVecLin := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨v₀, rfl⟩
    have heq : (K ∙ u) = LinearMap.range N.mulVecLin := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [finrank_span_singleton hv₀]
      exact hr.symm
    intro v
    have hv : N *ᵥ v ∈ (K ∙ u) := by
      rw [heq]
      exact ⟨v, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨a, ha.symm⟩
  choose φ hφ using hline
  have hrel : ∀ v w, σ (φ v) * hform σ u w = φ w * hform σ v u := by
    intro v w
    have h1 := hform_mulVec (σ := σ) N v w
    rw [hNh, hφ, hφ, hform_smul_left, hform_smul_right] at h1
    exact h1
  obtain ⟨w₀, hw₀⟩ := exists_hform_eq_one hσ hv₀
  have hw₀' : hform σ w₀ u = 1 := by rw [hform_comm hσ, hw₀, map_one]
  have hc : σ (φ w₀) = φ w₀ := by
    have := hrel w₀ w₀
    rwa [hw₀, hw₀', mul_one, mul_one] at this
  have hφv : ∀ v, φ v = φ w₀ * hform σ u v := by
    intro v
    have h1 := hrel v w₀
    rw [hw₀, mul_one] at h1
    calc φ v = σ (σ (φ v)) := (hσ _).symm
      _ = σ (φ w₀ * hform σ v u) := by rw [h1]
      _ = φ w₀ * hform σ u v := by rw [map_mul, hc, hform_comm hσ v u]
  have hc0 : φ w₀ ≠ 0 := by
    intro h0
    apply hv₀
    rw [hu, hφ, hφv, h0, zero_mul, zero_smul]
  refine ⟨u, φ w₀, hv₀, hc0, hc, ?_, fun v => by rw [hφ, hφv]⟩
  have h1 : N *ᵥ u = 0 := by rw [hu, mulVec_mulVec, hN, zero_mulVec]
  rw [hφ, hφv, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (mul_eq_zero.mp h1).resolve_left hc0
  · exact absurd h1 hv₀

end Transvection

section Vectors

variable {K : Type} [Field K] {k : ℕ}

@[expose] def uw₀ (hk : 2 ≤ k) : Fin k → K :=
  Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1

@[expose] def uv₀ (hk : 2 ≤ k) : Fin (2 + k) → K :=
  Pi.single (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)) 1 +
    Pi.single (finSumFinEquiv (Sum.inr ⟨1, by omega⟩)) 1

theorem uv₀_inl (hk : 2 ≤ k) (i : Fin 2) : uv₀ (K := K) hk (finSumFinEquiv (Sum.inl i)) = 0 := by
  rw [uv₀, Pi.add_apply, Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr),
    Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr), add_zero]

theorem uv₀_inr (hk : 2 ≤ k) (j : Fin k) :
    uv₀ (K := K) hk (finSumFinEquiv (Sum.inr j)) = uw₀ hk j := by
  simp only [uv₀, uw₀, Pi.add_apply, Pi.single_apply, finSumFinEquiv.injective.eq_iff,
    Sum.inr.injEq]

theorem uv₀_ne_zero (hk : 2 ≤ k) : uv₀ (K := K) hk ≠ 0 := by
  intro h0
  have := congrFun h0 (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
  rw [uv₀_inr] at this
  simp [uw₀, Fin.ext_iff] at this

theorem vecMulVec_uv₀ (hk : 2 ≤ k) :
    vecMulVec (uv₀ (K := K) hk) (uv₀ hk) = blk 0 (vecMulVec (uw₀ hk) (uw₀ hk)) := by
  ext x y
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, vecMulVec_apply]
  rcases x with x | x <;> rcases y with y | y
  · rw [uv₀_inl, zero_mul, fromBlocks_apply₁₁, Matrix.zero_apply]
  · rw [uv₀_inl, zero_mul, fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [uv₀_inl, mul_zero, fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [uv₀_inr, uv₀_inr, fromBlocks_apply₂₂, vecMulVec_apply]

theorem hform_single_add_single [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) {a b : ι} (hab : a ≠ b) :
    hform σ (Pi.single a 1 + Pi.single b 1) (Pi.single a 1 + Pi.single b 1) = 0 := by
  rw [hform_add_left, hform_single_one_left, hform_single_one_left]
  simp [hab, Ne.symm hab, CharTwo.add_self_eq_zero]

theorem hform_uv₀ [CharP K 2] (σ : K →+* K) (hk : 2 ≤ k) : hform σ (uv₀ hk) (uv₀ hk) = 0 :=
  hform_single_add_single σ (by simp [Fin.ext_iff])

theorem comp_uv₀ (σ : K →+* K) (hk : 2 ≤ k) : σ ∘ uv₀ (K := K) hk = uv₀ hk := by
  funext i
  simp only [Function.comp, uv₀, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

end Vectors

section Witt

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K)
include h

theorem herm_eq_hform {n : ℕ} (x y : Fin n → K) :
    CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) x y =
      hform h.bar x y := by
  simp only [CFSG.ClassicalGroups.Unitary.herm, hform, dotProduct, Function.comp,
    CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]

theorem exists_statedSU_mulVec_eq {n : ℕ} (hn : 3 ≤ n) {a a' : Fin n → K} (ha0 : a ≠ 0)
    (ha : hform h.bar a a = 0) (ha0' : a' ≠ 0) (ha' : hform h.bar a' a' = 0) :
    ∃ g : StatedSU n (2 ^ f) K, (g : GL (Fin n) K).val *ᵥ a = a' := by
  have hK := h.card_eq_sq
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨t, -, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_iso hσ hn ha0
    (by rw [herm_eq_hform h]; exact ha) ha0' (by rw [herm_eq_hform h]; exact ha')
  have hmem : (t : GL (Fin n) K) ∈ StatedSU n (2 ^ f) K := by
    rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n]
    exact t.2
  exact ⟨⟨t, hmem⟩, ht⟩

omit [Finite K] [CharP K 2] in
theorem hform_mulVec_mulVec {n : ℕ} (g : StatedSU n (2 ^ f) K) (x y : Fin n → K) :
    hform h.bar ((g : GL (Fin n) K).val *ᵥ x) ((g : GL (Fin n) K).val *ᵥ y) = hform h.bar x y := by
  rw [hform_mulVec, mulVec_mulVec,
    adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply g.2, one_mulVec]

end Witt

section Setup

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k f : ℕ}
variable {G : Type} [Group G] {A : Subgroup G}

theorem exists_uLeviTheta_spec (hk : 2 ≤ k) (h : UnitaryFieldData 2 f K)
    (e : rankTwoQuot A ≃* StatedProj (StatedSU (2 + k) (2 ^ f) K)) {p : G}
    (hp : IsInvolutionOfRank e p 1) :
    ∃ θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K), θ.ker = center ↥A ∧
      Function.Surjective θ ∧
      (∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (2 + k)) K, Represents e p M ∧
        orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 = a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (uBarL K k f) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) ∧
      ∃ (hpA : p ∈ A) (c : K) (Mp : StatedSU (2 + k) (2 ^ f) K), c ≠ 0 ∧ h.bar c = c ∧
        ((Mp : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
          blk 1 (1 + c • vecMulVec (uw₀ hk) (uw₀ hk)) ∧
        θ ⟨p, hpA⟩ = uProj K (2 + k) f Mp := by
  obtain ⟨-, M, hpM, hM2, hr⟩ := hp
  have hMH : M ∈ StatedSU (2 + k) (2 ^ f) K := hpM.2.1
  have hMu := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply hMH
  have hMM : (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * M = 1 := by
    have h1 := pow_orderOf_eq_one M
    rw [hM2, sq] at h1
    rw [← Units.val_mul, h1, Units.val_one]
  have hMadj : adjM h.bar (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = M := by
    calc adjM h.bar (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        adjM h.bar (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM h.bar ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) =
      (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  obtain ⟨u, c, hu, hc0, hcσ, huu, huc⟩ := exists_hermitian_rank_one h.bar_bar hNh
    (sub_one_mul_self_eq_zero hM2) hr
  obtain ⟨g, hg⟩ := exists_statedSU_mulVec_eq h (n := 2 + k) (by omega) (uv₀_ne_zero hk)
    (hform_uv₀ h.bar hk) hu huu
  have hgi : ((g⁻¹ : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K).val *ᵥ u = uv₀ hk := by
    rw [← hg, mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec]
  have hE : blk 0 (c • vecMulVec (uw₀ hk) (uw₀ hk)) = c • vecMulVec (uv₀ (K := K) hk) (uv₀ hk) := by
    rw [vecMulVec_uv₀, blk_smul, smul_zero]
  have hconj : ((g⁻¹ : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K).val *
      ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) * (g : GL (Fin (2 + k)) K).val =
        blk 0 (c • vecMulVec (uw₀ hk) (uw₀ hk)) := by
    rw [hE]
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, huc, mulVec_smul, hgi, ← hg, hform_mulVec_mulVec h,
      smul_mulVec, vecMulVec_mulVec', smul_smul, hform, comp_uv₀]
  refine ⟨(MulAut.conj (uProj K (2 + k) f g⁻¹)).toMonoidHom.comp (quotModelHom e), ?_, ?_, ?_,
    ?_⟩
  · rw [← ker_quotModelHom (e := e)]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · exact (MulAut.conj _).surjective.comp quotModelHom_surjective
  · rintro y ⟨hyj, M₁, N, hpM₁, hM₁2, hyN, a, ha⟩
    refine ⟨?_, hyj⟩
    obtain rfl := hpM.eq_of_orderOf_eq_two hpM₁ hM2 hM₁2
    have hNH : N ∈ StatedSU (2 + k) (2 ^ f) K := hyN.2.1
    obtain ⟨hyA, hyθ⟩ := (represents_iff_quotModelHom hNH).mp hyN
    refine mem_liftSub.mpr ⟨hyA, ?_⟩
    rw [MonoidHom.comp_apply, hyθ, MulEquiv.coe_toMonoidHom]
    change MulAut.conj (uProj K (2 + k) f g⁻¹) (uProj K (2 + k) f ⟨N, hNH⟩) ∈ _
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, inv_inv]
    have hNe : (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        1 + a • ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) := by
      rw [← ha, add_sub_cancel]
    obtain ⟨S, hS⟩ := mem_range_uL_of h (g := g⁻¹ * ⟨N, hNH⟩ * g)
      (S := 1 + (a * c) • vecMulVec (uw₀ hk) (uw₀ hk)) (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
        change ((g⁻¹ : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K).val *
          (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (g : GL (Fin (2 + k)) K).val = _
        rw [hNe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
          hconj, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk_smul,
          smul_zero, smul_smul, ← blk_one, blk_add, add_zero])
    exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩
  ·
    obtain ⟨hpA, hpθ⟩ := (represents_iff_quotModelHom hMH).mp hpM
    refine ⟨hpA, c, g⁻¹ * ⟨M, hMH⟩ * g, hc0, hcσ, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      change ((g⁻¹ : StatedSU (2 + k) (2 ^ f) K) : GL (Fin (2 + k)) K).val *
        (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (g : GL (Fin (2 + k)) K).val = _
      have hMe : (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
          1 + ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) := by
        rw [add_sub_cancel]
      rw [hMe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hconj, Subgroup.coe_inv,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, ← blk_one, blk_add, add_zero]
    · rw [MonoidHom.comp_apply, hpθ, MulEquiv.coe_toMonoidHom]
      change MulAut.conj (uProj K (2 + k) f g⁻¹) (uProj K (2 + k) f ⟨M, hMH⟩) = _
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, inv_inv]

end Setup

end CFSG.ComponentClassification.RankTwoClassical
