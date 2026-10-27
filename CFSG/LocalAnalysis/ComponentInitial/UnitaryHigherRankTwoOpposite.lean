module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoRestriction
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}

theorem unitary_rank_two_opposite_normalization (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (φ : Equiv.Perm (hypIsotropicLines h 2 ε)) (hφ : φ ∈ lineNormalizer h 2 ε) :
    ∃ x : semilinearSimilitudes h 2 ε,
      ((((x : SemiGL (HypIndex 2 ε) K).left : GL (HypIndex 2 ε) K) :
          Matrix (HypIndex 2 ε) (HypIndex 2 ε) K).map h.bar)ᵀ * hypGram 2 ε K *
        (((x : SemiGL (HypIndex 2 ε) K).left : GL (HypIndex 2 ε) K) :
          Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) = hypGram 2 ε K ∧
      ∀ L : hypIsotropicLines h 2 ε,
        ((L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ∨
          (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε) →
        φ L = semilinearPointAction h 2 ε x L := by
  have hB := hypForm_isSymm h (r := 2) (ε := ε)
  have hBl := hypForm_separatingLeft h (r := 2) (ε := ε)
  have hXs := hypX_isotropic h (r := 2) (ε := ε)
  have hYs := hypY_isotropic h (r := 2) (ε := ε)
  have hφo := (unitary_normalizer_preserves_orthogonality.{0} h (le_refl 2)).1 φ hφ
  set φ' := toIsoLines h φ with hφ'def
  have hφ' : ∀ L M : isoLines (hypForm h 2 ε),
      SubOrtho (hypForm h 2 ε) L M ↔ SubOrtho (hypForm h 2 ε) (φ' L) (φ' M) := fun L M => hφo L M
  set X₁ := polarImage (hypForm h 2 ε) φ' (hypX K 2 ε) with hX₁
  set Y₁ := polarImage (hypForm h 2 ε) φ' (hypY K 2 ε) with hY₁
  have hX₁s := isTotIso_polarImage φ' hφ' hXs
  have hY₁s := isTotIso_polarImage φ' hφ' hYs
  have hX₁d : finrank K X₁ = 2 := by
    rw [hX₁, finrank_polarImage h hB hBl hφ' hXs, finrank_hypX]
  have hY₁d : finrank K Y₁ = 2 := by
    rw [hY₁, finrank_polarImage h hB hBl hφ' hYs, finrank_hypY]
  have hX₁Y₁ : X₁ ⊓ Y₁ = ⊥ := by
    have hZs : ∀ v ∈ X₁ ⊓ Y₁, ∀ w ∈ X₁ ⊓ Y₁, hypForm h 2 ε v w = 0 :=
      fun v hv w hw => hX₁s v hv.1 w hw.1
    have hφ'' := subOrtho_symm_iff φ' hφ'
    have h1 : polarImage (hypForm h 2 ε) φ'.symm (X₁ ⊓ Y₁) ≤ hypX K 2 ε := by
      rw [← polarImage_symm_polarImage h hB hBl hφ' hXs]
      exact (polarImage_le_iff h hB hBl hφ'' hZs hX₁s).2 inf_le_left
    have h2 : polarImage (hypForm h 2 ε) φ'.symm (X₁ ⊓ Y₁) ≤ hypY K 2 ε := by
      rw [← polarImage_symm_polarImage h hB hBl hφ' hYs]
      exact (polarImage_le_iff h hB hBl hφ'' hZs hY₁s).2 inf_le_right
    have h0 : polarImage (hypForm h 2 ε) φ'.symm (X₁ ⊓ Y₁) = ⊥ := by
      rw [eq_bot_iff, ← hypX_inf_hypY]
      exact le_inf h1 h2
    have hd := finrank_polarImage h hB hBl hφ'' hZs
    rw [h0, finrank_bot] at hd
    exact Submodule.finrank_eq_zero.mp hd.symm
  obtain ⟨g, hgiso, hgX, hgY⟩ := exists_isometry_of_opposite h hε hX₁s hY₁s hX₁d hY₁d hX₁Y₁
  set x₀ : semilinearSimilitudes h 2 ε :=
    ⟨⟨glOfLinearEquiv g, 1⟩, isometry_mem_semilinearSimilitudes h hgiso⟩ with hx₀
  have hx₀J : ((((x₀ : SemiGL (HypIndex 2 ε) K).left : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K).map h.bar)ᵀ * hypGram 2 ε K *
        (((x₀ : SemiGL (HypIndex 2 ε) K).left : GL (HypIndex 2 ε) K) :
          Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) = hypGram 2 ε K :=
    (gramForm_isometry_iff h _ _).mp fun u v => by
      change gramForm h (hypGram 2 ε K)
        (((glOfLinearEquiv g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ u)
        (((glOfLinearEquiv g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ v)
          = _
      rw [glOfLinearEquiv_mulVec, glOfLinearEquiv_mulVec]
      exact hgiso u v
  have hx₀X : (x₀ : SemiGL (HypIndex 2 ε) K) • hypX K 2 ε = X₁ := by
    rw [hx₀, isometry_smul, hgX]
  have hx₀Y : (x₀ : SemiGL (HypIndex 2 ε) K) • hypY K 2 ε = Y₁ := by
    rw [hx₀, isometry_smul, hgY]
  have hη₀N : semilinearPointAction h 2 ε x₀ ∈ lineNormalizer h 2 ε :=
    semilinearPointGroup_le_normalizer ⟨x₀, rfl⟩
  obtain ⟨ψ₁, hψ₁def⟩ : ∃ ψ₁ : Equiv.Perm (hypIsotropicLines h 2 ε),
      ψ₁ = (semilinearPointAction h 2 ε x₀)⁻¹ * φ := ⟨_, rfl⟩
  have hψ₁N : ψ₁ ∈ lineNormalizer h 2 ε := by
    rw [hψ₁def]
    exact mul_mem (inv_mem hη₀N) hφ
  have hψ₁ : ∀ L M, LineOrth h L M ↔ LineOrth h (ψ₁ L) (ψ₁ M) := by
    rw [hψ₁def]
    exact lineOrth_inv_mul h x₀ hφo
  obtain ⟨ψ₁', hψ₁'def⟩ : ∃ ψ₁' : isoLines (hypForm h 2 ε) ≃ isoLines (hypForm h 2 ε),
      ψ₁' = toIsoLines h ψ₁ := ⟨_, rfl⟩
  have hψ₁' : ∀ L M : isoLines (hypForm h 2 ε),
      SubOrtho (hypForm h 2 ε) L M ↔ SubOrtho (hypForm h 2 ε) (ψ₁' L) (ψ₁' M) := by
    rw [hψ₁'def]
    exact fun L M => hψ₁ L M
  have hψ₁eq : ψ₁' = φ'.trans (toIsoLines h (semilinearPointAction h 2 ε x₀⁻¹)) := by
    rw [hψ₁'def, hψ₁def, map_inv]
    rfl
  have hψ₁X : polarImage (hypForm h 2 ε) ψ₁' (hypX K 2 ε) = hypX K 2 ε := by
    rw [hψ₁eq, polarImage_trans h hB hBl hφ' _ hXs, polarImage_semilinearPointAction h x₀⁻¹ hX₁s,
      ← hX₁, ← hx₀X, InvMemClass.coe_inv, inv_smul_smul]
  have hψ₁Y : polarImage (hypForm h 2 ε) ψ₁' (hypY K 2 ε) = hypY K 2 ε := by
    rw [hψ₁eq, polarImage_trans h hB hBl hφ' _ hYs, polarImage_semilinearPointAction h x₀⁻¹ hY₁s,
      ← hY₁, ← hx₀Y, InvMemClass.coe_inv, inv_smul_smul]
  have hpts : ∀ {W : Submodule K (HypIndex 2 ε → K)}, (∀ v ∈ W, ∀ w ∈ W, hypForm h 2 ε v w = 0) →
      polarImage (hypForm h 2 ε) ψ₁' W = W → ∀ L : hypIsotropicLines h 2 ε,
        ((ψ₁ L : Submodule K (HypIndex 2 ε → K)) ≤ W ↔
          (L : Submodule K (HypIndex 2 ε → K)) ≤ W) := by
    intro W hWs hW L
    have h1 := ptsIn_polarImage h hB hBl hψ₁' hWs
    rw [hW] at h1
    have h2 : ψ₁' L ∈ ψ₁' '' ptsIn (hypForm h 2 ε) W ↔ L ∈ ptsIn (hypForm h 2 ε) W :=
      ψ₁'.injective.mem_set_image
    rw [← h1, hψ₁'def] at h2
    exact h2
  have hψ₁XX := hpts hXs hψ₁X
  have hψ₁YY := hpts hYs hψ₁Y
  obtain ⟨A₀, σ, hA₀⟩ := exists_semilinear_on_hypX h hε hψ₁N hψ₁XX hψ₁YY
  have hT₁J := hypLevi_isometry (ε := ε) h A₀
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : semilinearSimilitudes h 2 ε,
      (x₁ : SemiGL (HypIndex 2 ε) K) = ⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩ :=
    ⟨⟨⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩, 1, one_ne_zero, map_one _, by
      rw [one_smul]
      exact hT₁J⟩, rfl⟩
  have hψ₁T₁ : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε →
      ψ₁ L = semilinearPointAction h 2 ε x₁ L := fun L hL => by
    apply Subtype.ext
    rw [hA₀ L hL, coe_semilinearPointAction, hx₁]
  obtain ⟨ψ₂, hψ₂def⟩ : ∃ ψ₂ : Equiv.Perm (hypIsotropicLines h 2 ε),
      ψ₂ = (semilinearPointAction h 2 ε x₁)⁻¹ * ψ₁ := ⟨_, rfl⟩
  have hψ₂ : ∀ L M, LineOrth h L M ↔ LineOrth h (ψ₂ L) (ψ₂ M) := by
    rw [hψ₂def]
    exact lineOrth_inv_mul h x₁ hψ₁
  have hψ₂X : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → ψ₂ L = L := by
    intro L hL
    rw [hψ₂def, Equiv.Perm.mul_apply, hψ₁T₁ L hL, Equiv.Perm.inv_eq_iff_eq]
  have hx₁Y : ((x₁⁻¹ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K) • hypY K 2 ε =
      hypY K 2 ε := by
    rw [InvMemClass.coe_inv, hx₁]
    conv_lhs => rw [← levi_smul_hypY (ε := ε) h A₀ σ]
    exact inv_smul_smul _ _
  have hψ₂Y : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε →
      (ψ₂ L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε := by
    intro L hL
    have h3 : (ψ₂ L : Submodule K (HypIndex 2 ε → K)) =
        ((x₁⁻¹ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K) •
          (ψ₁ L : Submodule K (HypIndex 2 ε → K)) := by
      rw [hψ₂def, Equiv.Perm.mul_apply, ← map_inv]
      rfl
    rw [h3, ← hx₁Y, semiGL_smul_eq_map, semiGL_smul_eq_map]
    exact Submodule.map_mono ((hψ₁YY L).mpr hL)
  refine ⟨x₀ * x₁, ?_, fun L hL => ?_⟩
  · have hl : ((x₀ * x₁ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K).left =
        (x₀ : SemiGL (HypIndex 2 ε) K).left * glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀) := by
      rw [Subgroup.coe_mul, hx₁, SemidirectProduct.mul_left]
      change (x₀ : SemiGL (HypIndex 2 ε) K).left *
        glAut (1 : K ≃+* K) (glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀)) = _
      rw [map_one, MulAut.one_apply]
    rw [hl, Units.val_mul, conjTranspose_mul_mul, hx₀J, hT₁J]
  · have hfix : ψ₂ L = L := hL.elim (hψ₂X L) fun hLY =>
      eq_of_le_hypY h ψ₂ hψ₂ hψ₂X hLY (hψ₂Y L hLY)
    have h1 : ψ₁ L = semilinearPointAction h 2 ε x₁ L := by
      rw [hψ₂def, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at hfix
      exact hfix
    rw [map_mul, Equiv.Perm.mul_apply, ← h1, hψ₁def, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
      Equiv.apply_symm_apply]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
