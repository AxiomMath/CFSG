module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoSchreier
public import CFSG.ClassicalGroups.UnitaryFlag.SemilinearIsotropicKernel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem lineNormalizer_eq_semilinearPointGroup (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) :
    lineNormalizer h r ε = semilinearPointGroup h r ε := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | hr3
  · obtain rfl : ε = 1 := by omega
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hq : 2 < p ^ f := lt_of_lt_of_le (by omega)
      (Nat.le_self_pow (by have := h.one_le; omega) p)
    exact (unitary_rank_one_permutation_normalizer h hq).1
  · exact (unitary_rank_two_permutation_normalizer h hε).1
  · exact (unitary_higher_permutation_normalizer h hr3 hε).1

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def semilinearNormalizerHom (r ε : ℕ) :
    semilinearSimilitudes h r ε →* lineNormalizer h r ε :=
  (semilinearPointAction h r ε).codRestrict _ fun x =>
    semilinearPointGroup_le_normalizer ⟨x, rfl⟩

@[expose] noncomputable def semilinearAutHom (hr : 1 ≤ r) (hε : ε ≤ 1) :
    semilinearSimilitudes h r ε →* MulAut (hypPSU h r ε) :=
  (linePermEquiv h hr hε).symm.toMonoidHom.comp (semilinearNormalizerHom h r ε)

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem linePerm_semilinearAutHom (x : semilinearSimilitudes h r ε) :
    linePerm h hr hε (semilinearAutHom h hr hε x) = semilinearPointAction h r ε x :=
  congrArg Subtype.val ((linePermEquiv h hr hε).apply_symm_apply (semilinearNormalizerHom h r ε x))

theorem semilinearAutHom_apply (x : semilinearSimilitudes h r ε) (g : hypSU h r ε) :
    semilinearAutHom h hr hε x (hypProj h r ε g) = hypProj h r ε ⟨_, conj_mem_hypSU x.2 g⟩ := by
  have h1 := linePerm_conj h hr hε (semilinearAutHom h hr hε x) (hypProj h r ε g)
  rw [linePerm_semilinearAutHom, semilinearPointAction_conj] at h1
  exact hypProjLineAction_injective h (by omega) h1.symm

theorem semilinearAutHom_surjective (hp : p ≠ 2) (hn : 3 ≤ 2 * r + ε) :
    Function.Surjective (semilinearAutHom h hr hε) := by
  intro α
  have hmem : linePerm h hr hε α ∈ semilinearPointGroup h r ε := by
    rw [← lineNormalizer_eq_semilinearPointGroup h hp hr hε hn, ← range_linePerm h hr hε]
    exact ⟨α, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, linePerm_injective h hr hε ?_⟩
  rw [linePerm_semilinearAutHom, hx]

theorem semilinearAutHom_eq_one_iff_pointAction (x : semilinearSimilitudes h r ε) :
    semilinearAutHom h hr hε x = 1 ↔ semilinearPointAction h r ε x = 1 := by
  constructor
  · intro h1
    rw [← linePerm_semilinearAutHom h hr hε x, h1, map_one]
  · intro h1
    apply linePerm_injective h hr hε
    rw [linePerm_semilinearAutHom h hr hε x, h1, map_one]

theorem eq_scalar_of_mulVec {A : GL (HypIndex r ε) K} {c : K} (hc0 : c ≠ 0)
    (hA : ∀ v, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = c • v) :
    A = GeneralLinearGroup.scalar (HypIndex r ε) (Units.mk0 c hc0) := by
  refine Units.ext (ext_iff_mulVec.mpr fun v => ?_)
  rw [hA, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply]
  funext i
  simp [mulVec_diagonal]

theorem semilinearPointAction_eq_one_iff (hn : 3 ≤ 2 * r + ε) (x : semilinearSimilitudes h r ε) :
    semilinearPointAction h r ε x = 1 ↔
      (x : SemiGL (HypIndex r ε) K).right = RingEquiv.refl K ∧
        ∃ c : Kˣ, (x : SemiGL (HypIndex r ε) K).left = GeneralLinearGroup.scalar _ c := by
  constructor
  · intro h1
    have := h.finite
    obtain ⟨μ, hμ0, hμ, hA⟩ := x.2
    have hfix : ∀ L : Submodule K (HypIndex r ε → K), Module.finrank K L = 1 →
        (∀ a ∈ L, ∀ b ∈ L, hypForm h r ε a b = 0) →
        semiLin (x : SemiGL (HypIndex r ε) K) '' (L : Set (HypIndex r ε → K)) = L := by
      intro L hL1 hLiso
      have hLmem : L ∈ hypIsotropicLines h r ε :=
        mem_hypIsotropicLines.mpr ⟨hL1, fun a ha => hLiso a ha a ha⟩
      have h2 := congrArg (fun π : Equiv.Perm (hypIsotropicLines h r ε) =>
        ((π ⟨L, hLmem⟩ : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K))) h1
      change (x : SemiGL (HypIndex r ε) K) • L = L at h2
      rw [semiGL_smul_eq_map] at h2
      rw [← Submodule.map_coe, h2]
    have hbij : Function.Bijective (semiLin (x : SemiGL (HypIndex r ε) K)) :=
      ⟨semiLin_injective _, Finite.injective_iff_surjective.mp (semiLin_injective _)⟩
    obtain ⟨hσ, c, hc0, hc⟩ :=
      (unitary_semilinear_isotropic_point_kernel h (by rw [finrank_hypIndex_fun]; exact hn)
        (hypForm_isSymm h)
        (hypForm_separatingLeft h)).1 (x : SemiGL (HypIndex r ε) K).right μ hμ0 hμ
        (semiLin (x : SemiGL (HypIndex r ε) K)) hbij (hypForm_semiLin h hA) hfix
    refine ⟨hσ, Units.mk0 c hc0, eq_scalar_of_mulVec hc0 fun v => ?_⟩
    have h3 : ((x : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (fun a => (x : SemiGL (HypIndex r ε) K).right (v a)) = c • v := hc v
    simpa only [hσ, RingEquiv.refl_apply] using h3
  · rintro ⟨hσ, c, hc⟩
    refine Equiv.ext fun L => Subtype.ext ?_
    rw [semilinearPointAction_apply, hσ, hc]
    change GeneralLinearGroup.scalar _ c • coordImage 1 (L : Submodule K (HypIndex r ε → K)) = _
    rw [coordImage_one, scalar_smul_submodule]
    rfl

theorem semilinearAutHom_eq_one_iff (hn : 3 ≤ 2 * r + ε) (x : semilinearSimilitudes h r ε) :
    semilinearAutHom h hr hε x = 1 ↔
      (x : SemiGL (HypIndex r ε) K).right = RingEquiv.refl K ∧
        ∃ c : Kˣ, (x : SemiGL (HypIndex r ε) K).left = GeneralLinearGroup.scalar _ c :=
  (semilinearAutHom_eq_one_iff_pointAction h hr hε x).trans
    (semilinearPointAction_eq_one_iff h hn x)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
