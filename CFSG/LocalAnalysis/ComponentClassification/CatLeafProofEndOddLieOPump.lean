module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalCommutant
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Module QuadraticMap

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {M F : Submodule K V}

abbrev orthSecondDerived {W : Type} [AddCommGroup W] [Module K W] (Q : QuadraticForm K W) :
    Subgroup (W ≃ₗ[K] W) :=
  ⁅⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆⁆

theorem exists_of_mem_secondDerived {Q : QuadraticForm K V} {Y : Subgroup (V ≃ₗ[K] V)}
    (ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
    (hρ : ∀ (y : Y) (m : M), (((ρ y).val m : M) : V) = (y : V ≃ₗ[K] V) m)
    (hrange : ρ.range = commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))) :
    ∀ x ∈ orthSecondDerived (Q.comp M.subtype), ∃ y ∈ Y, ∀ m : M, ((x m : M) : V) = y m := by
  intro x hx
  have hx' : x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype),
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype)⁆ :=
    Subgroup.commutator_le_self _ hx
  rw [← Subgroup.map_subtype_commutator, ← hrange] at hx'
  obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hx'
  exact ⟨y, y.2, hρ y⟩

theorem commutant_block [Finite K] [FiniteDimensional K V] (hk : ringChar K ≠ 2)
    {Q : QuadraticForm K V} (hMF : IsCompl M F) (horth : ∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate)
    (hM4 : 4 ≤ finrank K M) {Y : Subgroup (V ≃ₗ[K] V)}
    (hYF : ∀ y ∈ Y, ∀ f ∈ F, y f = f)
    (hD : ∀ x ∈ orthSecondDerived (Q.comp M.subtype), ∃ y ∈ Y, ∀ m : M, ((x m : M) : V) = y m)
    {B : V ≃ₗ[K] V} (hBO : B ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hBY : ∀ y ∈ Y, y * B = B * y) :
    (∀ f ∈ F, B f ∈ F) ∧ ∃ l : K, l * l = 1 ∧ ∀ m ∈ M, B m = l • m := by
  classical
  have hQM : (Q.comp M.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hMnd
  obtain ⟨hcent, hfix, -⟩ :=
    LocalAnalysis.ComponentInitial.odd_orthogonal_second_derived_natural_commutant hk hM4
      (Q.comp M.subtype) hQM
  have hfix' := Set.ext_iff.mp hfix
  have hpres : ∀ C : V ≃ₗ[K] V, (∀ y ∈ Y, y * C = C * y) → ∀ f ∈ F, C f ∈ F := by
    intro C hCY f hf
    obtain ⟨m, f', hmf⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF (C f)
    have hm : m = 0 := (hfix' m).mp fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hD x hx
      apply Subtype.ext
      rw [hxy]
      have h1 : y (C f) = C f := by
        rw [← LinearEquiv.mul_apply, hCY y hy, LinearEquiv.mul_apply, hYF y hy f hf]
      rw [hmf, map_add, hYF y hy f' f'.2] at h1
      exact add_right_cancel h1
    rw [hmf, hm, ZeroMemClass.coe_zero, zero_add]
    exact f'.2
  have hBY' : ∀ y ∈ Y, y * B⁻¹ = B⁻¹ * y := fun y hy => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hBY y hy, ← mul_assoc, inv_mul_cancel, one_mul]
  have hBF := hpres B hBY
  have hBF' := hpres B⁻¹ hBY'
  have hpresM : ∀ C : V ≃ₗ[K] V, C ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ f ∈ F, C⁻¹ f ∈ F) → ∀ m ∈ M, C m ∈ M := by
    intro C hCO hCF m hm
    obtain ⟨m', f', hmf⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF (C m)
    have hf0 : f' = 0 := by
      apply hFnd.1 f'
      intro f
      have h1 : polar Q (C m) f = 0 := by
        have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hCO m (C⁻¹ f)
        rw [show C (C⁻¹ (f : V)) = f from by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl]
          at h2
        rw [h2]
        exact horth m hm _ (hCF f f.2)
      rw [hmf, polar_add_left, horth m' m'.2 f f.2, zero_add] at h1
      exact h1
    rw [hmf, hf0, ZeroMemClass.coe_zero, add_zero]
    exact m'.2
  have hBM := hpresM B hBO (fun f hf => hBF' f hf)
  have hBM' := hpresM B⁻¹ (inv_mem hBO) (fun f hf => by rw [inv_inv]; exact hBF f hf)
  let BM : M ≃ₗ[K] M :=
    { toFun := fun m => ⟨B m, hBM m m.2⟩
      map_add' := fun x y => Subtype.ext (map_add B (x : V) (y : V))
      map_smul' := fun c x => Subtype.ext (map_smul B c (x : V))
      invFun := fun m => ⟨B⁻¹ m, hBM' m m.2⟩
      left_inv := fun m => Subtype.ext (B.symm_apply_apply m)
      right_inv := fun m => Subtype.ext (B.apply_symm_apply m) }
  have hBMc : BM ∈ centralizer ((orthSecondDerived (Q.comp M.subtype) : Subgroup (M ≃ₗ[K] M)) :
      Set (M ≃ₗ[K] M)) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hD x hx
    refine LinearEquiv.ext fun m => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change ((x (BM m) : M) : V) = B ((x m : M) : V)
    rw [hxy, hxy]
    change y (B m) = B (y m)
    rw [← LinearEquiv.mul_apply, hBY y hy, LinearEquiv.mul_apply]
  have hBMc' : BM ∈ ((centralizer ((orthSecondDerived (Q.comp M.subtype) :
      Subgroup (M ≃ₗ[K] M)) : Set (M ≃ₗ[K] M)) : Subgroup (M ≃ₗ[K] M)) : Set (M ≃ₗ[K] M)) :=
    hBMc
  rw [hcent] at hBMc'
  obtain ⟨a, ha⟩ := hBMc'
  have hBa : ∀ m ∈ M, B m = (a : K) • m := fun m hm => congrArg Subtype.val (ha ⟨m, hm⟩)
  refine ⟨hBF, a, ?_, hBa⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m : M, Q (m : V) ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nontrivial M := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    apply hm
    apply hMnd.1 m
    intro n
    have h1 : Q ((m : V) + n) = 0 := by
      rw [← Submodule.coe_add]
      exact hall _
    show polar Q (m : V) n = 0
    rw [polar, h1, hall m, hall n, sub_zero, sub_zero]
  have hQ1 : Q (B m₀) = Q m₀ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hBO m₀
  rw [hBa m₀ m₀.2, QuadraticMap.map_smul, smul_eq_mul] at hQ1
  have h0 : ((a : K) * a - 1) * Q m₀ = 0 := by rw [sub_mul, hQ1, one_mul, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hm₀)

theorem eigen_dims [FiniteDimensional K V] (hMF : IsCompl M F) (h2 : (2 : K) ≠ 0)
    {B : V ≃ₗ[K] V} {l : K} (hl : l * l = 1) (hBM : ∀ m ∈ M, B m = l • m)
    (hBF : ∀ f ∈ F, B f ∈ F) (hBB : ∀ v, B (B v) = v) (hne : ∃ f ∈ F, B f ≠ -l • f) :
    finrank K M < finrank K (Module.End.eigenspace B.toLinearMap l) ∧
      finrank K (Module.End.eigenspace B.toLinearMap (-l)) < finrank K F := by
  obtain ⟨f₀, hf₀, hne₀⟩ := hne
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact zero_ne_one hl
  constructor
  · apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (fun m hm => ?_) fun h => ?_
    · rw [Module.End.mem_eigenspace_iff]
      exact hBM m hm
    ·
      have huE : f₀ + l • B f₀ ∈ Module.End.eigenspace B.toLinearMap l := by
        rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_toLinearMap, map_add, map_smul, hBB,
          smul_add, smul_smul, hl, one_smul, add_comm]
      have huF : f₀ + l • B f₀ ∈ F := F.add_mem hf₀ (F.smul_mem _ (hBF f₀ hf₀))
      have huM : f₀ + l • B f₀ ∈ M := by
        rw [h]
        exact huE
      have hu0 : f₀ + l • B f₀ = 0 := by
        rw [← Submodule.mem_bot K, ← hMF.inf_eq_bot]
        exact ⟨huM, huF⟩
      have h3 : l • B f₀ = -f₀ := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hu0
      apply hne₀
      calc B f₀ = l • (l • B f₀) := by rw [smul_smul, hl, one_smul]
        _ = -l • f₀ := by rw [h3, smul_neg, neg_smul]
  · apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (fun v hv => ?_) fun h => ?_
    · rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_toLinearMap] at hv
      obtain ⟨m, f, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF v
      rw [map_add, hBM m m.2, smul_add] at hv
      have h1 : l • (m : V) + l • (m : V) = -l • (f : V) - B f := by
        calc l • (m : V) + l • (m : V) = (l • (m : V) + B f) + l • (m : V) - B f := by abel
          _ = (-l • (m : V) + -l • (f : V)) + l • (m : V) - B f := by rw [hv]
          _ = -l • (f : V) - B f := by rw [neg_smul, neg_smul]; abel
      have hmM : l • (m : V) + l • (m : V) ∈ M := M.add_mem (M.smul_mem _ m.2) (M.smul_mem _ m.2)
      have hmF : l • (m : V) + l • (m : V) ∈ F := by
        rw [h1]
        exact F.sub_mem (F.smul_mem _ f.2) (hBF f f.2)
      have h0 : l • (m : V) + l • (m : V) = 0 := by
        rw [← Submodule.mem_bot K, ← hMF.inf_eq_bot]
        exact ⟨hmM, hmF⟩
      have hm0 : (m : V) = 0 := by
        rw [← add_smul] at h0
        rcases smul_eq_zero.mp h0 with h | h
        · exact absurd h (by rw [← two_mul]; exact mul_ne_zero h2 hl0)
        · exact h
      rw [hm0, zero_add]
      exact f.2
    · apply hne₀
      have h3 : f₀ ∈ Module.End.eigenspace B.toLinearMap (-l) := by
        rw [h]
        exact hf₀
      rw [Module.End.mem_eigenspace_iff] at h3
      exact h3

end CFSG.ComponentClassification.CatLeafProof.EndOddO
