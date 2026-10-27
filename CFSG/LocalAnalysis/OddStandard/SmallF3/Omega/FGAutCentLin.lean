module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

theorem fg_eq_smul_of_commute_omega (hR : R.Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 3) W) (M : W →ₗ[ZMod 3] W)
    (hM : ∀ g ∈ omegaGroup hR, M ∘ₗ ((g : W ≃ₗ[ZMod 3] W) : W →ₗ[ZMod 3] W) =
      ((g : W ≃ₗ[ZMod 3] W) : W →ₗ[ZMod 3] W) ∘ₗ M) :
    ∃ c : ZMod 3, M = c • LinearMap.id := by
  have hB : R.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hR
  haveI : Finite (ZMod 3) := inferInstance
  have hcard : 2 < Nat.card (ZMod 3) := by
    rw [Nat.card_zmod]
    norm_num
  obtain ⟨hcomm, -⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      hcard R hB h3
  refine (hcomm M).mp ?_
  intro g hg
  rw [← Subgroup.map_subtype_commutator] at hg
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  exact hM g' (commutator_le_omegaGroup hR hg')

theorem fg_eq_zero_of_fixed_omega (hR : R.Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 3) W) {w : W}
    (hw : ∀ g ∈ omegaGroup hR, (g : W ≃ₗ[ZMod 3] W) w = w) : w = 0 := by
  by_contra hw0
  have hB : R.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hR
  let M : W →ₗ[ZMod 3] W := (R.polarBilin.flip w).smulRight w
  have hMapp : ∀ x, M x = R.polarBilin x w • w := fun x => rfl
  obtain ⟨c, hc⟩ := fg_eq_smul_of_commute_omega hR h3 M (by
    intro g hg
    ext x
    have hgw := hw g hg
    have hpol : R.polarBilin ((g : W ≃ₗ[ZMod 3] W) x) w = R.polarBilin x w := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 x w
      rw [hgw] at h
      exact h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hMapp, hpol,
      map_smul, hgw])
  obtain ⟨x, hx⟩ : ∃ x, R.polarBilin x w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 (hB.2 w h)
  have hcx : c • x = R.polarBilin x w • w := by
    have h := LinearMap.congr_fun hc x
    simpa [hMapp] using h.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcx
    exact hx ((smul_eq_zero.mp hcx.symm).resolve_right hw0)
  have htop : (⊤ : Submodule (ZMod 3) W) ≤ Submodule.span (ZMod 3) {w} := by
    intro y _
    have hy : c • y = R.polarBilin y w • w := by
      have h := LinearMap.congr_fun hc y
      simpa [hMapp] using h.symm
    have : y = c⁻¹ • (R.polarBilin y w • w) := by
      rw [← hy, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
  have hle := Submodule.finrank_mono htop
  rw [finrank_top, finrank_span_singleton hw0] at hle
  omega

end CFSG.OddStandard.SmallF3.Omega
