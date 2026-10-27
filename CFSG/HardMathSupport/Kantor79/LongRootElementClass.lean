module

public import CFSG.HardMathSupport.Kantor79.LongRootGroup
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle CFSG.ClassicalGroups.Orthogonal
open QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem rootEnd_ne_zero_of_independent {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b : E}
    (hli : LinearIndependent K ![a, b]) : rootEnd Q a b ≠ 0 := by
  intro hψ
  have hb0 : b ≠ 0 := by
    have := hli.ne_zero (1 : Fin 2)
    simpa using this
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hb0
  have hvb : polar Q v b ≠ 0 := by rwa [polar_comm] at hv
  have h0 := congrArg (fun f : E →ₗ[K] E => f v) hψ
  rw [rootEnd_apply, LinearMap.zero_apply] at h0
  have ha_eq : a = (-(polar Q v a / polar Q v b)) • b := by
    have hsplit : polar Q v b • a = -(polar Q v a • b) := eq_neg_of_add_eq_zero_left h0
    calc a = (polar Q v b)⁻¹ • (polar Q v b • a) := by
          rw [smul_smul, inv_mul_cancel₀ hvb, one_smul]
      _ = (polar Q v b)⁻¹ • (-(polar Q v a • b)) := by rw [hsplit]
      _ = (-(polar Q v a / polar Q v b)) • b := by module
  have hmem : a ∈ Submodule.span K ({b} : Set E) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨-(polar Q v a / polar Q v b), ha_eq.symm⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hrel : (1 : K) • a + (-c) • b = 0 := by
    rw [one_smul, ← hc, ← add_smul, add_neg_cancel, zero_smul]
  have hpair := hli
  rw [LinearIndependent.pair_iff] at hpair
  have hone : (1 : K) = 0 := (hpair 1 (-c) hrel).1
  exact one_ne_zero hone

theorem rootEquiv_ne_one_of_independent {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b : E} (ha : Q a = 0) (hb : Q b = 0)
    (hab : polar Q a b = 0) (hli : LinearIndependent K ![a, b]) :
    rootEquiv Q a b ha hb hab ≠ 1 := by
  intro h
  have hψ : rootEnd Q a b = 0 := by
    ext v
    have hv : rootEquiv Q a b ha hb hab v = v := by rw [h]; rfl
    rw [rootEquiv_apply] at hv
    have hsum : polar Q v b • a + polar Q v a • b = 0 := by
      have h' := hv
      rw [add_assoc] at h'
      exact add_left_cancel (a := v)
        (show v + (polar Q v b • a + polar Q v a • b) = v + 0 by simpa using h')
    rw [rootEnd_apply]
    exact hsum
  exact rootEnd_ne_zero_of_independent hQ hli hψ

theorem isLongRootElement_iff_exists_mem_longRootGroup {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : E ≃ₗ[K] E} :
    IsLongRootElement Q x ↔
      ∃ (a b : E) (ha : Q a = 0) (hb : Q b = 0)
        (hab : QuadraticMap.polarBilin Q a b = 0) (hli : LinearIndependent K ![a, b]),
        x ∈ longRootGroup Q a b ha hb hab ∧ x ≠ 1 := by
  constructor
  · intro hx
    unfold IsLongRootElement at hx
    obtain ⟨a, b, ha, hb, hab, -, -, hli, hform⟩ := hx
    have hab' : QuadraticMap.polarBilin Q a b = 0 := hab
    have hx_eq : x = rootEquiv Q a b ha hb hab := by
      ext v
      rw [rootEquiv_apply]
      exact hform v
    refine ⟨a, b, ha, hb, hab', hli, ?_, ?_⟩
    · rw [hx_eq]
      exact siegelEquiv_mem_longRootGroup 1
    · rw [hx_eq]
      exact rootEquiv_ne_one_of_independent hQ ha hb hab hli
  · rintro ⟨a, b, ha, hb, hab, hli, hx, hx1⟩
    exact (mem_longRootGroup_isLongRootElement hQ.1 hli hx hx1).1

end CFSG.HardMathSupport.Kantor79
