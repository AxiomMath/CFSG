module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_conj_vec (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) (g : OGroup Q)
    (h : phiSim Q (g * reflOf Q u hu * g⁻¹) = phiSim Q (reflOf Q w hw)) :
    ∃ a : ZMod 3, a ≠ 0 ∧ (g : V ≃ₗ[ZMod 3] V) u = a • w := by
  have hgu : Q ((g : V ≃ₗ[ZMod 3] V) u) ≠ 0 := by
    rw [map_ogroup_apply]; exact hu
  set A : OGroup Q := reflOf Q ((g : V ≃ₗ[ZMod 3] V) u) hgu with hA
  set B : OGroup Q := reflOf Q w hw with hB
  have hh : g * reflOf Q u hu * g⁻¹ = A := by
    rw [hA, mul_reflOf_mul_inv g u hu]
  have hab : phiSim Q A = phiSim Q B := by
    rw [← hh, hB]
    exact h
  have hker : phiSim Q (A * B⁻¹) = 1 := by
    rw [map_mul, map_inv, hab]
    exact mul_inv_cancel _
  rcases phiSim_eq_one_iff.mp hker with h1 | h2
  · have hAB : A = B := by
      have hz := congrArg (fun z => z * B) h1
      simpa [mul_assoc] using hz
    have hspan : Submodule.span (ZMod 3) {((g : V ≃ₗ[ZMod 3] V) u)} =
        Submodule.span (ZMod 3) {w} := by
      rw [← ff_commSp_reflOf hQ hgu, ← ff_commSp_reflOf hQ hw]
      exact congrArg commSp hAB
    have hmem : ((g : V ≃ₗ[ZMod 3] V) u) ∈ Submodule.span (ZMod 3) {w} := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨a, fun ha0 => hgu (by rw [← ha, ha0, zero_smul, map_zero]), ha.symm⟩
  · exfalso
    have hAeq : A = piOrth Q * B := by
      have hz := congrArg (fun z => z * B) h2
      simpa [mul_assoc] using hz
    have hdimA : invDim A = 1 := by
      simpa [invType] using congrArg Prod.fst (ff_invType_reflOf hQ hgu)
    have hdimB : invDim B = 1 := by
      simpa [invType] using congrArg Prod.fst (ff_invType_reflOf hQ (a := w) hw)
    have httB : B * B = 1 := reflOf_mul_self w hw
    have hdim' : invDim A = Module.finrank (ZMod 3) V - invDim B := by
      have h0 := congrArg Prod.fst (invType_piOrth_mul hQ httB)
      rw [← hAeq] at h0
      simpa [invType] using h0
    omega

end CFSG.OddStandard.SmallF3.Omega
