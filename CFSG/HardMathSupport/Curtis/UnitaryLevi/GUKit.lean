module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.IsotropicNotOrthogonal
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LinearGroups

variable {f : ℕ} {K : Type*} [Field K] [Finite K] (hK : UnitaryFieldData 2 f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)
  {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
  (hself : dualPoly hK.bar a = a) [Fact (Irreducible a)]
include H ha hself

omit [Finite K] hself [Fact (Irreducible a)] in
open scoped Classical in
theorem apply_eq_add_of_trivial_off (g : LinearMap.GeneralLinearGroup K V)
    (hg : ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ a →
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) (v : V) :
    (g : Module.End K V) v = (g : Module.End K V) (primaryProjection (x : Module.End K V) a v) +
      (v - primaryProjection (x : Module.End K V) a v) := by
  have hsq := H.squarefree
  have hv := eq_sum_primaryProjection hsq v
  have h1 : (g : Module.End K V) v = ∑ b ∈ primaryFactors (x : Module.End K V),
      (g : Module.End K V) (primaryProjection (x : Module.End K V) b v) := by
    conv_lhs => rw [hv]
    rw [map_sum]
  rw [h1, ← Finset.add_sum_erase _ _ ha]
  congr 1
  have h2 : v - primaryProjection (x : Module.End K V) a v =
      ∑ b ∈ (primaryFactors (x : Module.End K V)).erase a,
        primaryProjection (x : Module.End K V) b v := by
    have hv2 := hv
    rw [← Finset.add_sum_erase _ _ ha] at hv2
    rw [sub_eq_iff_eq_add']
    exact hv2
  rw [h2]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact hg b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb) _
    (primaryProjection_mem hsq (Finset.mem_of_mem_erase hb) v)

theorem primaryProjection_eq_zero_of_selfDual {W : Submodule K V}
    (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W)
    (hI : ∀ w' : primaryComponent (x : Module.End K V) a, w' ≠ 0 →
      ∃ u : primaryComponent (x : Module.End K V) a,
        selfDualForm hK H ha hself u u = 0 ∧ selfDualForm hK H ha hself u w' ≠ 0)
    {w : V} (hw : w ∈ W) : primaryProjection (x : Module.End K V) a w = 0 := by
  classical
  by_contra hne
  have hsq := H.squarefree
  have hE := unitaryFieldData_adjoinRoot hK (a := a)
  have hsymm := selfDualForm_isSymm hK H ha hself
  have hw₁ : primaryProjection (x : Module.End K V) a w ∈
      primaryComponent (x : Module.End K V) a := primaryProjection_mem hsq ha w
  set w' : primaryComponent (x : Module.End K V) a := ⟨_, hw₁⟩ with hw'
  have hw'0 : w' ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨u, huu, huw⟩ := hI w' hw'0
  set γ0 := selfDualForm hK H ha hself u w' with hγ0
  have hmove : ∀ c ∈ (unitaryFieldData_adjoinRoot hK (a := a)).traceZero,
      (((c * γ0) • u : primaryComponent (x : Module.End K V) a) : V) ∈ W := by
    intro c hc
    have hγ := (hermitian_unitary_transvection hE hsymm huu).2.1 c hc
    set γ := hermTransvectionGL (selfDualForm hK H ha hself) huu c
    set g := (selfDualFactorEquiv hK H ha hself).symm ⟨γ, sesqSpecialUnitaryGroup_le _ hγ⟩
    have hg1 : (selfDualFactorEquiv hK H ha hself g :
        sesqUnitaryGroup (selfDualForm hK H ha hself)) = ⟨γ, sesqSpecialUnitaryGroup_le _ hγ⟩ :=
      MulEquiv.apply_symm_apply _ _
    have hdet := det_eq_one_of_selfDual hK H ha hself g (by rw [hg1]; exact hγ)
    have hgU := mem_unitaryCentralizer.mp g.2.1
    have hgw := hC g (mem_sesqSpecialUnitaryGroup.mpr ⟨hgU.1, hdet⟩) hgU.2 w hw
    have hgoff : ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ a →
        ∀ v ∈ primaryComponent (x : Module.End K V) b,
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v :=
      fun b hb hba v hv => g.2.2 b hb (by simpa using hba) v hv
    have hgw' := apply_eq_add_of_trivial_off hK H ha
      (g : LinearMap.GeneralLinearGroup K V) hgoff w
    have hga : ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (primaryProjection (x : Module.End K V) a w) =
        ((w' + (c * γ0) • u : primaryComponent (x : Module.End K V) a) : V) := by
      rw [← blockApply_selfDualFactorEquiv hK H ha hself g _ hw₁, hg1]
      change (((hermTransvection (selfDualForm hK H ha hself) u c) w' :
        primaryComponent (x : Module.End K V) a) : V) = _
      rw [hermTransvection_apply]
    rw [hga] at hgw'
    rw [hgw'] at hgw
    have h1 := W.sub_mem hgw hw
    have h2 : ((w' + (c * γ0) • u : primaryComponent (x : Module.End K V) a) : V) +
        (w - primaryProjection (x : Module.End K V) a w) - w =
        (((c * γ0) • u : primaryComponent (x : Module.End K V) a) : V) := by
      rw [Submodule.coe_add]
      have : ((w' : primaryComponent (x : Module.End K V) a) : V) =
          primaryProjection (x : Module.End K V) a w := rfl
      rw [this]
      abel
    rwa [h2] at h1
  have hbarE : ∀ z : AdjoinRoot a, (unitaryFieldData_adjoinRoot hK (a := a)).bar
      ((unitaryFieldData_adjoinRoot hK (a := a)).bar z) = z :=
    (unitaryFieldData_adjoinRoot hK (a := a)).bar_bar
  have hdecomp : ∀ y ∈ primaryComponent (x : Module.End K V) a,
      B w y = B (w' : V) y := by
    intro y hy
    rw [B_eq_sum H w y, Finset.sum_eq_single a]
    · rw [hself, primaryProjection_of_mem hsq ha hy]
    · intro b hb hba
      have hne : a ≠ dualPoly hK.bar b := by
        intro hab
        apply hba
        have := dualPoly_dualPoly_of_mem H hb
        rw [← hab, hself] at this
        exact this.symm
      rw [primaryProjection_of_mem_ne hsq (dualPoly_mem_primaryFactors H hb) ha hne hy, map_zero]
    · intro h'
      exact absurd ha h'
  have hpair : ∀ c ∈ (unitaryFieldData_adjoinRoot hK (a := a)).traceZero,
      Algebra.trace K (AdjoinRoot a)
        (c * (γ0 * (unitaryFieldData_adjoinRoot hK (a := a)).bar γ0)) = 0 := by
    intro c hc
    have hy := hWt w hw _ (hmove c hc)
    rw [hdecomp _ (((c * γ0) • u : primaryComponent (x : Module.End K V) a)).2] at hy
    have h1 := trace_selfDualForm hK H ha hself w' u (c * γ0)
    have h2 : selfDualForm hK H ha hself w' u =
        (unitaryFieldData_adjoinRoot hK (a := a)).bar γ0 :=
      (hsymm.eq u w').symm
    rw [h2] at h1
    rw [← mul_assoc, h1]
    exact hy
  have hγ00 : γ0 ≠ 0 := huw
  have hN0 : γ0 * (unitaryFieldData_adjoinRoot hK (a := a)).bar γ0 ≠ 0 :=
    mul_ne_zero hγ00 (fun h0 => hγ00 ((unitaryFieldData_adjoinRoot hK (a := a)).bar.injective
      (h0.trans (map_zero _).symm)))
  set N := γ0 * (unitaryFieldData_adjoinRoot hK (a := a)).bar γ0 with hNdef
  have hbarN : (unitaryFieldData_adjoinRoot hK (a := a)).bar N = N := by
    rw [hNdef, map_mul, hbarE, mul_comm]
  have : CharP K 2 := hK.charP
  have hcharE : CharP (AdjoinRoot a) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot a)).injective 2
  have hc : N⁻¹ ∈ (unitaryFieldData_adjoinRoot hK (a := a)).traceZero := by
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_inv₀, hbarN]
    exact CharTwo.add_self_eq_zero _
  have h1 := hpair N⁻¹ hc
  rw [inv_mul_cancel₀ hN0, ← map_one (algebraMap K (AdjoinRoot a)),
    Algebra.trace_algebraMap, finrank_adjoinRoot] at h1
  have hodd := odd_natDegree_of_selfDual hK (coeff_zero_ne_zero_of_mem_primaryFactors hsq ha) hself
  obtain ⟨k, hk⟩ := hodd
  rw [hk, nsmul_one] at h1
  push_cast at h1
  rw [CharTwo.two_eq_zero, zero_mul, zero_add] at h1
  exact one_ne_zero h1

theorem primaryProjection_eq_zero_of_two_le {W : Submodule K V}
    (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W)
    (hdim : 2 ≤ Module.finrank (AdjoinRoot a) (primaryComponent (x : Module.End K V) a))
    {w : V} (hw : w ∈ W) : primaryProjection (x : Module.End K V) a w = 0 :=
  primaryProjection_eq_zero_of_selfDual hK H ha hself hWt hC
    (fun _ hw' => exists_isotropic_not_orthogonal (unitaryFieldData_adjoinRoot hK (a := a))
      (selfDualForm_isSymm hK H ha hself) (selfDualForm_separatingLeft hK H ha hself) hdim hw')
    hw

end CFSG.HardMathSupport.Curtis.UnitaryLevi
