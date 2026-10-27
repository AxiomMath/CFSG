module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fk_fr_aux_smul_eq_zero_or_eq (hQ : Q.Nondegenerate) {u v : V} (hu : Q u ≠ 0)
    (hv : Q v ≠ 0) {c : ZMod 3}
    (hcv : ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) v = c • v) :
    QuadraticMap.polar Q u v = 0 ∨ reflOf Q u hu = reflOf Q v hv := by
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  have haa : ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V)
      (((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) v) = v := by
    have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) v)
      (reflOf_mul_self u hu)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, Subgroup.coe_one] at h
    simpa using h
  have hc2 : c * c = 1 := by
    have h := congrArg (fun x => ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) x) hcv
    rw [map_smul] at h
    rw [haa] at h
    rw [hcv] at h
    rw [smul_smul] at h
    have h2 : (c * c) • v = v := h.symm
    have hsub : (c * c - 1) • v = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsub with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv0
  have hccases : c = 1 ∨ c = -1 :=
    (by decide : ∀ x : ZMod 3, x * x = 1 → x = 1 ∨ x = -1) c hc2
  have hkey : (1 - c) • v = (QuadraticMap.polar Q u v / Q u) • u := by
    have h := hcv
    rw [coe_reflOf_apply u hu v] at h
    have h1 : v - c • v = (QuadraticMap.polar Q u v / Q u) • u := by
      rw [← h]; abel
    rwa [sub_smul, one_smul]
  rcases hccases with hc | hc
  · left
    rw [hc] at hkey
    have h0 : (1 - (1 : ZMod 3)) = 0 := by ring
    rw [h0, zero_smul] at hkey
    rcases smul_eq_zero.mp hkey.symm with hk | hu0
    · rcases div_eq_zero_iff.mp hk with hp | hq
      · exact hp
      · exact absurd hq hu
    · exact absurd hu0 (fun h0 => hu (by rw [h0, map_zero]))
  · right
    rw [hc] at hkey
    have h2 : (1 - (-1 : ZMod 3)) = -1 := by decide
    rw [h2, neg_one_smul] at hkey
    have hk_ne : QuadraticMap.polar Q u v / Q u ≠ 0 := by
      intro hk0
      rw [hk0, zero_smul] at hkey
      exact hv0 (neg_eq_zero.mp hkey)
    have hv_span : v ∈ Submodule.span (ZMod 3) {u} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨-(QuadraticMap.polar Q u v / Q u), ?_⟩
      exact (neg_smul (QuadraticMap.polar Q u v / Q u) u).trans
        (neg_eq_iff_eq_neg.mp hkey).symm
    have hu_span : u ∈ Submodule.span (ZMod 3) {v} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨-(QuadraticMap.polar Q u v / Q u)⁻¹, ?_⟩
      have hu_eq : u = (QuadraticMap.polar Q u v / Q u)⁻¹ • (-v) := by
        rw [hkey, smul_smul, inv_mul_cancel₀ hk_ne, one_smul]
      have hneg : (-(QuadraticMap.polar Q u v / Q u)⁻¹) • v =
          (QuadraticMap.polar Q u v / Q u)⁻¹ • (-v) := by
        rw [neg_smul, smul_neg]
      exact hneg.trans hu_eq.symm
    have hspan_eq : Submodule.span (ZMod 3) {v} = Submodule.span (ZMod 3) {u} := by
      apply le_antisymm
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv_span
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hu_span
    exact eq_of_commSp_eq hQ (reflOf_mul_self u hu) (reflOf_mul_self v hv) (by
      rw [ff_commSp_reflOf hQ hu, ff_commSp_reflOf hQ hv, hspan_eq.symm])

theorem fk_fr_polar_eq_zero (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hcomm : phiSim Q (reflOf Q u hu) * phiSim Q (reflOf Q v hv) =
      phiSim Q (reflOf Q v hv) * phiSim Q (reflOf Q u hu))
    (hne : phiSim Q (reflOf Q u hu) ≠ phiSim Q (reflOf Q v hv)) :
    QuadraticMap.polar Q u v = 0 := by
  have hker : phiSim Q (reflOf Q u hu * reflOf Q v hv * (reflOf Q u hu)⁻¹ *
      (reflOf Q v hv)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rcases (phiSim_eq_one_iff.mp hker) with h1 | hpi
  · have hcomm' : reflOf Q u hu * reflOf Q v hv =
        reflOf Q v hv * reflOf Q u hu := by
      have h : (reflOf Q u hu * reflOf Q v hv) *
          (reflOf Q v hv * reflOf Q u hu)⁻¹ = 1 := by
        rw [mul_inv_rev, ← h1]
        group
      exact mul_inv_eq_one.mp h
    have hbv : ((reflOf Q v hv : OGroup Q) : V ≃ₗ[ZMod 3] V) v = -v :=
      (mem_commSp_iff (reflOf_mul_self v hv)).mp (by
        rw [ff_commSp_reflOf hQ hv]
        exact Submodule.mem_span_singleton_self v)
    have happ : ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V)
        (((reflOf Q v hv : OGroup Q) : V ≃ₗ[ZMod 3] V) v) =
        ((reflOf Q v hv : OGroup Q) : V ≃ₗ[ZMod 3] V)
        (((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) v) := by
      have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) v) hcomm'
      simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using h
    have hav_mem : ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) v ∈
        Submodule.span (ZMod 3) {v} := by
      rw [← ff_commSp_reflOf hQ hv, mem_commSp_iff (reflOf_mul_self v hv)]
      rw [← happ, hbv, map_neg]
    obtain ⟨c, hcv⟩ := Submodule.mem_span_singleton.mp hav_mem
    rcases fk_fr_aux_smul_eq_zero_or_eq hQ hu hv hcv.symm with hp | hab
    · exact hp
    · exact absurd (congrArg (phiSim Q) hab) hne
  · have hconj : reflOf Q u hu * reflOf Q v hv * (reflOf Q u hu)⁻¹ =
        piOrth Q * reflOf Q v hv := by
      rw [← hpi]
      group
    have h2 := two_mul_invDim_of_conj hQ (t := reflOf Q v hv) (s := reflOf Q u hu)
      (reflOf_mul_self v hv) hconj
    have hb1 : invDim (reflOf Q v hv) = 1 := by
      simp only [invDim]
      rw [ff_commSp_reflOf hQ hv]
      exact finrank_span_singleton (fun h => hv (by rw [h, map_zero]))
    rw [hb1, hdim] at h2
    omega

end CFSG.OddStandard.SmallF3.Omega
