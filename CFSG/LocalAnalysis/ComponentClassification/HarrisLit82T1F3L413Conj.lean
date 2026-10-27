module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413Model
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410b

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.L413

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem finrank_perp_frame_eight (fr : Frame (quadPlus 4 K)) :
    Module.finrank K fr.perp = 4 := by
  have h := finrank_perp_add_four fr
  rw [finrank_V8] at h
  omega

theorem exists_conj_inv4_mul (hodd : Odd (Nat.card K)) {x : spinGroup (quadPlus 4 K)}
    (hx : orderOf x = 2) (hxZ : x ∉ center (spinGroup (quadPlus 4 K))) :
    ∃ g : spinGroup (quadPlus 4 K), ∃ c ∈ center (spinGroup (quadPlus 4 K)),
      x = g * (inv4 K 1 * c) * g⁻¹ := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : (polarBilin (quadPlus 4 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 K
  have hQ := nondegenerate_quadPlus 4 K
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have : Group.IsPerfect (spinGroup (quadPlus 4 K)) := isPerfect_spinGroup_quadPlus (by norm_num)
  have hdet := CFSG.ClassicalInvolution.Asc77.T7H.det_spinAction_eq_one x
  have h4dvd := CFSG.ClassicalInvolution.Asc77.T7H.four_dvd_finrank_minusSp_of_sq_one h2 hQ' hxx
    hdet
  have hii : spinAction (quadPlus 4 K) x * spinAction (quadPlus 4 K) x = 1 := by
    rw [← map_mul, hxx, map_one]
  have hne : spinAction (quadPlus 4 K) x ≠ 1 := fun h => hxZ (ker_spinAction_le_center _ h)
  have hne' : ¬ ∀ v, spinAction (quadPlus 4 K) x v = -v := fun h => hxZ (by
    rw [center_eq_scalarSpin]
    exact mem_of_spinAction_eq_smul (c := -1) fun v => by rw [h v, neg_one_smul])
  have ha0 : Module.finrank K (minusSp (spinAction (quadPlus 4 K) x)) ≠ 0 := by
    intro h0
    have hbot : minusSp (spinAction (quadPlus 4 K) x) = ⊥ := Submodule.finrank_eq_zero.mp h0
    refine hne (LinearEquiv.ext fun v => ?_)
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq h2 hii v
    have hw0 : w = 0 := by
      have : w ∈ (⊥ : Submodule K (Fin 4 ⊕ Fin 4 → K)) := hbot ▸ hw
      exact (Submodule.mem_bot _).mp this
    rw [hw0, add_zero]
    exact mem_plusSp.mp hu
  have ha8 : Module.finrank K (minusSp (spinAction (quadPlus 4 K) x)) ≠ 8 := by
    intro h8
    have htop : minusSp (spinAction (quadPlus 4 K) x) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h8, finrank_V8])
    exact hne' fun v => mem_minusSp.mp (htop ▸ Submodule.mem_top)
  have hle : Module.finrank K (minusSp (spinAction (quadPlus 4 K) x)) ≤ 8 :=
    finrank_V8 (K := K) ▸ Submodule.finrank_le _
  have hdim : Module.finrank K (minusSp (spinAction (quadPlus 4 K) x)) = 4 := by
    obtain ⟨k, hk⟩ := h4dvd
    omega
  obtain ⟨fr, hfr⟩ := exists_frame_La_neg_one_eq hodd hQ' hxx hdim
  obtain ⟨g, hg⟩ := exists_spin_conj hodd hQ' (pl K 1) fr
    (by rw [finrank_perp_frame_eight]; omega)
  have hθ : spinAction (quadPlus 4 K) (g * inv4 K 1 * g⁻¹) = spinAction (quadPlus 4 K) x := by
    rw [map_mul, map_mul, map_inv, inv4, spinAction_rt, ← hg (-1), hfr]
  have hk : (g * inv4 K 1 * g⁻¹)⁻¹ * x ∈ (spinAction (quadPlus 4 K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
  rcases (mem_ker_spinAction_iff _ hQ _).mp hk with h | h
  · exact ⟨g, 1, one_mem _, by rw [mul_one]; exact (inv_mul_eq_one.mp h).symm⟩
  · refine ⟨g, neg8 K, neg8_mem_center, ?_⟩
    have hc := (commute_negOneS (n := 4) (by norm_num) g⁻¹).eq
    calc x = g * inv4 K 1 * g⁻¹ * neg8 K := inv_mul_eq_iff_eq_mul.mp h
      _ = g * inv4 K 1 * (g⁻¹ * neg8 K) := mul_assoc _ _ _
      _ = g * inv4 K 1 * (neg8 K * g⁻¹) := by rw [← hc]
      _ = g * (inv4 K 1 * neg8 K) * g⁻¹ := by simp only [mul_assoc]

end CFSG.ComponentClassification.HarrisLit.T1.L413
