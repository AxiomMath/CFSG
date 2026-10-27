module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F12Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F12T0
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Act

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem exists_central_conj_t0 :
    ∃ z : Q3, z ∈ E0 ∧ z ≠ 1 ∧ z ≠ t0 ∧ ∀ r ∈ Q0, r * z = z * r := by
  obtain ⟨c, hc, h0, h1, -⟩ := exists_mem_Zq_smul_base_triple x0_mem_plane x2_mem_plane
    x1_mem_plane x0_ne_x2 x0_ne_x1 x1_ne_x2.symm
  have hcinv0 : c⁻¹ • x0 = x0 := by rw [inv_smul_eq_iff]; exact h0.symm
  have hcinv2 : c⁻¹ • x2 = x1 := by rw [inv_smul_eq_iff]; exact h1.symm
  have hconj : ∀ r ∈ (Q0 : Set Q3), c⁻¹ * r * c ∈ L0 := by
    intro r hr
    obtain ⟨hr0, hr1, hr2⟩ := mem_Q0_iff_of_fix.1 hr
    have hx0 : (c⁻¹ * r * c) • x0 = x0 := by
      rw [mul_smul, mul_smul, h0, hr0, hcinv0]
    have hx1 : (c⁻¹ * r * c) • x1 = x1 := by
      rw [mul_smul, mul_smul, h1, hr2, hcinv2]
    rw [mem_L0_iff]
    exact ⟨by rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]; exact hx0, hx1⟩
  refine ⟨c * t0 * c⁻¹, conj_mem_E0 hc t0 t0_mem_E0, ?_, ?_, ?_⟩
  · intro h
    apply t0_ne_one
    calc t0 = c⁻¹ * (c * t0 * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · exact conj_t0_ne_t0 hc h0 h1
  · intro r hr
    exact mul_conj_comm_of_conj_mem (P := (L0 : Set Q3)) (Q := (Q0 : Set Q3))
      (t := t0) (c := c) (fun p hp => mul_comm_t0_of_mem_L0 hp) hconj hr

theorem mem_center_of_planeXAct_fixes
    {q : ↥Q0}
    (h : ∀ y : Fin 891, planeXAct q y = y) : q ∈ Subgroup.center ↥Q0 := by
  have hE0 : (q : Q3) ∈ E0 := mem_E0_of_planeXAct_fixes h
  have hfix : ∀ i : Fin 891, (q : Q3) • planeX i = planeX i := planeXAct_forall_eq_iff.1 h
  obtain ⟨z, hzE0, hz1, hzt0, hzc⟩ := exists_central_conj_t0
  have ht0c : ∀ r ∈ Q0, r * t0 = t0 * r := fun r hr => mul_comm_t0_of_mem_L0 (Q0_le_L0 hr)
  let S : Set Q3 := {e : Q3 | e ∈ E0 ∧ ∀ i : Fin 891, e • planeX i = planeX i}
  have hSfin : S.Finite := finite_fix_planes_E0
  have hcardS : S.ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact card_fix_planes_E0_le
  have h1S : (1 : Q3) ∈ S := ⟨E0.one_mem, fun i => by simp⟩
  have haS : t0 ∈ S :=
    ⟨t0_mem_E0, fun i => smul_planeX_eq_self_of_central t0_mem_E0 ht0c i⟩
  have hbS : z ∈ S := ⟨hzE0, fun i => smul_planeX_eq_self_of_central hzE0 hzc i⟩
  have habS : t0 * z ∈ S :=
    ⟨E0.mul_mem t0_mem_E0 hzE0, fun i => by
      rw [mul_smul, smul_planeX_eq_self_of_central hzE0 hzc i,
        smul_planeX_eq_self_of_central t0_mem_E0 ht0c i]⟩
  have hqS : (q : Q3) ∈ S := ⟨hE0, hfix⟩
  obtain ⟨h1a, h1b, h1ab, hab, haab, hbab⟩ :=
    ne_of_sq_eq_one (sq_eq_one_of_mem_E0 t0_mem_E0) t0_ne_one hz1 hzt0.symm
  have hcases : (q : Q3) = 1 ∨ (q : Q3) = t0 ∨ (q : Q3) = z ∨ (q : Q3) = t0 * z :=
    eq_or_eq_or_eq_or_eq_of_ncard_le_four hSfin hcardS (a := (1 : Q3)) (b := t0) (c := z)
      (d := t0 * z) h1S haS hbS habS h1a h1b h1ab hab haab hbab hqS
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  rcases hcases with hq | hq | hq | hq
  · rw [hq]; group
  · rw [hq]; exact mul_comm_t0_of_mem_L0 (Q0_le_L0 g.2)
  · rw [hq]; exact hzc (g : Q3) g.2
  · rw [hq]
    calc (g : Q3) * (t0 * z) = ((g : Q3) * t0) * z := by rw [mul_assoc]
      _ = (t0 * (g : Q3)) * z := by rw [mul_comm_t0_of_mem_L0 (Q0_le_L0 g.2)]
      _ = t0 * ((g : Q3) * z) := by rw [mul_assoc]
      _ = t0 * (z * (g : Q3)) := by rw [hzc (g : Q3) g.2]
      _ = (t0 * z) * (g : Q3) := by rw [← mul_assoc]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
