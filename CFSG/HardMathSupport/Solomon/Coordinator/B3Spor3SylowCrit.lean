module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Phi

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem gLAPPrimeCoreOf_three_eq_bot_of_sylow {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (S : ℕ → Subgroup G)
    (hS : ∀ p : ℕ, p.Prime → p ∣ Nat.card C → p ≠ 3 →
      S p ≤ C ∧ Nat.card (S p) = p ^ (Nat.card C).factorization p ∧
        ∀ s ∈ S p, orderOf s = p → ∃ u ∈ C, 3 ∣ orderOf (s * (u * s * u⁻¹))) :
    GLAPPrimeCoreOf 3 C = ⊥ := by
  have hconj : ∀ a y : G, orderOf (a * y * a⁻¹) = orderOf y := fun a y => by
    have := MulEquiv.orderOf_eq (MulAut.conj a) y
    rwa [MulAut.conj_apply] at this
  apply gLAPPrimeCoreOf_three_eq_bot_of_conj_product
  intro w hw hwp hw3
  have hpd : orderOf w ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hw
  obtain ⟨hSC, hcard, hwit⟩ := hS (orderOf w) hwp hpd hw3
  have : Fact (orderOf w).Prime := ⟨hwp⟩
  have hS' : Nat.card ((S (orderOf w)).subgroupOf C) =
      orderOf w ^ (Nat.card C).factorization (orderOf w) := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  let P : Sylow (orderOf w) C := Sylow.ofCard _ hS'
  let w' : C := ⟨w, hw⟩
  have hpg : IsPGroup (orderOf w) (Subgroup.zpowers w') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  have hwQ : w' ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers w')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hwQ
  have hsP : ((MulAut.conj g)⁻¹ • w' : C) ∈ (P : Subgroup C) := hwQ
  set s' : C := (MulAut.conj g)⁻¹ • w' with hs'
  have hs'e : s' = g⁻¹ * w' * g := by
    rw [hs']
    simp [MulAut.smul_def, MulAut.conj_symm_apply]
  have hsS : (s' : G) ∈ S (orderOf w) := hsP
  have hso : orderOf (s' : G) = orderOf w := by
    rw [hs'e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have := hconj ((g : G)⁻¹) w
    rwa [inv_inv] at this
  obtain ⟨u, huC, hdiv⟩ := hwit _ hsS hso
  refine ⟨(g : G) * u * (g : G)⁻¹, C.mul_mem (C.mul_mem g.2 huC) (C.inv_mem g.2), ?_⟩
  have hw' : w = (g : G) * (s' : G) * (g : G)⁻¹ := by
    rw [hs'e]
    simp [w', mul_assoc]
  have e : w * ((g : G) * u * (g : G)⁻¹ * w * ((g : G) * u * (g : G)⁻¹)⁻¹) =
      (g : G) * ((s' : G) * (u * (s' : G) * u⁻¹)) * (g : G)⁻¹ := by
    rw [hw']
    group
  rw [e, hconj]
  exact hdiv

end CFSG.HardMathSupport.Solomon.Coordinator

end
