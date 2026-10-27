module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {x₁ x₂ lam tau : G}

private theorem m12_tau_sq (h : M12Rel x₁ x₂ lam tau) : tau * tau = 1 := by
  rw [← pow_two, ← h.ord_tau]
  exact pow_orderOf_eq_one tau

private theorem m12_tau_inv (h : M12Rel x₁ x₂ lam tau) : tau⁻¹ = tau :=
  inv_eq_of_mul_eq_one_right (m12_tau_sq h)

private theorem m12_tau_conj_baseGrp (h : M12Rel x₁ x₂ lam tau) :
    ∀ a ∈ baseGrp x₁ x₂, tau * a * tau⁻¹ = a⁻¹ := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.toWreathRel).1
  intro a ha
  rw [baseGrp] at ha
  induction ha using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact h.tau_x₁
      · exact h.tau_x₂
  | one => simp
  | mul x y hx hy ihx ihy =>
      change x ∈ baseGrp x₁ x₂ at hx
      change y ∈ baseGrp x₁ x₂ at hy
      calc tau * (x * y) * tau⁻¹
          = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
        _ = (x * y)⁻¹ := by
              rw [mul_inv_rev]
              exact setLike_mul_comm (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hy)
  | inv x hx ihx =>
      rw [show tau * x⁻¹ * tau⁻¹ = (tau * x * tau⁻¹)⁻¹ from by group, ihx]

private theorem m12_tau_mul_eq (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : tau * a = a⁻¹ * tau := by
  have h1 : tau * a * tau = a⁻¹ := by
    simpa [m12_tau_inv h] using m12_tau_conj_baseGrp h a ha
  calc tau * a = tau * a * (tau * tau) := by rw [m12_tau_sq h, mul_one]
    _ = (tau * a * tau) * tau := by group
    _ = a⁻¹ * tau := by rw [h1]

private theorem m12_tau_mul_inv_eq (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : tau * a⁻¹ = a * tau := by
  have h1 := m12_tau_mul_eq h (Subgroup.inv_mem _ ha)
  simpa using h1

private theorem m12_commutator_tau_left (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : ⁅a, tau⁆ = a ^ 2 := by
  have hinv : tau * a⁻¹ * tau⁻¹ = a := by
    have hmem : a⁻¹ ∈ baseGrp x₁ x₂ := Subgroup.inv_mem _ ha
    simpa using m12_tau_conj_baseGrp h a⁻¹ hmem
  rw [commutatorElement_def]
  rw [show a * tau * a⁻¹ * tau⁻¹ = a * (tau * a⁻¹ * tau⁻¹) from by group, hinv]
  exact (pow_two a).symm

private theorem m12_commutator_left_tau (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : ⁅tau, a⁆ = (a ^ 2)⁻¹ := by
  have h1 : ⁅tau, a⁆ = (⁅a, tau⁆)⁻¹ := by
    have := congrArg Inv.inv (commutatorElement_inv (g₁ := tau) (g₂ := a))
    simpa using this
  rw [h1, m12_commutator_tau_left h ha]

private theorem m12_commutator_base (h : M12Rel x₁ x₂ lam tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : ⁅a, b⁆ = 1 := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.toWreathRel).1
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact setLike_mul_comm ha hb

private theorem m12_commutator_base_tau (h : M12Rel x₁ x₂ lam tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : ⁅a, b * tau⁆ = a ^ 2 := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.toWreathRel).1
  rw [commutatorElement_mul_right_eq_mul_conj, m12_commutator_base h ha hb, one_mul,
    m12_commutator_tau_left h ha]
  have hcomm : Commute b (a ^ 2) :=
    setLike_mul_comm hb (Subgroup.pow_mem _ ha 2)
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem m12_commutator_tau_base (h : M12Rel x₁ x₂ lam tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : ⁅a * tau, b⁆ = (b ^ 2)⁻¹ := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.toWreathRel).1
  rw [commutatorElement_mul_left_eq_conj_mul, m12_commutator_left_tau h hb,
    m12_commutator_base h ha hb, mul_one]
  have hcomm : Commute a ((b ^ 2)⁻¹) :=
    setLike_mul_comm ha (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 2))
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem m12_commutator_tau_tau_left (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : ⁅a * tau, tau⁆ = a ^ 2 := by
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_self,
    m12_commutator_tau_left h ha]
  group

private theorem m12_commutator_tau_tau (h : M12Rel x₁ x₂ lam tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) :
    ⁅a * tau, b * tau⁆ = a ^ 2 * (b ^ 2)⁻¹ := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (WreathRel.baseGrp_eq h.toWreathRel).1
  rw [commutatorElement_mul_right_eq_mul_conj, m12_commutator_tau_base h ha hb,
    m12_commutator_tau_tau_left h ha]
  have hcomm : Commute b a := setLike_mul_comm hb ha
  have hcomm' : Commute b⁻¹ (a ^ 2) := (hcomm.inv_left).pow_right 2
  calc (b ^ 2)⁻¹ * b * a ^ 2 * b⁻¹
      = b⁻¹ * a ^ 2 * b⁻¹ := by group
    _ = a ^ 2 * b⁻¹ * b⁻¹ := by rw [hcomm'.eq]
    _ = a ^ 2 * (b ^ 2)⁻¹ := by group

private theorem m12_sq_mem_fourGrp (h : M12Rel x₁ x₂ lam tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : a ^ 2 ∈ fourGrp x₁ x₂ := by
  rw [WreathRel.fourGrp_eq_mho h.toWreathRel]
  exact Subgroup.subset_closure ⟨a, ha, rfl⟩

private theorem m12_mem_zpowers_tau (h : M12Rel x₁ x₂ lam tau) {z : G}
    (hz : z ∈ zpowers tau) : z = 1 ∨ z = tau := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hmod : tau ^ (k % (2 : ℤ)) = z := by
    have h1 := zpow_mod_orderOf tau k
    rw [h.ord_tau, hk] at h1
    simpa using h1
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left; rw [hk0, zpow_zero] at hmod; exact hmod.symm
  · right; rw [hk1, zpow_one] at hmod; exact hmod.symm

private def m12_tauSub (h : M12Rel x₁ x₂ lam tau) : Subgroup G where
  carrier := {g | ∃ a ∈ baseGrp x₁ x₂, g = a ∨ g = a * tau}
  one_mem' := ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
  mul_mem' := by
    rintro g g' ⟨a, ha, hga | hga⟩ ⟨b, hb, hgb | hgb⟩
    · exact ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inl (by rw [hga, hgb])⟩
    · exact ⟨a * b, Subgroup.mul_mem _ ha hb, Or.inr (by rw [hga, hgb]; group)⟩
    · exact ⟨a * b⁻¹, Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb), Or.inr (by
        rw [hga, hgb]
        rw [show a * tau * b = a * (tau * b) from by group, m12_tau_mul_eq h hb]
        group)⟩
    · exact ⟨a * b⁻¹, Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb), Or.inl (by
        rw [hga, hgb]
        calc a * tau * (b * tau) = a * (tau * b) * tau := by group
          _ = a * (b⁻¹ * tau) * tau := by rw [m12_tau_mul_eq h hb]
          _ = a * (b⁻¹ * (tau * tau)) := by group
          _ = a * b⁻¹ := by rw [m12_tau_sq h, mul_one])⟩
  inv_mem' := by
    rintro g ⟨a, ha, hga | hga⟩
    · exact ⟨a⁻¹, Subgroup.inv_mem _ ha, Or.inl (by rw [hga])⟩
    · exact ⟨a, ha, Or.inr (by
        rw [hga, mul_inv_rev, m12_tau_inv h, m12_tau_mul_inv_eq h ha])⟩

private theorem m12_le_tauSub (h : M12Rel x₁ x₂ lam tau) :
    baseGrp x₁ x₂ ⊔ zpowers tau ≤ m12_tauSub h := by
  apply sup_le
  · intro a ha
    exact ⟨a, ha, Or.inl rfl⟩
  · intro z hz
    rcases m12_mem_zpowers_tau h hz with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
    · exact ⟨1, Subgroup.one_mem _, Or.inr (by simp)⟩

private theorem m12_mem_sup_tau (h : M12Rel x₁ x₂ lam tau) {g : G}
    (hg : g ∈ baseGrp x₁ x₂ ⊔ zpowers tau) :
    ∃ a ∈ baseGrp x₁ x₂, g = a ∨ g = a * tau := by
  have := m12_le_tauSub h hg
  simpa [m12_tauSub] using this

theorem commutator_baseGrp_sup_tau_of (h : M12Rel x₁ x₂ lam tau) :
    ⁅baseGrp x₁ x₂ ⊔ zpowers tau, baseGrp x₁ x₂ ⊔ zpowers tau⁆ = fourGrp x₁ x₂ := by
  have hx₁A : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂A : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ ⊔ zpowers tau := Subgroup.mem_sup_left hx₁A
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ ⊔ zpowers tau := Subgroup.mem_sup_left hx₂A
  have htauB : tau ∈ baseGrp x₁ x₂ ⊔ zpowers tau :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  have hmem₁ : x₁ ^ 2 ∈ ⁅baseGrp x₁ x₂ ⊔ zpowers tau, baseGrp x₁ x₂ ⊔ zpowers tau⁆ := by
    have hc := Subgroup.commutator_mem_commutator hx₁B htauB
    rw [m12_commutator_tau_left h hx₁A] at hc
    exact hc
  have hmem₂ : x₂ ^ 2 ∈ ⁅baseGrp x₁ x₂ ⊔ zpowers tau, baseGrp x₁ x₂ ⊔ zpowers tau⁆ := by
    have hc := Subgroup.commutator_mem_commutator hx₂B htauB
    rw [m12_commutator_tau_left h hx₂A] at hc
    exact hc
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg g' hg'
    obtain ⟨a, ha, hga⟩ := m12_mem_sup_tau h hg
    obtain ⟨b, hb, hgb⟩ := m12_mem_sup_tau h hg'
    rcases hga with rfl | rfl <;> rcases hgb with rfl | rfl
    · rw [m12_commutator_base h ha hb]
      exact Subgroup.one_mem _
    · rw [m12_commutator_base_tau h ha hb]
      exact m12_sq_mem_fourGrp h ha
    · rw [m12_commutator_tau_base h ha hb]
      exact Subgroup.inv_mem _ (m12_sq_mem_fourGrp h hb)
    · rw [m12_commutator_tau_tau h ha hb]
      exact Subgroup.mul_mem _ (m12_sq_mem_fourGrp h ha)
        (Subgroup.inv_mem _ (m12_sq_mem_fourGrp h hb))
  · rw [fourGrp, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hmem₁
    · have hz : (x₁ * x₂) ^ 2 = (x₁ ^ 2)⁻¹ * x₂ ^ 2 := by
        rw [WreathRel.x₂_sq h.toWreathRel, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hz]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hmem₁) hmem₂

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
