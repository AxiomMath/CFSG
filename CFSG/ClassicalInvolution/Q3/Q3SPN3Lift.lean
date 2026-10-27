module

public import CFSG.ClassicalInvolution.Q3.Q3TLKAut

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3SPN3

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement

section Eichler

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eichler_pow_three [Finite F] (hF3 : Nat.card F = 3) (u w : V) :
    eichler Q u w ^ 3 = 1 := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hw : polar Q u w = 0 := h.2
    have h2w : polar Q u (w + w) = 0 := by rw [polar_add_right, hw, add_zero]
    have h3F : (3 : F) = 0 := by
      have : Fintype F := Fintype.ofFinite F
      have h := FiniteField.cast_card_eq_zero F
      rw [← Nat.card_eq_fintype_card, hF3] at h
      exact_mod_cast h
    have h3 : w + w + w = 0 := by
      have : (3 : F) • w = 0 := by rw [h3F, zero_smul]
      rw [← this]
      module
    calc eichler Q u w ^ 3 = eichler Q u w * eichler Q u w * eichler Q u w := by
          rw [pow_succ, pow_two]
      _ = eichler Q u (w + w) * eichler Q u w := by rw [eichler_mul hw hw]
      _ = eichler Q u (w + w + w) := eichler_mul h2w hw
      _ = 1 := by rw [h3, eichler_zero_right]
  · rw [eichler_of_not h, one_pow]

end Eichler

section Lift

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} [Finite F]

theorem elemOn_le_map_fixedGroup3 (hF3 : Nat.card F = 3)
    (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c) (α : spinGroup Q ≃* spinGroup Q)
    {w : V ≃ₗ[F] V} (hθw : ∀ y, spinAction Q (α y) = w * spinAction Q y * w⁻¹) {S : Submodule F V}
    (hw : ∀ n ∈ elemOn Q S, w * n = n * w) :
    elemOn Q S ≤ (fixedGroup α).map (spinAction Q) := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hP : elemOn Q S ≤ (spinAction Q).range := by
    rw [hrange]
    exact elemOn_le_elementaryGroup
  have hcentral : ∀ s ∈ (elemOn Q S).comap (spinAction Q),
      s⁻¹ * α s ∈ Subgroup.center (spinGroup Q) := by
    intro s hs
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθw]
    have h1 := hw _ (Subgroup.mem_comap.mp hs)
    calc (spinAction Q s)⁻¹ * (w * spinAction Q s * w⁻¹)
        = (spinAction Q s)⁻¹ * (spinAction Q s * w) * w⁻¹ := by rw [← h1]; group
      _ = 1 := by group
  rw [elemOn, Subgroup.closure_le]
  rintro g ⟨u, v, hu, hv, hQu, hpolar, rfl⟩
  have hgP : eichler Q u v ∈ elemOn Q S := eichler_mem_elemOn hu hv
  obtain ⟨s, hs, hαs⟩ := Q3TLK.exists_fixed_lift_of_pow_three (spinAction Q) hker hZ3 α hP hcentral
    hgP (eichler_pow_three hF3 u v)
  exact ⟨s, mem_fixedGroup.mpr hαs, hs⟩

theorem elemOn_le_map_centralizer3 (hF3 : Nat.card F = 3)
    (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c) {g : spinGroup Q}
    {S : Submodule F V} (hs : spinAction Q g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ y ∈ S, spinAction Q g y = y) :
    elemOn Q S ≤ (Subgroup.centralizer ({g} : Set (spinGroup Q))).map (spinAction Q) := by
  have key := elemOn_le_map_fixedGroup3 hF3 hrange hZ3 (MulAut.conj g) (w := spinAction Q g)
    (S := S) (fun y => by simp [MulAut.conj_apply, map_mul, map_inv])
    (fun n hn => comm_of_scalar_elemOn hs (by simp : (1 : F) * 1 = 1)
      (fun x hx => by rw [hfix x hx, one_smul]) hn)
  have hfg : fixedGroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set (spinGroup Q)) := by
    ext y
    rw [mem_fixedGroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rwa [hfg] at key

end Lift

end CFSG.ClassicalInvolution.Q3.Q3SPN3
