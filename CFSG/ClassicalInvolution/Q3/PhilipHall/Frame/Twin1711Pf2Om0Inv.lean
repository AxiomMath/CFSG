module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0

open CFSG.EvenSmallLie.OmegaEight

set_option linter.unusedSectionVars false


theorem exists_conj_sylowT_of_involution {x : Equiv.Perm (Fin 360)} (hx : x ∈ autT)
    (hx2 : orderOf x = 2) : ∃ a ∈ autT, a * x * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : autT := ⟨x, hx⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autT sylowA Q
  have h1 : x' ∈ (Q : Subgroup autT) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, coe_sylowA,
    Subgroup.mem_subgroupOf] at h1
  refine ⟨(g⁻¹ : autT), (g⁻¹ : autT).2, ?_⟩
  simpa using h1

theorem exists_type_eq {i : ℕ} (hi : i < 3) : ∃ j < 38, repTypes.getD j 0 = i := by
  interval_cases i
  · exact ⟨0, by norm_num, by decide⟩
  · exact ⟨3, by norm_num, by decide⟩
  · exact ⟨12, by norm_num, by decide⟩

theorem mainPerm_mem_omegaT {i : ℕ} (hi : i < 3) : mainPerm i ∈ omegaT := by
  obtain ⟨j, hj, hjt⟩ := exists_type_eq hi
  have h1 := conj_mainPerm hj
  rw [hjt] at h1
  have h2 : repPerm j ∈ omegaT := (repPerm_mem_omegaT_iff hj).2 (by rw [hjt]; exact hi)
  rw [← h1] at h2
  exact (conj_mem_omegaT (conjPerm_spec hj).2).2 h2

@[expose] noncomputable def xOm (i : Fin 3) : omegaT := ⟨mainPerm i, mainPerm_mem_omegaT i.2⟩

theorem om0_h1 : ∀ t : omegaT, t * t = 1 → t ≠ 1 →
    ∃ (i : Fin 3) (α : omegaT ≃* omegaT), α t = xOm i := by
  intro t ht2 ht1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x : Equiv.Perm (Fin 360) := (t : Equiv.Perm (Fin 360)) with hxdef
  have hxA : x ∈ autT := omegaT_le_autT t.2
  have hxx : x * x = 1 := congrArg Subtype.val ht2
  have hx1 : x ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  obtain ⟨a, ha, haS⟩ := exists_conj_sylowT_of_involution hxA hord
  have hord' : orderOf (a * x * a⁻¹) = 2 := by
    rw [show a * x * a⁻¹ = MulAut.conj a x from rfl, MulEquiv.orderOf_eq, hord]
  obtain ⟨j, hj, c, hc, hcj⟩ := exists_rep_of_involution haS hord'
  have hconj := conj_mainPerm hj
  set i := repTypes.getD j 0 with hi
  have hcA : c ∈ autT := sylowT_le_autT hc
  have hu : a * x * a⁻¹ ∈ omegaT := (conj_mem_omegaT ha).1 t.2
  have hrep : repPerm j ∈ omegaT := by
    have e : repPerm j = c⁻¹ * (a * x * a⁻¹) * c := by rw [hcj]; group
    rw [e]
    exact (conj_mem_omegaT (autT.inv_mem hcA)).1 hu
  have hi3 : i < 3 := (repPerm_mem_omegaT_iff hj).1 hrep
  have hcj' : conjPerm j ∈ autT := (conjPerm_spec hj).2
  have hg : (c * conjPerm j)⁻¹ * a ∈ autT :=
    autT.mul_mem (autT.inv_mem (autT.mul_mem hcA hcj')) ha
  refine ⟨⟨i, hi3⟩, autConj ⟨_, hg⟩, Subtype.ext ?_⟩
  rw [autConj_apply]
  show (c * conjPerm j)⁻¹ * a * x * ((c * conjPerm j)⁻¹ * a)⁻¹ = mainPerm i
  have e1 : (c * conjPerm j)⁻¹ * a * x * ((c * conjPerm j)⁻¹ * a)⁻¹ =
      (conjPerm j)⁻¹ * (c⁻¹ * (a * x * a⁻¹) * c) * conjPerm j := by group
  have e2 : c⁻¹ * (a * x * a⁻¹) * c = repPerm j := by rw [hcj]; group
  rw [e1, e2, ← hconj]
  group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0
