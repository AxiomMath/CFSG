module

public import CFSG.LargeExtraspecial.AS35HSixEleven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_conj_mem_M_of_le {X : Subgroup G} (hMX : S.M ≤ X) {a : G} (ha : a ∈ X)
    (ha2 : orderOf a = 2) : ∃ x ∈ X, x * a * x⁻¹ ∈ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -, hPM⟩ := S.exists_sylow_le_M
  let PX : Sylow 2 X := P.subtype (hPM.trans hMX)
  have hp : IsPGroup 2 (zpowers (⟨a, ha⟩ : X)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ha2, pow_one])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X R PX
  have hmem : x * ⟨a, ha⟩ * x⁻¹ ∈ (PX : Subgroup X) := by
    rw [← hx, Sylow.smul_def, Sylow.pointwise_smul_def]
    exact ⟨⟨a, ha⟩, hR (Subgroup.mem_zpowers _), by simp⟩
  rw [Sylow.coe_subtype, mem_subgroupOf] at hmem
  refine ⟨x, x.2, hPM ?_⟩
  simpa using hmem

end Setting

namespace S14

@[expose] def AschbacherSixElevenFusionMStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) →
    (∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) →
    ∀ (hQX : S.QG ≤ S.BStab) (hMX : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab),
      S.BStab ≠ ⊤ → (S.restrict S.BStab hQX hMX).AschTwo →
        ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∈ S.BSet

theorem aschbacherSixElevenFusionCoreStmt_of_fusionM (h : AschbacherSixElevenFusionMStmt) :
    AschbacherSixElevenFusionCoreStmt := by
  intro G _ _ S ih hS h65 h69 h610 hQX hMX' hX hA2 g hg
  have hS4 := hS.sixFour
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS4 hS.hSet_nonempty
  have hzB : S.z ∈ S.BSet := by
    have := S.self_mem_BAt hS4 ⟨t, ht⟩ 1
    simpa using this
  have h69' : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet := fun g hg => (h69 g hg).le
  have hmem : ∀ x, x ∈ S.BStab ↔ x * S.z * x⁻¹ ∈ S.BSet := fun x =>
    S.mem_BStab_iff hS4 h69' hzB
  have hMX : S.M ≤ S.BStab := fun m hm => (hmem m).mpr (by rw [S.conj_z_of_mem_M hm]; exact hzB)
  have ha2 : orderOf (g * S.z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, S.orderOf_z]
  obtain ⟨x, hxX, hxM⟩ := S.exists_conj_mem_M_of_le hMX hg ha2
  have hk : (x * g) * S.z * (x * g)⁻¹ ∈ S.M := by
    rw [show (x * g) * S.z * (x * g)⁻¹ = x * (g * S.z * g⁻¹) * x⁻¹ by group]
    exact hxM
  have hkB := h G S ih hS h65 h69 h610 hQX hMX' hX hA2 (x * g) hk
  have hgX : g ∈ S.BStab := by
    have h1 := mul_mem (inv_mem hxX) ((hmem (x * g)).mpr hkB)
    rwa [inv_mul_cancel_left] at h1
  exact (hmem g).mp hgX

end S14

end CFSG.LargeExtraspecial
