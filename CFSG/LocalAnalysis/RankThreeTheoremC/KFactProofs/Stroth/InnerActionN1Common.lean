module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

theorem not_isMulCommutative_of_noncomm_pSubgroup {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {H : Subgroup K} (hH : IsPGroup p H) {a b : K} (ha : a ∈ H) (hb : b ∈ H)
    (hab : a * b ≠ b * a) {S : Subgroup K} (hS : IsPGroup p S) (hSi : ¬ p ∣ S.index) :
    ¬ IsMulCommutative S := by
  intro hcomm
  let P : Sylow p K := hS.toSylow hSi
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  have hmem : ∀ x ∈ H, g * x * g⁻¹ ∈ S := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ ((g • Q : Sylow p K) : Subgroup K) := by
      rw [Sylow.coe_subgroup_smul]
      have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup K) (hHQ hx)
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [hg] at h1
    exact h1
  have hc := (hcomm.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
  have hc' : g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := congrArg Subtype.val hc
  apply hab
  calc a * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [hc']
    _ = b * a := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
