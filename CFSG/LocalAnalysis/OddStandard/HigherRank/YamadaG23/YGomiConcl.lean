module

public import CFSG.GH74.GLS.IVK.Proofs2.ConjComponent
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem oddCore_eq_pPrimeCore' (Q : Type*) [Group Q] :
    CFSG.oddCore Q = CFSG.pPrimeCore 2 Q := by
  apply le_antisymm
  · apply sSup_le
    intro N hN
    exact le_sSup (show N ∈ {K : Subgroup Q | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩)
  · apply sSup_le
    intro N hN
    exact le_sSup (show N ∈ {K : Subgroup Q | K.Normal ∧ Odd (Nat.card K)} from
      ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩)

private theorem normal_le_center_or_eq_top_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hnq,
        inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = n₁ * (n₁⁻¹ * x) := by group
    have hy : y = n₂ * (n₂⁻¹ * y) := by group
    set z₁ := n₁⁻¹ * x
    set z₂ := n₂⁻¹ * y
    have c₁ := Subgroup.mem_center_iff.mp hz₁
    have c₂ := Subgroup.mem_center_iff.mp hz₂
    rw [hx, hy, commutatorElement_def]
    have e : n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by
            rw [← c₁ (n₂ * z₂), mul_assoc _ z₁, mul_inv_cancel, mul_one]
        _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
        _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [← c₂ n₁⁻¹]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

end CFSG.OddStandard.HigherRank.YamadaG23
