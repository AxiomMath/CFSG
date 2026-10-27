module

import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace TenThreeOTwoZ

theorem mem_pCoreOf_of_le {X Y : Subgroup G} (hYX : Y ≤ X) {y : G} (hy : y ∈ Y)
    (hyX : y ∈ pCoreOf 2 X) : y ∈ pCoreOf 2 Y := by
  set N : Subgroup ↥Y := (pCoreOf 2 X).subgroupOf Y
  have hXn := normal_pCoreOf_subgroupOf X
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hXn.conj_mem ⟨n, hYX n.2⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨g, hYX g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩
  have hP : IsPGroup 2 N := by
    intro n
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨(n : ↥Y), Subgroup.mem_subgroupOf.mp n.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hle : N ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hN, hP⟩
  exact ⟨⟨y, hy⟩, hle (Subgroup.mem_subgroupOf.mpr hyX), rfl⟩

theorem mem_pCoreOf_of_symThree {I₀ L : Subgroup G} (hIL : I₀ ≤ L)
    (e : ↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)) {x : G} (hx : x ∈ I₀)
    (hxL : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : x ∈ pCoreOf 2 I₀ := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)
  have hcomm : ∀ t : ↥I₀, π t * π ⟨x, hx⟩ = π ⟨x, hx⟩ * π t := by
    intro t
    have hc : x * (t : G) * x⁻¹ * (t : G)⁻¹ ∈ pCoreOf 2 I₀ :=
      mem_pCoreOf_of_le hIL (I₀.mul_mem (I₀.mul_mem (I₀.mul_mem hx t.2) (I₀.inv_mem hx))
        (I₀.inv_mem t.2)) (hxL t (hIL t.2))
    obtain ⟨c, hc', hcc⟩ := hc
    have hc1 : π c = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    have hceq : c = ⟨x, hx⟩ * t * (⟨x, hx⟩ : ↥I₀)⁻¹ * t⁻¹ := Subtype.ext (by simpa using hcc)
    rw [hceq, map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
    have := congrArg (· * π t * π ⟨x, hx⟩) hc1
    simp only [one_mul, inv_mul_cancel_right, mul_assoc] at this
    rw [← this]
    group
  have h1 : e (π ⟨x, hx⟩) = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro k
    symm
    obtain ⟨q, rfl⟩ := e.surjective k
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I₀) q
    show e (π t) * e (π ⟨x, hx⟩) = e (π ⟨x, hx⟩) * e (π t)
    rw [← map_mul e, ← map_mul e, hcomm t]
  have h2 : π ⟨x, hx⟩ = 1 := by
    rw [← map_one e.symm, ← h1, MulEquiv.symm_apply_apply]
  exact coe_mem_pCoreOf_two_of_mk_eq_one _ h2

end TenThreeOTwoZ

end CFSG.LocalAnalysis.RankThreeTheoremC
