module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74

theorem sylow_conj_mem {G : Type} [Group G] [Finite G] (S T : Sylow 2 G) :
    ∃ h : G, ∀ x : G, x ∈ (T : Subgroup G) ↔ ∃ s ∈ (S : Subgroup G), h * s * h⁻¹ = x := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S T
  refine ⟨h, fun x => ?_⟩
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def]

theorem exists_conj_mem_of_rank {G : Type} [Group G] [Finite G] {z : G} (hz : IsCentralInvolution z)
    (hrank : SectionalTwoRankLE G 4) {E : Subgroup G} (hE : IsElementaryAbelian 2 ↥E)
    (hE16 : Nat.card ↥E = 16) : ∃ g : G, g * z * g⁻¹ ∈ E := by
  obtain ⟨hz2, S, hzS, hSz⟩ := hz
  have hEp : IsPGroup 2 ↥E := IsElementaryAbelian.isPGroup 2 ↥E
  obtain ⟨T, hET⟩ := hEp.exists_le_sylow
  obtain ⟨h, hh⟩ := sylow_conj_mem S T
  refine ⟨h, ?_⟩
  by_contra hnot
  set t : G := h * z * h⁻¹ with ht
  have htT : t ∈ (T : Subgroup G) := (hh t).mpr ⟨z, hzS, rfl⟩
  have htc : ∀ x ∈ (T : Subgroup G), x * t = t * x := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := (hh x).mp hx
    have := hSz s hs
    calc h * s * h⁻¹ * (h * z * h⁻¹) = h * (s * z) * h⁻¹ := by group
      _ = h * (z * s) * h⁻¹ := by rw [this]
      _ = h * z * h⁻¹ * (h * s * h⁻¹) := by group
  have ht2 : t ^ 2 = 1 := by
    have : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hz2])
    calc t ^ 2 = h * z ^ 2 * h⁻¹ := by simp [ht, pow_two, mul_assoc]
      _ = 1 := by rw [this]; group
  have hEc : ∀ x ∈ E, x * t = t * x := fun x hx => htc x (hET hx)
  have hE' : IsElementaryAbelian 2 ↥(E ⊔ zpowers t) := by
    have := hE
    have := IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) ht2
    refine IsElementaryAbelian.sup_of_le_centralizer fun y hy => mem_centralizer_iff.2
      fun x hx => ?_
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (hEc x hx) m).eq
  have hlt : E < E ⊔ zpowers t := by
    refine lt_of_le_of_ne le_sup_left fun heq => hnot ?_
    rw [heq]
    exact mem_sup_right (mem_zpowers t)
  have hcard : 2 ^ 4 < Nat.card ↥(E ⊔ zpowers t) := by
    have := Subgroup.card_lt_of_lt hlt
    omega
  have := hrank.card_le_of_elementary (E ⊔ zpowers t)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hE')
  omega

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
