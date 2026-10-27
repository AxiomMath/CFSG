module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Cfg

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

theorem quot_FP_data {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    ⁅F.map (QuotientGroup.mk' (zpowers a)), F.map (QuotientGroup.mk' (zpowers a))⁆ =
        F.map (QuotientGroup.mk' (zpowers a)) ∧
    (∀ f ∈ F.map (QuotientGroup.mk' (zpowers a)),
      (∀ g ∈ F.map (QuotientGroup.mk' (zpowers a)), f * g = g * f) → f = 1) ∧
    P.map (QuotientGroup.mk' (zpowers a)) ≤ F.map (QuotientGroup.mk' (zpowers a)) ∧
    Nat.card ↥(P.map (QuotientGroup.mk' (zpowers a))) = 64 ∧
    IsA8Type ↥(P.map (QuotientGroup.mk' (zpowers a))) := by
  let π : Y →* Y ⧸ zpowers a := QuotientGroup.mk' (zpowers a)
  have hker : ∀ x ∈ F, π x = 1 → x = 1 := by
    intro x hxF hx
    have hxZ : x ∈ zpowers a := by
      rw [← QuotientGroup.ker_mk' (zpowers a), MonoidHom.mem_ker]
      exact hx
    have hmem : x ∈ F ⊓ zpowers a := ⟨hxF, hxZ⟩
    rwa [h.F_inf, Subgroup.mem_bot] at hmem
  have hinj_of_le : ∀ H : Subgroup Y, H ≤ F → Function.Injective (π.subgroupMap H) := by
    intro H hHF x y hxy
    have h1 : π (x : Y) = π (y : Y) := by
      simpa using congrArg Subtype.val hxy
    apply Subtype.ext
    have h2 : π ((x : Y) * (y : Y)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hmem : (x : Y) * (y : Y)⁻¹ ∈ F :=
      F.mul_mem (hHF x.2) (F.inv_mem (hHF y.2))
    exact mul_inv_eq_one.mp (hker _ hmem h2)
  let eP : P ≃* P.map π :=
    MulEquiv.ofBijective (π.subgroupMap P)
      ⟨hinj_of_le P h.P_le, MonoidHom.subgroupMap_surjective π P⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← Subgroup.map_commutator, h.F_perfect]
  ·
    intro f hf hcomm
    obtain ⟨x, hxF, rfl⟩ := Subgroup.mem_map.mp hf
    have hx1 : x = 1 := by
      apply h.F_center x hxF
      intro g hgF
      have h1 : π x * π g = π g * π x :=
        hcomm (π g) (Subgroup.mem_map_of_mem π hgF)
      have h2 : π (x * g) = π (g * x) := by rw [map_mul, map_mul, h1]
      have hmem : (x * g) * (g * x)⁻¹ ∈ F :=
        F.mul_mem (F.mul_mem hxF hgF) (F.inv_mem (F.mul_mem hgF hxF))
      have h3 : π ((x * g) * (g * x)⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hker _ hmem h3)
    rw [hx1, map_one]
  · exact Subgroup.map_mono h.P_le
  · rw [← Nat.card_congr eP.toEquiv, h.P_card]
  · obtain ⟨Q, ⟨eQ⟩⟩ := h.P_A8
    exact ⟨Q, ⟨eP.symm.trans eQ⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
