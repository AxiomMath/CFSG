module

public import CFSG.LargeExtraspecial.DWRed
public import CFSG.LargeExtraspecial.DWSm77Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem le_QG_of_normal_four {T : Subgroup G} (hTM : T ≤ S.M)
    (hT : ∀ m ∈ S.M, ∀ x ∈ T, m * x * m⁻¹ ∈ T) (hcard : Nat.card T = 4) : T ≤ S.QG := by
  set P : Subgroup S.M := T.subgroupOf S.M
  have hPn : P.Normal :=
    ⟨fun x hx m => mem_subgroupOf.mpr (hT m m.2 x (mem_subgroupOf.mp hx))⟩
  have hPcard : Nat.card P = 2 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, hcard]
    rfl
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hPcard
  have hPQ := S.le_of_normal P hPn hP2
  intro x hx
  exact S.mem_QG_iff.mpr ⟨hTM hx, hPQ (mem_subgroupOf.mpr hx)⟩

theorem exists_fixed_of_normal_order_four {T : Subgroup G} (hTM : T ≤ S.M)
    (hT : ∀ m ∈ S.M, ∀ x ∈ T, m * x * m⁻¹ ∈ T) (hcard : Nat.card T = 4) (hz : S.z ∈ T) :
    ∃ t ∈ T, t ∈ S.QG ∧ S.cl t ≠ 0 ∧ T = S.clPre (ZMod 2 ∙ S.cl t) ∧
      ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl t) = S.cl t := by
  have hTQ := le_QG_of_normal_four hTM hT hcard
  set W := S.clSub T with hW
  have hpre : S.clPre W = T := S.clPre_clSub hTQ hz
  have hWcard : Nat.card W = 2 := by
    have h := S.card_clPre W
    rw [hpre, hcard] at h
    omega
  have hWrank : finrank (ZMod 2) W = 1 := by
    have h := S.card_submodule W
    rw [hWcard] at h
    have := Nat.pow_right_injective le_rfl (h.symm.trans (pow_one 2).symm)
    exact this
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hWrank
    exact absurd hWrank (by norm_num)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨t, htT, htQ, rfl⟩ := S.mem_clSub_iff.mp hwW
  have hspan : W = ZMod 2 ∙ S.cl t := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hwW
    · rw [finrank_span_singleton hw0, hWrank]
  have hinv : IsMbarInvariant S (ZMod 2 ∙ S.cl t) := by
    rw [← hspan]
    intro m v hv
    obtain ⟨x, hxT, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.ρ_cl m hxQ]
    exact S.cl_mem_clSub (hT m m.2 x hxT) (S.conj_mem_QG m.2 hxQ)
  exact ⟨t, htT, htQ, hw0, by rw [← hspan, hpre], apply_eq_of_invariant_span hw0 hinv⟩

theorem eq_zero_of_fixed
    (hG1 : ∀ c ∈ S.QG, (∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z) → c = 1 ∨ c = S.z)
    {v : S.Qt} (hfix : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  refine (S.cl_eq_zero_iff hcQ).mpr (hG1 c hcQ fun m hm => ?_)
  have h := hfix ⟨m, hm⟩
  rw [S.ρ_cl ⟨m, hm⟩ hcQ] at h
  rcases (S.cl_eq_cl_iff hcQ (S.conj_mem_QG hm hcQ)).mp h.symm with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem reduction_of_noFixed
    (hG1 : ∀ c ∈ S.QG, (∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z) → c = 1 ∨ c = S.z)
    (hred : S.IsReducible) :
    ∃ W : Submodule (ZMod 2) S.Qt, IsMinimalInvariant S W ∧ W ≠ ⊤ ∧
      (∀ m ∈ S.M, ∀ x ∈ S.clPre W, m * x * m⁻¹ ∈ S.clPre W) ∧
      (IsCompl W (perp S W) ∨
        (W ≤ perp S W ∧ (∀ x ∈ S.clPre W, ∀ y ∈ S.clPre W, x * y = y * x) ∧
          ∀ x ∈ S.clPre W, x ^ 2 = 1)) := by
  obtain ⟨W, hW, htop, hnorm, hc | ⟨hiso, hsq⟩ | ⟨v, hv, rfl⟩⟩ := reduction hred
  · exact ⟨W, hW, htop, hnorm, Or.inl hc⟩
  · exact ⟨W, hW, htop, hnorm, Or.inr ⟨hiso, fun x hx y hy => commute_of_mem_clPre hiso hx hy,
      hsq⟩⟩
  · exfalso
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [QuadraticMap.map_zero] at hv
      exact absurd hv (by decide)
    have hfix := apply_eq_of_invariant_span hv0 hW.2.1
    exact hv0 (eq_zero_of_fixed hG1 hfix)

section Simple

variable [IsSimpleGroup G]

theorem not_normal_order_four_of_simple (h2 : 2 ≤ S.width) {T : Subgroup G} (hTM : T ≤ S.M)
    (hT : ∀ m ∈ S.M, ∀ x ∈ T, m * x * m⁻¹ ∈ T) (hcard : Nat.card T = 4) (hz : S.z ∈ T) :
    False := by
  obtain ⟨t, -, -, hw0, -, hfix⟩ := exists_fixed_of_normal_order_four hTM hT hcard hz
  exact hw0 (eq_zero_of_forall_ρ_apply_eq S h2 hfix)

theorem reduction_of_simple (h2 : 2 ≤ S.width) (hred : S.IsReducible) :
    ∃ W : Submodule (ZMod 2) S.Qt, IsMinimalInvariant S W ∧ W ≠ ⊤ ∧
      (∀ m ∈ S.M, ∀ x ∈ S.clPre W, m * x * m⁻¹ ∈ S.clPre W) ∧
      (IsCompl W (perp S W) ∨
        (W ≤ perp S W ∧ (∀ v ∈ W, S.q v = 0) ∧ CFSG.IsElementaryAbelian 2 (S.clPre W))) := by
  obtain ⟨W, hW, htop, hnorm, hc | ⟨hiso, -, hsq⟩⟩ :=
    reduction_of_noFixed (fun _ hc hconj => eq_one_or_z_of_forall_conj S h2 hc hconj) hred
  · exact ⟨W, hW, htop, hnorm, Or.inl hc⟩
  · have hq : ∀ v ∈ W, S.q v = 0 := by
      intro v hv
      obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
      exact (S.q_cl_eq_zero_iff hxQ).mpr (hsq x ⟨hxQ, hv⟩)
    exact ⟨W, hW, htop, hnorm, Or.inr ⟨hiso, hq, isElementaryAbelian_clPre hiso hq⟩⟩

end Simple

end CFSG.LargeExtraspecial.DW
