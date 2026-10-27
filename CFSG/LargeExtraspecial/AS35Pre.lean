module

public import CFSG.LargeExtraspecial.S10FourB
public import CFSG.RankThree.Literature.FSmithInvolution
public import CFSG.RankThree.Literature.FSmithTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
include S in
theorem exists_mul_ne_mul : ∃ x y : G, x * y ≠ y * x := by
  by_contra! hall
  have hzc : S.zQ ∈ _root_.commutator S.Q := by
    rw [S.extraspecial.2.1]
    exact S.zQ_mem_center
  have hbot : _root_.commutator S.Q = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (Subtype.ext (hall _ _))
  rw [hbot, Subgroup.mem_bot] at hzc
  exact S.zQ_ne_one hzc

theorem exists_conj_mem_M_ne [IsSimpleGroup G] :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra! hiso
  obtain ⟨N, hNn, hNodd, hN⟩ := S10.exists_odd_normal_of_isolated S.z S.z_ne_one S.z_mul_z
    fun g hg => hiso g (mem_centralizer_singleton_iff.mpr hg)
  rcases hNn.eq_bot_or_eq_top with hbot | htop
  · have hcen : S.z ∈ center G := by
      rw [mem_center_iff]
      intro g
      have h := hN g
      rw [hbot, mem_bot, mul_inv_eq_one] at h
      calc g * S.z = g * S.z * g⁻¹ * g := by group
        _ = S.z * g := by rw [h]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · rw [hc, mem_bot] at hcen
      exact S.z_ne_one hcen
    · obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
      exact hxy ((mem_center_iff.mp (hc ▸ mem_top x : x ∈ center G)) y).symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := S.orderOf_z ▸ orderOf_dvd_natCard S.z
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

omit [Finite G] in
theorem conj_not_mem_QG (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {g : G}
    (hne : g * S.z * g⁻¹ ≠ S.z) : g * S.z * g⁻¹ ∉ S.QG :=
  fun h => hne (hW g h)

theorem not_forall_eq_transvection [IsSimpleGroup G] (hn : 3 ≤ S.width) (m : S.M) (v : S.Qt)
    (hv : S.q v = 1) :
    ¬ ∀ u : S.Qt, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + polar S.q u v • v := by
  classical
  intro hm
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hz₀ : ∀ g : S.M, g * S.zM = S.zM * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have hz₀1 : S.zM ≠ 1 := fun h => S.z_ne_one (congrArg Subtype.val h)
  have hdim : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width
  obtain ⟨a, F, ha, haa, haF, hz₀F, hF2, hCF, hFa, he, hc⟩ :=
    exists_smith_subgroup S.extraspecial S.normal hz₀ hz₀1 S.zM_mem_Q S.centralizer_le
      (hdim ▸ (by omega : 3 ≤ 2 * S.width)) hv hm
  let ϕ : S.M →* Multiplicative (ZMod 2) := (dicksonHom S.q S.q_nondegenerate).comp S.ρ
  have hV : ∀ g : G, ϕ.transfer g = 1 := by
    have := (ϕ.transfer).normal_ker
    rcases Subgroup.Normal.eq_bot_or_eq_top (ϕ.transfer).ker with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
      apply hxy
      apply (MonoidHom.ker_eq_bot_iff _).mp h
      rw [map_mul, map_mul, mul_comm]
    · intro g
      have hg : g ∈ (ϕ.transfer).ker := by
        rw [h]
        exact mem_top g
      exact hg
  have hϕa : ϕ a ≠ 1 := by
    have hρa : ((S.ρ a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        CFSG.ClassicalGroups.Orthogonal.reflect S.q v := eq_reflect_of_apply hv ha
    change dicksonHom S.q S.q_nondegenerate (S.ρ a) ≠ 1
    rw [dicksonHom_apply, hρa, finrank_commSpace_reflect S.q_nondegenerate hv, Nat.cast_one, Ne,
      ofAdd_eq_one]
    exact one_ne_zero
  refine smith_transfer ϕ S.z_ne_one S.z_mul_z (F := F.map S.M.subtype) (a := (a : G))
    (map_subtype_le F) (hF2.map _) ?_ (mem_map_of_mem _ haF) (congrArg Subtype.val haa) hϕa
    (hV a) ?_ ?_ ?_
  · intro c hc
    have hcz : c * S.z = S.z * c := hc S.z (mem_map_of_mem _ hz₀F)
    have hcM : c ∈ S.M := mem_centralizer_singleton_iff.mpr hcz
    rcases hCF ⟨c, hcM⟩ (fun f hf => Subtype.ext (hc f (mem_map_of_mem _ hf))) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro f ⟨f', hf', rfl⟩
    rcases hFa f' hf' with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · obtain ⟨e, heF, he⟩ := he
    exact ⟨e, mem_map_of_mem _ heF, congrArg Subtype.val he⟩
  · obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, h3⟩ := hc
    exact ⟨c₁, mem_map_of_mem _ hc₁, c₂, mem_map_of_mem _ hc₂, congrArg Subtype.val h1,
      congrArg Subtype.val h2, congrArg Subtype.val h3⟩

theorem two_le_finrank_commSpace [IsSimpleGroup G] (hn : 3 ≤ S.width) {x : S.M} (hx : x ∉ S.Q) :
    2 ≤ finrank (ZMod 2) (commSpace ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra! hlt
  have h1 : ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h =>
    hx (S.mem_Q_of_ρ_eq_one (Subtype.ext h))
  have hsum := finrank_commSpace_add_finrank_fixSpace ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rcases eq_one_or_eq_transvection_of_finrank_fixSpace S.q_nondegenerate (S.ρ x).2
      (by omega) with h | ⟨c, hc, hxc, -, -⟩
  · exact h1 h
  · exact S.not_forall_eq_transvection hn x c hc hxc

end Setting

end CFSG.LargeExtraspecial
