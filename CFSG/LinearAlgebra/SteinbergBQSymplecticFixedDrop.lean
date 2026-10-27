module

public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.LinearAlgebra

open Module
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup)

theorem symplectic_small_rank_fixed_space_drop {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (b : LinearMap.BilinForm (ZMod 2) V) (hb : b.Nondegenerate)
    (_halt : b.IsAlt) (E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    [IsElementaryAbelian 2 E] (hEb : E ≤ bilinIsometryGroup b) (hE1 : E ≠ ⊥) {k : ℕ}
    (hk : Nat.card E = 2 ^ k) (hk3 : k ≤ 3)
    (hrank : k = 3 → ∃ e ∈ E, e ≠ 1 ∧
      finrank (ZMod 2) (LinearMap.range ((e : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 2) :
    ∃ B ≤ E, B.relIndex E ≤ 4 ∧
      {v : V | ∀ g ∈ E, (g : V →ₗ[ZMod 2] V) v = v} ⊂
        {v : V | ∀ g ∈ B, (g : V →ₗ[ZMod 2] V) v = v} := by
  classical
  have hmoved : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V, g ≠ 1 →
      ∃ v, (g : V →ₗ[ZMod 2] V) v ≠ v := by
    intro g hg
    by_contra hcon
    push Not at hcon
    exact hg (Units.ext (LinearMap.ext hcon))
  rcases Nat.lt_or_ge k 3 with hk2 | hk3'
  ·
    refine ⟨⊥, bot_le, ?_, ⟨fun v _ g hg => ?_, fun h => ?_⟩⟩
    · rw [Subgroup.relIndex_bot_left, hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    · rw [Subgroup.mem_bot] at hg
      rw [hg]
      rfl
    · obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
      obtain ⟨v, hv⟩ := hmoved g fun h => hg1 (Subtype.ext h)
      refine hv (h (fun g' hg' => ?_) g g.2)
      rw [Subgroup.mem_bot] at hg'
      rw [hg']
      rfl
  · have hk3'' : k = 3 := le_antisymm hk3 hk3'
    obtain ⟨e, heE, he1, herank⟩ := hrank hk3''
    by_contra hcon
    push Not at hcon
    obtain ⟨U, hU⟩ : ∃ U : Submodule (ZMod 2) V,
        ∀ v, v ∈ U ↔ ∀ g ∈ E, (g : V →ₗ[ZMod 2] V) v = v :=
      ⟨{ carrier := {v | ∀ g ∈ E, (g : V →ₗ[ZMod 2] V) v = v}
         add_mem' := fun hv hw g hg => by
           rw [map_add, hv g hg, hw g hg]
         zero_mem' := fun g _ => map_zero _
         smul_mem' := fun c v hv g hg => by
           rw [map_smul, hv g hg] }, fun v => Iff.rfl⟩
    have hfix : ∀ s ∈ E, s ≠ 1 → ∀ v, (s : V →ₗ[ZMod 2] V) v = v → v ∈ U := by
      intro s hs hs1 v hv
      have hs2 : s ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian s hs
      have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
      have hle : Subgroup.zpowers s ≤ E := (Subgroup.zpowers_le).2 hs
      have hidx : (Subgroup.zpowers s).relIndex E = 4 := by
        have h1 := Subgroup.card_mul_index ((Subgroup.zpowers s).subgroupOf E)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hord,
          hk, hk3''] at h1
        change 2 * (Subgroup.zpowers s).relIndex E = 2 ^ 3 at h1
        omega
      have h := hcon _ hle (by rw [hidx])
      have hsub : {v : V | ∀ g ∈ E, (g : V →ₗ[ZMod 2] V) v = v} ⊆
          {v : V | ∀ g ∈ Subgroup.zpowers s, (g : V →ₗ[ZMod 2] V) v = v} :=
        fun w hw g hg => hw g (hle hg)
      have hsup : {v : V | ∀ g ∈ Subgroup.zpowers s, (g : V →ₗ[ZMod 2] V) v = v} ⊆
          {v : V | ∀ g ∈ E, (g : V →ₗ[ZMod 2] V) v = v} := by
        by_contra hns
        exact h ⟨hsub, hns⟩
      have hvz : ∀ g ∈ Subgroup.zpowers s, (g : V →ₗ[ZMod 2] V) v = v := by
        have hstab : Subgroup.zpowers s ≤
            MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) V) v :=
          (Subgroup.zpowers_le).2 (MulAction.mem_stabilizer_iff.2 hv)
        exact fun g hg => MulAction.mem_stabilizer_iff.1 (hstab hg)
      exact (hU v).2 (hsup hvz)
    have hker : LinearMap.ker ((e : V →ₗ[ZMod 2] V) - LinearMap.id) = U := by
      ext v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact ⟨hfix e heE he1 v, fun hv => (hU v).1 hv e heE⟩
    have hUdim : finrank (ZMod 2) V ≤ finrank (ZMod 2) U + 2 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ((e : V →ₗ[ZMod 2] V) - LinearMap.id)
      rw [hker] at h1
      omega
    have hperp : finrank (ZMod 2) (b.orthogonal U) ≤ 2 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hb]
      omega
    obtain ⟨x₀, hx₀⟩ := hmoved e he1
    have hmem : ∀ s ∈ E, (s : V →ₗ[ZMod 2] V) x₀ - x₀ ∈ b.orthogonal U := by
      intro s hs
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have h1 := mem_bilinIsometryGroup.1 (hEb hs) u x₀
      rw [(hU u).1 hu s hs] at h1
      rw [map_sub, h1, sub_self]
    let F : E → b.orthogonal U := fun s =>
      ⟨((s : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x₀ - x₀, hmem s s.2⟩
    have hFinj : Function.Injective F := by
      intro s t hst
      have h1 : ((s : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x₀ =
          ((t : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x₀ :=
        sub_left_injective (congrArg Subtype.val hst)
      by_contra hne
      have hne' : (t : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * s ≠ 1 := fun h =>
        hne (Subtype.ext ((inv_mul_eq_one.1 h).symm))
      have h2 : (((t : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * s :
          LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x₀ = x₀ := by
        rw [Units.val_mul, Module.End.mul_apply, h1, ← Module.End.mul_apply, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Module.End.one_apply]
      have h3 := hfix _ (E.mul_mem (E.inv_mem t.2) s.2) hne' x₀ h2
      exact hx₀ ((hU x₀).1 h3 e heE)
    have : Finite V := Module.finite_of_finite (ZMod 2)
    have h1 := Nat.card_le_card_of_injective F hFinj
    rw [hk, hk3'', Module.natCard_eq_pow_finrank (K := ZMod 2) (V := b.orthogonal U),
      Nat.card_zmod] at h1
    have h2 : 2 ^ finrank (ZMod 2) (b.orthogonal U) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) hperp
    omega

end CFSG.LinearAlgebra
