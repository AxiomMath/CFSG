module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG

variable {H : Type*} [Group H]

theorem pCore_comap_le_sup_sylow [Finite H] {p : ℕ} [Fact p.Prime]
    {K : Subgroup H} [K.Normal] (T : Sylow p H) :
    (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) ≤ K ⊔ (T : Subgroup H) := by
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  let N : Subgroup (H ⧸ K) := pCore p (H ⧸ K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hNp : IsPGroup p N := pCore_isPGroup
  haveI : N.Normal := pCore_normal
  let Tq : Sylow p (H ⧸ K) := Sylow.mapSurjective (f := π) hπ T
  have hcoe : (Tq : Subgroup (H ⧸ K)) = (T : Subgroup H).map π :=
    Sylow.coe_mapSurjective (f := π) hπ T
  have hle : N ≤ Tq := IsPGroup.le_sylow_of_normal hNp Tq
  calc N.comap π ≤ Tq.comap π := Subgroup.comap_mono hle
    _ = ((T : Subgroup H).map π).comap π := by rw [hcoe]
    _ = K ⊔ (T : Subgroup H) := QuotientGroup.comap_map_mk' K (T : Subgroup H)

end CFSG

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

theorem centralizerMod_iSup_right {ι : Type*} [Nonempty ι] {V₁ X : Subgroup G}
    (U : ι → Subgroup G) (hU : ∀ i, U i ≤ Subgroup.normalizer (V₁ : Set G)) :
    centralizerMod V₁ X (⨆ i, U i) = ⨅ i, centralizerMod V₁ X (U i) := by
  refine le_antisymm (le_iInf fun i => centralizerMod_anti_right X (le_iSup U i)) ?_
  intro x hx
  rw [Subgroup.mem_iInf] at hx
  obtain ⟨hxX, hxN, -⟩ := (hx (Classical.arbitrary ι))
  let Cx : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (V₁ : Set G) ∧ x * y * x⁻¹ * y⁻¹ ∈ V₁}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁N, hy₁⟩ ⟨hy₂N, hy₂⟩
        refine ⟨Subgroup.mul_mem _ hy₁N hy₂N, ?_⟩
        have h1 : y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp hy₁N _).mp hy₂
        have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
            (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact V₁.mul_mem hy₁ h1
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
        have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp (V₁.inv_mem hy)
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hUC : ∀ i, U i ≤ Cx := fun i y hy => ⟨hU i hy, (hx i).2.2 y hy⟩
  have hsup : (⨆ i, U i) ≤ Cx := iSup_le hUC
  exact ⟨hxX, hxN, fun y hy => (hsup hy).2⟩

end CFSG.Quasithin
