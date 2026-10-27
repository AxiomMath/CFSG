module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {S : Type} [Group S]

private theorem chevToolsY_center_eq_bot [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hmem : a ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp hmem b).symm

theorem chevToolsY_mulAut_conj_conj (β : MulAut S) (s : S) :
    β * MulAut.conj s * β⁻¹ = MulAut.conj (β s) := by
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem chevToolsY_conj_injective (hS : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro s t hst
  have hy : ∀ y : S, s * y * s⁻¹ = t * y * t⁻¹ := by
    intro y
    have h := DFunLike.congr_fun hst y
    simpa only [MulAut.conj_apply] using h
  have hcentral : t⁻¹ * s ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have key : t⁻¹ * (s * g * s⁻¹) * t = g := by
      rw [hy g]
      group
    have hconj : t⁻¹ * s * g * (t⁻¹ * s)⁻¹ = g := by
      calc t⁻¹ * s * g * (t⁻¹ * s)⁻¹ = t⁻¹ * (s * g * s⁻¹) * t := by group
        _ = g := key
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  rw [hS] at hcentral
  have hw : t⁻¹ * s = 1 := Subgroup.mem_bot.mp hcentral
  calc s = t * (t⁻¹ * s) := by group
    _ = t := by rw [hw, mul_one]

theorem chevToolsY_centralizer_inner_eq_bot (hS : Subgroup.center S = ⊥) :
    Subgroup.centralizer ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro β hβ
  rw [Subgroup.mem_centralizer_iff] at hβ
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro s
  show β s = s
  have hmem : MulAut.conj s ∈ ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) :=
    SetLike.mem_coe.mpr (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  have hc := hβ (MulAut.conj s) hmem
  have key : β * MulAut.conj s * β⁻¹ = MulAut.conj s := by
    rw [← hc, mul_inv_cancel_right]
  have h' : MulAut.conj (β s) = MulAut.conj s :=
    (chevToolsY_mulAut_conj_conj β s).symm.trans key
  exact chevToolsY_conj_injective hS h'

theorem chevToolsY_inner_inf_centralizer (hS : Subgroup.center S = ⊥) (β : MulAut S) :
    inner S ⊓ Subgroup.centralizer ({β} : Set (MulAut S)) =
      (fixSubgroup β).map (MulAut.conj : S →* MulAut S) := by
  ext x
  constructor
  · rintro ⟨hxinner, hxcent⟩
    obtain ⟨s, rfl⟩ := hxinner
    have hxcent' : MulAut.conj s ∈ Subgroup.centralizer ({β} : Set (MulAut S)) := hxcent
    rw [Subgroup.mem_centralizer_singleton_iff] at hxcent'
    have key : β * MulAut.conj s * β⁻¹ = MulAut.conj s := by
      rw [← hxcent', mul_inv_cancel_right]
    have h' : MulAut.conj (β s) = MulAut.conj s :=
      (chevToolsY_mulAut_conj_conj β s).symm.trans key
    have hfix : β s = s := chevToolsY_conj_injective hS h'
    exact Subgroup.mem_map.mpr
      ⟨s, (CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup).mpr hfix, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hfix : β s = s := (CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup).mp hs
    have key : β * MulAut.conj s * β⁻¹ = MulAut.conj s := by
      rw [chevToolsY_mulAut_conj_conj, hfix]
    refine Subgroup.mem_inf.mpr
      ⟨MonoidHom.mem_range.mpr ⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp key).symm

theorem chevToolsY_isSimpleGroup_inner [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) :
    IsSimpleGroup ↥(inner S) :=
  MulEquiv.isSimpleGroup
    (MonoidHom.ofInjective (chevToolsY_conj_injective (chevToolsY_center_eq_bot hnonab))).symm

theorem chevToolsY_nonabelian_inner [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) :
    ∃ a b : ↥(inner S), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hnonab
  have hinj := chevToolsY_conj_injective (chevToolsY_center_eq_bot ⟨a, b, hab⟩)
  refine ⟨(MonoidHom.ofInjective hinj) a, (MonoidHom.ofInjective hinj) b, fun h => hab ?_⟩
  apply (MonoidHom.ofInjective hinj).injective
  rw [map_mul, map_mul]
  exact h

theorem chevToolsY_isCatalogGroup_inner [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (h : CFSG.Open.IsCatalogGroup S) : CFSG.Open.IsCatalogGroup ↥(inner S) := by
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨(MonoidHom.ofInjective (chevToolsY_conj_injective
    (chevToolsY_center_eq_bot hnonab))).symm.trans f⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
