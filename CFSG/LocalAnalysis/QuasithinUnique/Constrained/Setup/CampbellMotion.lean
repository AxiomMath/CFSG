module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMnorm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Motion

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem tr_one {S₀ : Subgroup G} {α : S₀ ≃* S₀} {Y : Subgroup G} : tr S₀ α 1 Y = aimg S₀ α Y := by
  unfold tr; rw [cj_one]

theorem mem_conj_of_normal_subgroupOf {S₀ Y : Subgroup G} (hn : (Y.subgroupOf S₀).Normal)
    {s x : G} (hs : s ∈ S₀) (hx : x ∈ Y) (hxS : x ∈ S₀) : s * x * s⁻¹ ∈ Y := by
  have := hn.conj_mem ⟨x, hxS⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
  exact Subgroup.mem_subgroupOf.mp this

omit [Field k] in
theorem maxElem_cj_of_le {S₀ A : Subgroup G} (g : G) (hA : IsMaxElemAbelian S₀ A)
    (hA' : A ≤ cj S₀ g) : IsMaxElemAbelian (cj S₀ g) A := by
  refine ⟨hA', hA.2.1, fun B hB hBe => ?_⟩
  have h1 : cj B g⁻¹ ≤ S₀ := by
    have := cj_mono (g := g⁻¹) hB
    rwa [cj_inv_cj] at this
  have h2 := maxElem_card_le hA h1 (isElemAbelian_cj hBe g⁻¹)
  rwa [card_cj] at h2

omit [Field k] in
theorem isElemAbelian_Vmod : CFSG.Open.IsElemAbelian 2 (Vmod G) :=
  isElemAbelian_iff.mpr ⟨fun _ ha _ hb => Ecore_commute (Vmod_le_Ecore ha) (Vmod_le_Ecore hb),
    fun _ ha => Vmod_sq ha⟩

omit [Field k] in
theorem isElemAbelian_Zfix : CFSG.Open.IsElemAbelian 2 (Zfix S) :=
  isElemAbelian_mono isElemAbelian_Vmod inf_le_left

omit [Field k] in
theorem isElemAbelian_Fcore : CFSG.Open.IsElemAbelian 2 (Fcore G) := by
  refine isElemAbelian_iff.mpr ⟨?_, fun a ha => (mem_centerTorsion_iff.mp ha).2.2⟩
  intro a ha b hb
  exact (mem_centerTorsion_iff.mp hb).2.1 a (mem_centerTorsion_iff.mp ha).1

omit [Field k] in
theorem Fcore_commute_thompsonJ_core {f y : G} (hf : f ∈ Fcore G)
    (hy : y ∈ thompsonJ (CFSG.pCore 2 G)) : y * f = f * y :=
  (mem_centerTorsion_iff.mp hf).2.1 y hy

omit [Field k] in
theorem aimg_Fcore_normal_mem [Finite G] (α : (S : Subgroup G) ≃* (S : Subgroup G)) {s x : G}
    (hs : s ∈ (S : Subgroup G)) (hx : x ∈ aimg (S : Subgroup G) α (Fcore G)) :
    s * x * s⁻¹ ∈ aimg (S : Subgroup G) α (Fcore G) := by
  have hn : ((Fcore G).subgroupOf (S : Subgroup G)).Normal := inferInstance
  exact mem_conj_of_normal_subgroupOf (normal_subgroupOf_aimg Fcore_le_sylow hn) hs hx (aimg_le hx)

omit [Field k] in
theorem aimg_Zfix_central (α : (S : Subgroup G) ≃* (S : Subgroup G)) {s z : G}
    (hs : s ∈ (S : Subgroup G)) (hz : z ∈ aimg (S : Subgroup G) α (Zfix S)) : s * z = z * s := by
  obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hz
  have h1 : ((α.symm ⟨s, hs⟩ : (S : Subgroup G)) : G) * y = y * (α.symm ⟨s, hs⟩ : (S : Subgroup G)) :=
    IsSeed.Zfix_central hy (α.symm ⟨s, hs⟩).2
  have h2 : (α.symm ⟨s, hs⟩ : (S : Subgroup G)) * y = y * (α.symm ⟨s, hs⟩ : (S : Subgroup G)) :=
    Subtype.ext h1
  have h3 : α (α.symm ⟨s, hs⟩) * α y = α y * α (α.symm ⟨s, hs⟩) := by
    rw [← map_mul, ← map_mul, h2]
  rw [α.apply_symm_apply] at h3
  exact congrArg Subtype.val h3

omit [Field k] in
theorem aimg_Zfix_le_sylow (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Zfix S) ≤ (S : Subgroup G) := aimg_le

omit [Field k] in
theorem isElemAbelian_aimg_Zfix (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    CFSG.Open.IsElemAbelian 2 (aimg (S : Subgroup G) α (Zfix S)) :=
  isElemAbelian_aimg α isElemAbelian_Zfix

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem adm_Fcore : Adm (S : Subgroup G) (Fcore G) := by
  obtain ⟨A, hA⟩ := exists_maxElem (S : Subgroup G)
  exact ⟨_, (h.isMaxElemAbelian_core_sup_Fcore hA).2, le_sup_right⟩

theorem adm_core_of_adm {Y : Subgroup G} (hY : Adm (S : Subgroup G) Y)
    (hYQ : Y ≤ CFSG.pCore 2 G) : Adm (CFSG.pCore 2 G) Y := by
  obtain ⟨A, hA, hYA⟩ := hY
  obtain ⟨A', hA', hle, -⟩ := h.exists_core_max hA
  exact ⟨A', hA', fun x hx => hle ⟨hYA hx, hYQ hx⟩⟩

theorem adm_sylow_of_adm_core {Y : Subgroup G} (hY : Adm (CFSG.pCore 2 G) Y) :
    Adm (S : Subgroup G) Y := by
  obtain ⟨A, hA, hYA⟩ := hY
  exact ⟨A, h.max_core_facts.1 A hA, hYA⟩

theorem isMaxElemAbelian_cj_of_core {B : Subgroup G} (hB : IsMaxElemAbelian (CFSG.pCore 2 G) B)
    (g : G) : IsMaxElemAbelian (cj (S : Subgroup G) g) B := by
  refine maxElem_cj_of_le g (h.max_core_facts.1 B hB) ?_
  have : cj (CFSG.pCore 2 G) g ≤ cj (S : Subgroup G) g := cj_mono (core_le_sylow S)
  rw [cj_eq_self_of_normal] at this
  exact hB.1.trans this

theorem adm_cj_of_adm_core {Y : Subgroup G} (hY : Adm (CFSG.pCore 2 G) Y) (g : G) :
    Adm (cj (S : Subgroup G) g) Y := by
  obtain ⟨A, hA, hYA⟩ := hY
  exact ⟨A, h.isMaxElemAbelian_cj_of_core hA g, hYA⟩

theorem aimg_Fcore_rep (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Fcore G) = aimg (S : Subgroup G) α (Vmod G) ⊔
      (aimg (S : Subgroup G) α (Fcore G) ⊓ Subgroup.centralizer (Fcore G : Set G)) := by
  have := h.tr_Fcore_rep α 1 (Y := Fcore G) (by rw [cj_one]; exact h.adm_Fcore)
  simpa only [tr_one] using this

theorem aimg_Fcore_le_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    aimg (S : Subgroup G) α (Fcore G) ≤ CFSG.pCore 2 G := by
  calc aimg (S : Subgroup G) α (Fcore G)
      = aimg (S : Subgroup G) α (Vmod G) ⊔
        (aimg (S : Subgroup G) α (Fcore G) ⊓ Subgroup.centralizer (Fcore G : Set G)) :=
        h.aimg_Fcore_rep α
    _ ≤ CFSG.pCore 2 G := sup_le hV fun x hx =>
        h.sylow_inf_centralizer_Fcore_le ⟨aimg_le hx.1, hx.2⟩

theorem adm_core_aimg_Fcore (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    Adm (CFSG.pCore 2 G) (aimg (S : Subgroup G) α (Fcore G)) := by
  obtain ⟨A, hA, hFA⟩ := h.adm_Fcore
  exact h.adm_core_of_adm ⟨_, isMaxElemAbelian_aimg α hA, aimg_mono hFA⟩
    (h.aimg_Fcore_le_core α hV)

theorem aimg_Fcore_le_thompsonJ_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    aimg (S : Subgroup G) α (Fcore G) ≤ thompsonJ (CFSG.pCore 2 G) := by
  obtain ⟨A, hA, hle⟩ := h.adm_core_aimg_Fcore α hV
  exact hle.trans (maxElem_le_thompsonJ hA)

theorem commutator_thompsonJ_aimg_Fcore (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    ⁅thompsonJ (S : Subgroup G), aimg (S : Subgroup G) α (Fcore G)⁆ =
      aimg (S : Subgroup G) α (Zfix S) := by
  have := aimg_commutator (S := (S : Subgroup G)) (α := α) (thompsonJ_le_self' _)
    (Fcore_le_sylow (S := S))
  rw [aimg_thompsonJ, h.commutator_thompsonJ_Fcore] at this
  exact this.symm

theorem mul_mem_Fcore_of_central {z z' : G} (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hz : z ∈ Zfix S) (hz' : z' ∈ aimg (S : Subgroup G) α (Zfix S)) : z * z' ∈ Fcore G := by
  have hzS : z ∈ (S : Subgroup G) := Zfix_le_sylow hz
  have hz'S : z' ∈ (S : Subgroup G) := aimg_le hz'
  have hcomm : z * z' = z' * z := (IsSeed.Zfix_central hz hz'S).symm
  refine h.mem_Fcore_of_central_involution ((S : Subgroup G).mul_mem hzS hz'S) (fun t ht => ?_) ?_
  · calc z * z' * t = z * (z' * t) := by group
      _ = z * (t * z') := by rw [aimg_Zfix_central α ht hz']
      _ = (z * t) * z' := by group
      _ = (t * z) * z' := by rw [IsSeed.Zfix_central hz ht]
      _ = t * (z * z') := by group
  · have h1 : z ^ 2 = 1 := (isElemAbelian_iff.mp isElemAbelian_Zfix).2 z hz
    have h2 : z' ^ 2 = 1 := (isElemAbelian_iff.mp (isElemAbelian_aimg_Zfix α)).2 z' hz'
    rw [(show Commute z z' from hcomm).mul_pow, h1, h2, one_mul]

theorem tr_commutator_A_Fcore_le (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G)
    {A : Subgroup G} (hA : IsMaxElemAbelian (cj (S : Subgroup G) g) A) :
    ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ ≤ tr (S : Subgroup G) α g (Zfix S) := by
  obtain ⟨h1, h2⟩ := h.tr_commutator_A_Fcore α g hA
  by_cases hAQ : A ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G)
  · rw [h1 hAQ]; exact bot_le
  · exact (h2 hAQ).1.le

theorem tr_commutator_eq_of_ne_bot (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G)
    {A : Subgroup G} (hA : IsMaxElemAbelian (cj (S : Subgroup G) g) A)
    (hne : ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ ≠ ⊥) :
    ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ = tr (S : Subgroup G) α g (Zfix S) ∧
      ¬ A ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G) ∧
      cj (S : Subgroup G) g = A ⊔ tr (S : Subgroup G) α g (CFSG.pCore 2 G) := by
  obtain ⟨h1, h2⟩ := h.tr_commutator_A_Fcore α g hA
  by_cases hAQ : A ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G)
  · exact absurd (h1 hAQ) hne
  · exact ⟨(h2 hAQ).1, hAQ, (h2 hAQ).2⟩

end IsSeed

end Motion

end CFSG.QuasithinUnique.Setup.Campbell
