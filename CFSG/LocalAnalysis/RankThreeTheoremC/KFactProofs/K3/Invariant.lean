module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Wreath

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.ABGLocalTools (IsSylowOf)

section Invariant

variable {H : Type} [Group H] [Finite H]

theorem sylow_inf_component (S : Sylow 3 H) {L : Subgroup H}
    (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    IsSylowOf 3 ((S : Subgroup H) ⊓ L) L := by
  have hS : IsSylowOf 3 (S : Subgroup H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hSK : IsSylowOf 3 (S : Subgroup H) ((S : Subgroup H) ⊔ L) :=
    hS.of_le le_sup_left le_top
  have hKN : (S : Subgroup H) ⊔ L ≤ normalizer (L : Set H) :=
    sup_le hSL Subgroup.le_normalizer
  exact hSK.inf_of_le_normalizer le_sup_right hKN

end Invariant

section Invariant

variable {H : Type} [Group H] [Finite H]

theorem ti_mem_map (S : Sylow 3 H) (e : (S : Subgroup H) ≃* W3) (L : Subgroup H)
    (y : (S : Subgroup H)) :
    e y ∈ (((S : Subgroup H) ⊓ L).subgroupOf (S : Subgroup H)).map e.toMonoidHom ↔
      (y : H) ∈ L := by
  constructor
  · intro hmem
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    change e z = e y at hzy
    have hzy' : z = y := e.injective hzy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hz
    rw [← hzy']
    exact hz.2
  · intro hy
    exact Subgroup.mem_map.mpr
      ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨y.2, hy⟩), rfl⟩

theorem ti_normal (S : Sylow 3 H) {L : Subgroup H}
    (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) (e : (S : Subgroup H) ≃* W3)
    {N : Subgroup W3} (hmem : ∀ y : (S : Subgroup H), e y ∈ N ↔ (y : H) ∈ L) :
    N.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective n
  obtain ⟨y, rfl⟩ := e.surjective g
  rw [← map_inv e, ← map_mul e, ← map_mul e, hmem]
  have hz : (z : H) ∈ L := (hmem z).mp hn
  have hy : (y : H) ∈ normalizer (L : Set H) := hSL y.2
  exact (Subgroup.mem_set_normalizer_iff.mp hy (z : H)).mp hz

theorem ti_ne_bot (S : Sylow 3 H) (e : (S : Subgroup H) ≃* W3) {L : Subgroup H}
    {N : Subgroup W3} (hmem : ∀ y : (S : Subgroup H), e y ∈ N ↔ (y : H) ∈ L)
    {t : H} (ht : t ∈ (S : Subgroup H)) (htL : t ∈ L) (ho : orderOf t = 3) : N ≠ ⊥ := by
  intro hbot
  have h1 : e ⟨t, ht⟩ ∈ N := (hmem ⟨t, ht⟩).mpr htL
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : e ⟨t, ht⟩ = e 1 := by rw [h1, map_one]
  have h3 : (⟨t, ht⟩ : (S : Subgroup H)) = 1 := e.injective h2
  have h4 : t = 1 := congrArg Subtype.val h3
  rw [h4, orderOf_one] at ho
  norm_num at ho

theorem ti_commute (S : Sylow 3 H) (e : (S : Subgroup H) ≃* W3) {L₁ L₂ : Subgroup H}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂)
    {N₁ N₂ : Subgroup W3} (hmem₁ : ∀ y : (S : Subgroup H), e y ∈ N₁ ↔ (y : H) ∈ L₁)
    (hmem₂ : ∀ y : (S : Subgroup H), e y ∈ N₂ ↔ (y : H) ∈ L₂) :
    ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a := by
  intro a ha b hb
  obtain ⟨z, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  have hz : (z : H) ∈ L₁ := (hmem₁ z).mp ha
  have hy : (y : H) ∈ L₂ := (hmem₂ y).mp hb
  have hzy : z * y = y * z := Subtype.ext (component_commute h₁ h₂ h12 hz hy)
  rw [← map_mul e, ← map_mul e, hzy]

theorem not_two_invariant (hH : primeComplementCore (G := H) 3 = ⊥) (S : Sylow 3 H)
    (hSW : Nonempty ((S : Subgroup H) ≃* W3)) {L₁ L₂ : Subgroup H} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂)
    (hS₁ : (S : Subgroup H) ≤ normalizer (L₁ : Set H))
    (hS₂ : (S : Subgroup H) ≤ normalizer (L₂ : Set H)) : False := by
  obtain ⟨e⟩ := hSW
  obtain ⟨t₁, ht₁, ho₁, l₁, hl₁, hlt₁⟩ :=
    exists_mem_sylow_component hH h₁ (sylow_inf_component S hS₁)
  obtain ⟨t₂, ht₂, ho₂, l₂, hl₂, hlt₂⟩ :=
    exists_mem_sylow_component hH h₂ (sylow_inf_component S hS₂)
  obtain ⟨N₁, hmem₁⟩ : ∃ N : Subgroup W3, ∀ y : (S : Subgroup H), e y ∈ N ↔ (y : H) ∈ L₁ :=
    ⟨(((S : Subgroup H) ⊓ L₁).subgroupOf (S : Subgroup H)).map e.toMonoidHom,
      fun y => ti_mem_map S e L₁ y⟩
  obtain ⟨N₂, hmem₂⟩ : ∃ N : Subgroup W3, ∀ y : (S : Subgroup H), e y ∈ N ↔ (y : H) ∈ L₂ :=
    ⟨(((S : Subgroup H) ⊓ L₂).subgroupOf (S : Subgroup H)).map e.toMonoidHom,
      fun y => ti_mem_map S e L₂ y⟩
  have hN₁ : N₁.Normal := ti_normal S hS₁ e hmem₁
  have hN₂ : N₂.Normal := ti_normal S hS₂ e hmem₂
  have hne₁ : N₁ ≠ ⊥ := ti_ne_bot S e hmem₁ ht₁.1 ht₁.2 ho₁
  have hne₂ : N₂ ≠ ⊥ := ti_ne_bot S e hmem₂ ht₂.1 ht₂.2 ho₂
  have hs₁ : e ⟨t₁, ht₁.1⟩ ∈ N₁ := (hmem₁ ⟨t₁, ht₁.1⟩).mpr ht₁.2
  have hs₂ : e ⟨t₂, ht₂.1⟩ ∈ N₂ := (hmem₂ ⟨t₂, ht₂.1⟩).mpr ht₂.2
  have hnot₁ : t₁ ∈ L₂ → False := fun h =>
    hlt₁ (component_inf_le_center h₁ h₂ h12 ht₁.2 h l₁ hl₁)
  have hnot₂ : t₂ ∈ L₁ → False := fun h =>
    hlt₂ (component_inf_le_center h₂ h₁ h12.symm ht₂.2 h l₂ hl₂)
  have hnc₁ : ¬ N₁ ≤ center W3 := fun hle =>
    hnot₁ ((hmem₂ ⟨t₁, ht₁.1⟩).mp (W3_center_le_of_normal hN₂ hne₂ (hle hs₁)))
  have hnc₂ : ¬ N₂ ≤ center W3 := fun hle =>
    hnot₂ ((hmem₁ ⟨t₂, ht₂.1⟩).mp (W3_center_le_of_normal hN₁ hne₁ (hle hs₂)))
  rcases W3_comparable hN₁ hN₂ hnc₁ hnc₂ (ti_commute S e h₁ h₂ h12 hmem₁ hmem₂) with hle | hle
  · exact hnot₁ ((hmem₂ ⟨t₁, ht₁.1⟩).mp (hle hs₁))
  · exact hnot₂ ((hmem₁ ⟨t₂, ht₂.1⟩).mp (hle hs₂))

end Invariant

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
