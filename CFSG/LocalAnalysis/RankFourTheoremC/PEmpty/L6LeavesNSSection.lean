module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS

open Subgroup CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open scoped commutatorElement

theorem s622IsSimpleSection_comap {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) {K : Subgroup Z} (hK : IsSimpleGroup ↥K)
    (hn : ∃ a b : ↥K, a * b ≠ b * a) : S622IsSimpleSection (K.comap π) π.ker := by
  have hmem : ∀ l : Y, ∀ k : ↥K, π l = (k : Z) → l ∈ K.comap π := fun l k hl => by
    rw [mem_comap, hl]
    exact k.2
  refine ⟨Subgroup.ker_le_comap π K, inferInstance, ?_, ?_, ?_⟩
  · intro hkeq
    obtain ⟨a, b, hab⟩ := hn
    have ha1 : a ≠ 1 := fun h1 => hab (by rw [h1]; simp)
    obtain ⟨l, hl⟩ := hπ (a : Z)
    have hl1 : l ∈ π.ker := by
      rw [hkeq]
      exact hmem l a hl
    apply ha1
    apply Subtype.ext
    rw [← hl]
    exact MonoidHom.mem_ker.mp hl1
  · intro N hDN hNL hNn
    set Nb : Subgroup ↥K := (N.map π).subgroupOf K with hNb
    have hNbn : Nb.Normal := by
      refine ⟨fun k hk g => ?_⟩
      obtain ⟨n₀, hn₀, hn₀k⟩ := Subgroup.mem_subgroupOf.mp hk
      obtain ⟨l, hl⟩ := hπ (g : Z)
      have hlK : l ∈ K.comap π := hmem l g hl
      have hn₀L : n₀ ∈ K.comap π := hNL hn₀
      have hc := (Subgroup.normal_subgroupOf_iff hNL).1 hNn n₀ l hn₀ hlK
      refine Subgroup.mem_subgroupOf.mpr ⟨l * n₀ * l⁻¹, hc, ?_⟩
      show π (l * n₀ * l⁻¹) = (g : Z) * (k : Z) * (g : Z)⁻¹
      rw [map_mul, map_mul, map_inv, hl, hn₀k]
    haveI := hK
    haveI := hNbn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nb with hbot | htop
    · left
      refine le_antisymm (fun n hn => ?_) hDN
      have hnK : π n ∈ K := hNL hn
      have : (⟨π n, hnK⟩ : ↥K) ∈ Nb := Subgroup.mem_subgroupOf.mpr ⟨n, hn, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val this)
    · right
      refine le_antisymm hNL (fun l hl => ?_)
      have : (⟨π l, hl⟩ : ↥K) ∈ Nb := by
        rw [htop]
        exact mem_top _
      obtain ⟨n, hn, hnl⟩ := Subgroup.mem_subgroupOf.mp this
      have hker : n⁻¹ * l ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
      have e : l = n * (n⁻¹ * l) := by group
      rw [e]
      exact N.mul_mem hn (hDN hker)
  · intro hall
    obtain ⟨a, b, hab⟩ := hn
    obtain ⟨l₁, hl₁⟩ := hπ (a : Z)
    obtain ⟨l₂, hl₂⟩ := hπ (b : Z)
    have h1 := hall l₁ (hmem l₁ a hl₁) l₂ (hmem l₂ b hl₂)
    have h2 : π (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) = 1 := h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hl₁, hl₂] at h2
    apply hab
    apply Subtype.ext
    have h3 : ⁅(a : Z), (b : Z)⁆ = 1 := h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem s622IsSimpleSection_map {Y A : Type} [Group Y] [Group A] (f : Y →* A)
    (hf : Function.Injective f) {L D : Subgroup Y} (h : S622IsSimpleSection L D) :
    S622IsSimpleSection (L.map f) (D.map f) := by
  obtain ⟨hDL, hDn, hDne, hmin, hnab⟩ := h
  have hDn' := (Subgroup.normal_subgroupOf_iff hDL).1 hDn
  refine ⟨Subgroup.map_mono hDL, ?_, fun h => hDne (Subgroup.map_injective hf h), ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hDL)]
    rintro _ _ ⟨d, hd, rfl⟩ ⟨l, hl, rfl⟩
    exact ⟨l * d * l⁻¹, hDn' d l hd hl, by simp⟩
  · intro N hDN hNL hNn
    have hNL' : N ≤ L.map f := hNL
    set N₀ : Subgroup Y := N.comap f with hN₀
    have hDN₀ : D ≤ N₀ := fun d hd => hDN ⟨d, hd, rfl⟩
    have hN₀L : N₀ ≤ L := by
      intro n hn
      obtain ⟨l, hl, hln⟩ := hNL' hn
      rw [← hf hln]
      exact hl
    have hN₀n : (N₀.subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hN₀L]
      intro n l hn hl
      have := (Subgroup.normal_subgroupOf_iff hNL').1 hNn (f n) (f l) hn ⟨l, hl, rfl⟩
      show f (l * n * l⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact this
    have hNeq : N = N₀.map f := by
      refine le_antisymm (fun n hn => ?_) (Subgroup.map_comap_le f N)
      obtain ⟨l, hl, rfl⟩ := hNL' hn
      exact ⟨l, hn, rfl⟩
    rcases hmin N₀ hDN₀ hN₀L hN₀n with h1 | h1
    · left
      rw [hNeq, h1]
    · right
      rw [hNeq, h1]
  · intro hall
    apply hnab
    intro a ha b hb
    obtain ⟨d, hd, hdeq⟩ := hall (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩
    have : d = a * b * a⁻¹ * b⁻¹ := hf (by rw [hdeq]; simp)
    rw [← this]
    exact hd

theorem mem_normalizer_comap {Y Z : Type*} [Group Y] [Group Z] (π : Y →* Z) {K : Subgroup Z}
    {g : Y} (hg : π g ∈ normalizer (K : Set Z)) :
    g ∈ normalizer ((K.comap π : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff]
  intro h
  have := mem_normalizer_iff.mp hg (π h)
  simp only [mem_comap, map_mul, map_inv]
  exact this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS
