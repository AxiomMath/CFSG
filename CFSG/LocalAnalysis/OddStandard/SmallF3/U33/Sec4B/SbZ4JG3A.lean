module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem z4j_card_tG_E16 {Y : Subgroup G} (hY : IsE16In S Y) :
    {u : G | u ∈ Y ∧ ∃ g : G, u = g * t * g⁻¹}.ncard ≤ 4 := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hz.toCtx10.toCtx4
  have hS : S ≤ invCent t := hc4.toCtx.toCtx0.le_invCent
  have hcount := hz.toCtx10.l47.2.2.2.2 Y hY
  have ht1 : t ≠ 1 := S4A.t_ne_one hc4.toCtx.hyp
  have hsub : {u : G | u ∈ Y ∧ ∃ g : G, u = g * t * g⁻¹} ⊆
      {t} ∪ (conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G)) := by
    rintro u ⟨huY, g, rfl⟩
    have huH : g * t * g⁻¹ ∈ invCent t := hS (hY.1 huY)
    have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      have h2 := hY.2.1.2 _ huY
      rwa [pow_two] at h2
    have hu1 : g * t * g⁻¹ ≠ 1 := by
      intro h1
      apply ht1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨k, hk, hkcases⟩ := (hc4.five_classes).1 _ huH hu2 hu1
    have hktk : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    obtain ⟨g', hg'⟩ : ∃ g' : G, k * (g * t * g⁻¹) * k⁻¹ = g' * t * g'⁻¹ :=
      ⟨k * g, by group⟩
    rcases hkcases with h1 | h1 | h1 | h1 | h1
    · left
      have h2 : g * t * g⁻¹ = k⁻¹ * (k * (g * t * g⁻¹) * k⁻¹) * k := by group
      rw [h1] at h2
      rw [h2]
      calc k⁻¹ * t * k = k⁻¹ * (t * k) := by group
        _ = t := by rw [← hktk]; group
    · exact absurd ⟨g', by rw [← hg', h1]⟩ hc4.not_conj_z
    · exact absurd (hg'.symm.trans h1) (hz.nPre.tau_ttau_not_conj.1 g')
    · right
      refine ⟨⟨k⁻¹, (invCent t).inv_mem hk, ?_⟩, huY⟩
      rw [← h1]
      group
    · exact absurd (hg'.symm.trans h1) (hz.nPre.tau_ttau_not_conj.2 g')
  calc {u : G | u ∈ Y ∧ ∃ g : G, u = g * t * g⁻¹}.ncard
      ≤ (({t} : Set G) ∪ (conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({t} : Set G).ncard +
        (conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G)).ncard :=
        Set.ncard_union_le _ _
    _ = 4 := by rw [Set.ncard_singleton, hcount.2.1]

theorem z4j_card_tG_elem16 {F : Subgroup G} (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF2 : ∀ a ∈ F, a * a = 1) (hF : Nat.card F = 16) :
    {u : G | u ∈ F ∧ ∃ g : G, u = g * t * g⁻¹}.ncard ≤ 4 := by
  by_cases hne : ∃ u ∈ F, ∃ g : G, u = g * t * g⁻¹
  · obtain ⟨u₀, hu₀F, g₀, hu₀⟩ := hne
    have hFc : F ≤ centralizer ({g₀ * t * g₀⁻¹} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff, ← hu₀]
      exact hFab a ha u₀ hu₀F
    have hFp : IsPGroup 2 F := by
      intro x
      exact ⟨1, Subtype.ext (by simpa [pow_two] using hF2 (x : G) x.2)⟩
    obtain ⟨k, hk⟩ := S4B.c17_exists_conj hz.toCtx10 g₀ hFp hFc
    let Y : Subgroup G := F.map (MulAut.conj k).toMonoidHom
    have hYS : Y ≤ S := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hk a ha
    have hYab : IsMulCommutative ↥Y := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hFab a' ha' b' hb']
    have hY2 : ∀ x ∈ Y, x ^ 2 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, pow_two, hF2 a ha, map_one]
    have hYcard : Nat.card Y = 16 := by
      rw [← hF]
      exact Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hbound := hz.z4j_card_tG_E16 (show IsE16In S Y from ⟨hYS, ⟨hYab, hY2⟩, hYcard⟩)
    calc {u : G | u ∈ F ∧ ∃ g : G, u = g * t * g⁻¹}.ncard
        = ((fun u : G => k * u * k⁻¹) ''
            {u : G | u ∈ F ∧ ∃ g : G, u = g * t * g⁻¹}).ncard :=
          (Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)).symm
      _ ≤ {u : G | u ∈ Y ∧ ∃ g : G, u = g * t * g⁻¹}.ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro _ ⟨u, ⟨huF, g, hug⟩, rfl⟩
          refine ⟨⟨u, huF, by simp [MulAut.conj_apply]⟩, k * g, ?_⟩
          rw [hug]
          group
      _ ≤ 4 := hbound
  · have hempty : {u : G | u ∈ F ∧ ∃ g : G, u = g * t * g⁻¹} = ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨u, h.1, h.2⟩
    rw [hempty]
    simp

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
