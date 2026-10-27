module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNotLeX
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
import CFSG.GroupTheory.ConjTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem isPComponentIn_conj_mem {p : ℕ} {M H : Subgroup G} {g : G}
    (hg : g ∈ H ⊓ M) {Y : Subgroup G} (hY : IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) :
    IsPComponentIn p (Y.map (MulAut.conj g).toMonoidHom) H ∧
      ¬ Y.map (MulAut.conj g).toMonoidHom ≤ M := by
  refine ⟨isPComponentIn_conj hY hg.1, fun hle => hYM fun y hy => ?_⟩
  have hmem : g * y * g⁻¹ ∈ M := hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  have hconj : g⁻¹ * (g * y * g⁻¹) * g ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hg.2) hmem) hg.2
  simpa [mul_assoc] using hconj

theorem inf_le_normalizer_kSub (p : ℕ) (M H : Subgroup G) :
    H ⊓ M ≤ normalizer (kSub p M H : Set G) := by
  by_cases hL : pLayerIn p H ≤ M
  · have hKH : H ≤ normalizer (kSub p M H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le p M H)).mp
        (kSub_normal_of_le hL)
    exact inf_le_left.trans hKH
  · intro g hg
    have hkSub : kSub p M H =
        sSup {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
      rw [kSub, if_neg hL]
    rw [hkSub]
    exact CFSG.Walter.mem_normalizer_sSup_of_map_mem
      (fun Y hY => isPComponentIn_conj_mem hg hY.1 hY.2)
      (fun Y hY => isPComponentIn_conj_mem (inv_mem hg) hY.1 hY.2)

private theorem mem_xSub_iff {p : ℕ} {M H : Subgroup G} {z : G} (hz : z ∈ H) :
    z ∈ xSub p M H ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨z, hz⟩ ∈
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  have hsub : ((xSub p M H).subgroupOf H) =
      (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    rw [xSub]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h1 : (⟨z, hz⟩ : ↥H) ∈ (xSub p M H).subgroupOf H ↔ z ∈ xSub p M H :=
    Subgroup.mem_subgroupOf
  have h2 : (⟨z, hz⟩ : ↥H) ∈ (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ↔ z ∈ xSub p M H := by
    rw [← hsub]
    exact h1
  rw [Subgroup.mem_comap] at h2
  exact h2.symm

private theorem conj_mem_kStar {p : ℕ} {M H : Subgroup G} {g : G} (hg : g ∈ H ⊓ M)
    {k : StarGroup p H} (hk : k ∈ kStar p M H) :
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨g, hg.1⟩ * k *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨g, hg.1⟩)⁻¹ ∈ kStar p M H := by
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let gH : ↥H := ⟨g, hg.1⟩
  change π gH * k * (π gH)⁻¹ ∈ kStar p M H
  obtain ⟨kH, hkH, rfl⟩ := Subgroup.mem_map.mp hk
  have hgnorm : g ∈ Subgroup.normalizer (kSub p M H : Set G) :=
    inf_le_normalizer_kSub p M H hg
  have hconjG : g * (kH : G) * g⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp hgnorm (kH : G)).mp (Subgroup.mem_subgroupOf.mp hkH)
  have hconjH : gH * kH * gH⁻¹ ∈ (kSub p M H).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr hconjG
  exact Subgroup.mem_map.mpr ⟨gH * kH * gH⁻¹, hconjH, by simp [π, map_mul, map_inv]⟩

private theorem conj_mem_xSub {p : ℕ} {M H : Subgroup G} {g x : G} (hg : g ∈ H ⊓ M)
    (hx : x ∈ xSub p M H) : g * x * g⁻¹ ∈ xSub p M H := by
  have hxH : x ∈ H := by
    unfold xSub CFSG.AGLEmbedding.d1PlusCore at hx
    exact Subgroup.map_subtype_le _ hx
  have hgxH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg.1 hxH) (H.inv_mem hg.1)
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let gH : ↥H := ⟨g, hg.1⟩
  let xH : ↥H := ⟨x, hxH⟩
  have hxCent : π xH ∈ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) :=
    (mem_xSub_iff hxH).mp hx
  have hgHinv : (π gH)⁻¹ = π ⟨g⁻¹, H.inv_mem hg.1⟩ := by
    have hsub : gH⁻¹ = (⟨g⁻¹, H.inv_mem hg.1⟩ : ↥H) := Subtype.ext rfl
    rw [← map_inv, hsub]
  have hconj' : ∀ k ∈ kStar p M H, (π gH)⁻¹ * k * π gH ∈ kStar p M H := by
    intro k hk
    have h := conj_mem_kStar (M := M) (H := H) (p := p) (g := g⁻¹) (inv_mem hg) hk
    have hb : (π ⟨g⁻¹, H.inv_mem hg.1⟩ : StarGroup p H) = (π gH)⁻¹ := hgHinv.symm
    rwa [hb, inv_inv] at h
  rw [mem_xSub_iff hgxH]
  have hπ : π ⟨g * x * g⁻¹, hgxH⟩ = π gH * π xH * (π gH)⁻¹ := by
    rw [show (⟨g * x * g⁻¹, hgxH⟩ : ↥H) = gH * xH * gH⁻¹ from rfl, map_mul, map_mul, map_inv]
  rw [hπ, Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : (π gH)⁻¹ * k * π gH ∈ kStar p M H := hconj' k hk
  have hcomm := (Subgroup.mem_centralizer_iff.mp hxCent) ((π gH)⁻¹ * k * π gH) hk'
  symm
  calc π gH * π xH * (π gH)⁻¹ * k
      = π gH * (π xH * ((π gH)⁻¹ * k * π gH)) * (π gH)⁻¹ := by group
    _ = π gH * (((π gH)⁻¹ * k * π gH) * π xH) * (π gH)⁻¹ := by rw [hcomm]
    _ = k * (π gH * π xH * (π gH)⁻¹) := by group

theorem inf_le_normalizer_xSub (p : ℕ) (M H : Subgroup G) :
    H ⊓ M ≤ normalizer (xSub p M H : Set G) := fun _ hg =>
  CFSG.GroupTheory.mem_normalizer_of_conj_mem fun _ hx => conj_mem_xSub hg hx

private theorem map_conj_le_of {W V : Subgroup G} {t : G} (hWV : W ≤ V)
    (h : ∀ w ∈ W, t * w * t⁻¹ ∈ W) :
    W.map (MulAut.conj t).toMonoidHom ≤ V := by
  rintro y ⟨w, hw, rfl⟩
  exact hWV (h w hw)

namespace IsE27InvConfig

private theorem conj_mem {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {t : G}
    (ht : t ∈ ({t₁, t₂, t₃} : Set G)) {x : G} (hx : x ∈ V) : t * x * t⁻¹ ∈ V := by
  have hV1 : W₁ ≤ V := (le_sup_left.trans le_sup_left).trans (le_of_eq h.join.symm)
  have hV2 : W₂ ≤ V := (le_sup_right.trans le_sup_left).trans (le_of_eq h.join.symm)
  have hV3 : W₃ ≤ V := le_sup_right.trans (le_of_eq h.join.symm)
  have hmap : V.map (MulAut.conj t).toMonoidHom ≤ V := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with h₁ | h₂ | h₃
    · subst t
      have h1 := map_conj_le_of hV1 (W := W₁) (t := t₁)
        (fun w hw => by rw [h.inv₁ w hw]; exact W₁.inv_mem hw)
      have h2 := map_conj_le_of hV2 (W := W₂) (t := t₁)
        (fun w hw => by simpa [h.comm₁ w (Subgroup.mem_sup_left hw)] using hw)
      have h3 := map_conj_le_of hV3 (W := W₃) (t := t₁)
        (fun w hw => by simpa [h.comm₁ w (Subgroup.mem_sup_right hw)] using hw)
      conv_lhs => rw [h.join]
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le h1 h2) h3
    · subst t
      have h1 := map_conj_le_of hV1 (W := W₁) (t := t₂)
        (fun w hw => by simpa [h.comm₂ w (Subgroup.mem_sup_left hw)] using hw)
      have h2 := map_conj_le_of hV2 (W := W₂) (t := t₂)
        (fun w hw => by rw [h.inv₂ w hw]; exact W₂.inv_mem hw)
      have h3 := map_conj_le_of hV3 (W := W₃) (t := t₂)
        (fun w hw => by simpa [h.comm₂ w (Subgroup.mem_sup_right hw)] using hw)
      conv_lhs => rw [h.join]
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le h1 h2) h3
    · subst t
      have h1 := map_conj_le_of hV1 (W := W₁) (t := t₃)
        (fun w hw => by simpa [h.comm₃ w (Subgroup.mem_sup_left hw)] using hw)
      have h2 := map_conj_le_of hV2 (W := W₂) (t := t₃)
        (fun w hw => by simpa [h.comm₃ w (Subgroup.mem_sup_right hw)] using hw)
      have h3 := map_conj_le_of hV3 (W := W₃) (t := t₃)
        (fun w hw => by rw [h.inv₃ w hw]; exact W₃.inv_mem hw)
      conv_lhs => rw [h.join]
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le h1 h2) h3
  exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

end IsE27InvConfig

theorem TwelveSixKCtx.inf_xSub_eq_bot (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hC₁ : centralizer (W₁ : Set G) ≤ M)
    (hC₂ : centralizer (W₂ : Set G) ≤ M) (hC₃ : centralizer (W₃ : Set G) ≤ M)
    (ht₁ : t₁ ∈ H ⊓ M) (ht₂ : t₂ ∈ H ⊓ M) (ht₃ : t₃ ∈ H ⊓ M) :
    V ⊓ xSub p M H = ⊥ := by
  by_contra hne
  have hDt : ∀ t ∈ ({t₁, t₂, t₃} : Set G), ∀ x ∈ V ⊓ xSub p M H,
      t * x * t⁻¹ ∈ V ⊓ xSub p M H := by
    intro t ht x hx
    have htHM : t ∈ H ⊓ M := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact ht₁
      · exact ht₂
      · exact ht₃
    exact ⟨hcfg.conj_mem ht hx.1,
      (Subgroup.mem_normalizer_iff.mp (inf_le_normalizer_xSub p M H htHM) x).mp hx.2⟩
  rcases hcfg.exists_le_of_invariant inf_le_left hne hDt with h | h | h
  · exact (hc.not_le_xSub_of_centralizer_le hcfg.card₁ hC₁) (h.trans inf_le_right)
  · exact (hc.not_le_xSub_of_centralizer_le hcfg.card₂ hC₂) (h.trans inf_le_right)
  · exact (hc.not_le_xSub_of_centralizer_le hcfg.card₃ hC₃) (h.trans inf_le_right)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
