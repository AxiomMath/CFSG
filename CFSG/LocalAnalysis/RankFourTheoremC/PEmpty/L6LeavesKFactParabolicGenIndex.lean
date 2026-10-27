module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.LieType.BorelTits CFSG.ABGLocalTools Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_eq_of_isPGroup_quotient (W : Sylow 2 G) {Δ : Subgroup G} [Δ.Normal]
    (hq : IsPGroup 2 (G ⧸ Δ)) (g : G) : ∃ δ ∈ Δ, ∃ w ∈ (W : Subgroup G), g = δ * w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' Δ) := QuotientGroup.mk'_surjective Δ
  set W' : Sylow 2 (G ⧸ Δ) := W.mapSurjective hsurj with hW'
  have hK : IsPGroup 2 ↥(⊤ : Subgroup (G ⧸ Δ)) := hq.of_equiv Subgroup.topEquiv.symm
  have htop : (⊤ : Subgroup (G ⧸ Δ)) = (W' : Subgroup (G ⧸ Δ)) := W'.is_maximal' hK le_top
  have hmem : (QuotientGroup.mk' Δ) g ∈ (W : Subgroup G).map (QuotientGroup.mk' Δ) := by
    have : (QuotientGroup.mk' Δ) g ∈ (W' : Subgroup (G ⧸ Δ)) := htop ▸ Subgroup.mem_top _
    rwa [hW', Sylow.coe_mapSurjective] at this
  obtain ⟨w, hw, hwg⟩ := hmem
  refine ⟨g * w⁻¹, ?_, w, hw, by group⟩
  have h1 : w⁻¹ * g ∈ Δ := by
    have := (QuotientGroup.eq (a := w) (b := g)).mp hwg
    exact this
  have := Normal.conj_mem ‹Δ.Normal› _ h1 w
  simpa [mul_assoc] using this

theorem iSup_inf_eq_of_family {ι : Type} (F : ParFam G ι) {Δ : Subgroup G} [Δ.Normal]
    (hq : IsPGroup 2 (G ⧸ Δ)) : ⨆ i, (F.P i ⊓ Δ) = Δ := by
  set M : Subgroup G := ⨆ i, (F.P i ⊓ Δ) with hM
  have hMΔ : M ≤ Δ := iSup_le fun i => inf_le_right
  have hWP : ∀ i, (F.W : Subgroup G) ≤ F.P i := fun i => le_normalizer.trans (F.normalizer_le i)
  have hWM : (F.W : Subgroup G) ≤ normalizer (M : Set G) := by
    intro w hw
    have hmap : ∀ i, (F.P i ⊓ Δ).map (MulAut.conj w).toMonoidHom = F.P i ⊓ Δ := by
      intro i
      have hw1 : w ∈ normalizer ((F.P i ⊓ Δ : Subgroup G) : Set G) :=
        inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer (hWP i hw),
            by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _⟩
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hw1
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [hM, Subgroup.map_iSup]
    exact iSup_congr hmap
  have hPM : ∀ i, F.P i ≤ M ⊔ (F.W : Subgroup G) := by
    intro i p hp
    obtain ⟨δ, hδ, w, hw, rfl⟩ := exists_mul_eq_of_isPGroup_quotient F.W hq p
    have hδP : δ ∈ F.P i := by
      have := (F.P i).mul_mem hp ((F.P i).inv_mem (hWP i hw))
      simpa using this
    exact mul_mem (Subgroup.mem_sup_left (le_iSup (fun i => F.P i ⊓ Δ) i ⟨hδP, hδ⟩))
      (Subgroup.mem_sup_right hw)
  have hMW : M ⊔ (F.W : Subgroup G) = ⊤ := by
    rw [eq_top_iff, ← F.gen]
    exact iSup_le hPM
  refine le_antisymm hMΔ fun δ hδ => ?_
  have hδ' : δ ∈ M ⊔ (F.W : Subgroup G) := hMW ▸ Subgroup.mem_top δ
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M _ hWM] at hδ'
  obtain ⟨m, hm, w, hw, rfl⟩ := hδ'
  have hwΔ : w ∈ Δ := by
    have := Δ.mul_mem (Δ.inv_mem (hMΔ hm)) hδ
    simpa using this
  obtain ⟨i0⟩ := F.nonempty
  exact mul_mem hm (le_iSup (fun i => F.P i ⊓ Δ) i0 ⟨hWP i0 hw, hwΔ⟩)

theorem hasParGen_of_normal_two_quotient {ι : Type} (F : ParFam G ι) {Δ : Subgroup G} [Δ.Normal]
    (hq : IsPGroup 2 (G ⧸ Δ)) (hQΔ : ∀ i, F.Q i ⊓ Δ ≠ ⊥)
    (hSN : ∀ S : Sylow 2 ↥Δ, normalizer (S : Set ↥Δ) ≤ S) : HasParGen ↥Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWsyl : IsSylowOf 2 (F.W : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, F.W.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact F.W.not_dvd_index
  have hSΔ : IsSylowOf 2 ((F.W : Subgroup G) ⊓ Δ) Δ :=
    hWsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  obtain ⟨S, hS⟩ := hSΔ.exists_sylow_eq_subgroupOf
  have hWP : ∀ i, (F.W : Subgroup G) ≤ F.P i := fun i => le_normalizer.trans (F.normalizer_le i)
  refine ⟨S, parabGen_eq_top_of_family (fun i => (F.P i ⊓ Δ).subgroupOf Δ) (fun i => ?_)
    (fun i => ?_) ?_⟩
  · refine (hSN S).trans ?_
    rw [hS]
    exact Subgroup.subgroupOf_mono Δ (inf_le_inf_right Δ (hWP i))
  · intro hbot
    have hQP : (F.Q i ⊓ Δ).subgroupOf Δ ≤ (F.P i ⊓ Δ).subgroupOf Δ :=
      Subgroup.subgroupOf_mono Δ (inf_le_inf_right Δ (F.le i))
    have hnorm : (F.P i ⊓ Δ).subgroupOf Δ ≤ normalizer (((F.Q i ⊓ Δ).subgroupOf Δ : Subgroup ↥Δ)
        : Set ↥Δ) := by
      intro x hx
      have hx1 : (x : G) ∈ F.P i := (Subgroup.mem_inf.mp hx).1
      have hx2 : (x : G) ∈ normalizer ((F.Q i ⊓ Δ : Subgroup G) : Set G) :=
        inf_normalizer_le_normalizer_inf
          ⟨F.normalizes i hx1, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _⟩
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : F.Q i ⊓ Δ ≤ Δ)]
      exact hx2
    have hp : IsPGroup 2 ((F.Q i ⊓ Δ).subgroupOf Δ) := (F.isPGroup i).to_inf_left.comap_subtype
    have hle := le_pCoreOf_of_le_normalizer 2 hQP hnorm hp
    rw [hbot, le_bot_iff] at hle
    apply hQΔ i
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : F.Q i ⊓ Δ ≤ Δ), hle, Subgroup.map_bot]
  · have hM := iSup_inf_eq_of_family F hq
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ ⨆ i, (F.P i ⊓ Δ) := by
      rw [hM]
      exact x.2
    have h1 : (⨆ i, (F.P i ⊓ Δ).subgroupOf Δ).map Δ.subtype = ⨆ i, (F.P i ⊓ Δ) := by
      rw [Subgroup.map_iSup]
      congr 1
      ext1 i
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
    have h2 : (x : G) ∈ (⨆ i, (F.P i ⊓ Δ).subgroupOf Δ).map Δ.subtype := h1 ▸ hx
    obtain ⟨y, hy, hyx⟩ := h2
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
