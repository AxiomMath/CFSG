module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionReconstruction
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.RankOneRecog

open CFSG.Open

section Ambient

variable {G : Type*} [Group G]

theorem inf_centralizer_eq_bot_of_center_eq_bot {L : Subgroup G}
    (h : Subgroup.center L = ⊥) : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  rw [h, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)

theorem commutator_ne_bot_of_not_le_centralizer {L U : Subgroup G} {w : G} (hwU : w ∈ U)
    (hwnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) : ⁅L, U⁆ ≠ ⊥ := by
  intro h
  apply hwnc
  have h1 : L ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact h1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwU))

variable [Finite G]

theorem normalizes_component {H S U L : Subgroup G} (hcore : CFSG.oddCore H = ⊥)
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) (hL : IsComponentIn L H) :
    U ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨S', hS'⟩ := isSylowTwoOf_iff_exists.mp hS
  have hUH : U ≤ H := hUS.trans hS.1
  have hU'S' : U.subgroupOf H ≤ (S' : Subgroup H) := subgroupOf_le_of_map_eq hS' hUS
  have hnorm := strongly_closed_normalizes_components hcore S' hU'S' (isElemAbelian_subgroupOf hU)
    (stronglyClosed_subgroupOf hS' hcl) hL.2
  intro a ha
  have h1 : (⟨a, hUH ha⟩ : H) ∈
      Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H) := hnorm ha
  have h2 : a ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H)).map H.subtype :=
    ⟨_, h1, rfl⟩
  rw [map_subtype_normalizer hL.1] at h2
  exact h2.2

end Ambient

section Datum

variable {G : Type} [Group G] [Finite G] {T M U : Subgroup G} {z : G}

theorem _root_.CFSG.QuasithinUnique.UniqueFusionDatum.reconstruction_of_model
    (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) {S : Subgroup G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({u} : Set G))) (hUS : U ≤ S) {L : Subgroup G}
    (hL : IsComponentIn L (Subgroup.centralizer ({u} : Set G)))
    (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      fusionIsBenderGroup L ∧ (∀ u' ∈ U, ∃ x ∈ L, ∀ y ∈ L, u'⁻¹ * y * u' = x⁻¹ * y * x) ∧
      ∃ w ∈ U, w ∈ Subgroup.centralizer (S : Set G) ∧ w ≠ 1 ∧
        ¬ L ≤ Subgroup.centralizer ({w} : Set G) ∧
        ∀ R : Subgroup G, IsPGroup 2 R → w ∈ R → Subgroup.normalizer (R : Set G) ≤ M := by
  obtain ⟨-, -, -, hloc⟩ := hd.escaping_centralizer_local_structure hu hu1 hH
  obtain ⟨-, hcl, w, -, hwU, hwS, hw1, hwC, hwR⟩ := hloc S hS hUS
  obtain ⟨hodd, -, hnocomp⟩ := hd.escaping_centralizer_odd_core_components hu hu1 hH
  obtain ⟨-, -, hLodd, -⟩ := hd.escaping_component_central_involution hu hu1 hH hS hUS hwU hwS
    hwC hL
  have hLM : ¬ L ≤ M := by
    intro hle
    apply hnocomp _ hL.2
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL.1]
    exact hle
  have hwnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G) := fun hle => hLM (hle.trans hwC)
  have hQ : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  obtain ⟨hcenter, hsimple, hnonab, hbender, hinner⟩ := rank_one_central_quotient_reconstruction
    hS hUS hd.elem hcl hL.1 hL.2.2 hQ.1 hUL (isPGroup_two_center_of_oddCore_eq_bot hLodd) hmodel
    ⟨w, hwU, hwS, hwnc⟩
  exact ⟨hcenter, hsimple, hnonab, hbender, hinner, w, hwU, hwS, hw1, hwnc, hwR⟩

end Datum

end CFSG.QuasithinUnique.RankOneRecog
