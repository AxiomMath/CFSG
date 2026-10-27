module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentSplitting
import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def CentralQuotientRankOneRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M U : Subgroup G) (z : G),
    UniqueFusionDatum T M U z → ∀ u ∈ U, u ≠ 1 →
    ¬ Subgroup.centralizer ({u} : Set G) ≤ M →
    ∀ S : Subgroup G, IsSylowTwoOf S (Subgroup.centralizer ({u} : Set G)) → U ≤ S →
    ∀ L : Subgroup G, IsComponentIn L (Subgroup.centralizer ({u} : Set G)) →
      U ≤ Subgroup.normalizer (L : Set G) → fusionIsBenderGroup (L ⧸ Subgroup.center L)

theorem localComponentRecognition_of_centralQuotient
    (hrec : CentralQuotientRankOneRecognition) : LocalComponentRecognition := by
  intro G _ _ T M U z hd u hu hu1 hH S hS hUS L hL
  obtain ⟨-, -, -, hloc⟩ := hd.escaping_centralizer_local_structure hu hu1 hH
  obtain ⟨-, hcl, -⟩ := hloc S hS hUS
  obtain ⟨hodd, -, -⟩ := hd.escaping_centralizer_odd_core_components hu hu1 hH
  have hUL : U ≤ Subgroup.normalizer (L : Set G) :=
    RankOneRecog.normalizes_component hodd hS hUS hd.elem hcl hL
  have hmodel := hrec G T M U z hd u hu hu1 hH S hS hUS L hL hUL
  obtain ⟨hcenter, hsimple, hnonab, hbender, hinner, w, hwU, -, -, hwnc, hwR⟩ :=
    hd.reconstruction_of_model hu hu1 hH hS hUS hL hUL hmodel
  have hP : IsSylowTwoOf (S ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hL.1 hL.2.2
  obtain ⟨-, hVcard, htrans, -, hcyc⟩ :=
    constructed_rank_one_involution_normalizer_ambient hbender hP
      (V := omegaOne (S ⊓ L)) rfl
  obtain ⟨hAV, ⟨hUAC, hAC, -⟩, hNM, hCfix, htransA, hreg, hcycU⟩ :=
    confined_inner_rank_one_component_splitting (H := Subgroup.centralizer ({u} : Set G)) (M := M)
      (V := omegaOne (S ⊓ L)) (A := U ⊓ L) (C := U ⊓ Subgroup.centralizer (L : Set G))
      hS hUS hd.elem hcl hd.normal hL.1
      (RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hcenter) hP hUL hinner
      (RankOneRecog.commutator_ne_bot_of_not_le_centralizer hwU hwnc) rfl hVcard htrans hcyc hwU
      hwR rfl rfl
  exact ⟨hsimple, hnonab, hbender, hUL, hAV, by rw [hAV]; exact hVcard, hUAC.symm, hAC, hNM,
    hCfix, fun a ha b hb ha1 hb1 => htransA a ha ha1 b hb hb1, hreg, hcycU⟩

end CFSG.QuasithinUnique
