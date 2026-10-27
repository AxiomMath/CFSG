module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndPair
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_sylow_le_sylowImage {K A : Subgroup G} (hAK : A ≤ K) (hA : IsPGroup 2 A) :
    ∃ S : Sylow 2 ↥K, A ≤ sylowImage K S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨S, hS⟩ := hA'.exists_le_sylow
  exact ⟨S, fun a ha => ⟨⟨a, hAK ha⟩, hS ha, rfl⟩⟩

theorem false_of_isKleinFour_le_sylow_of_noCommuting
    {C : Subgroup G} (hCtight : TightlyEmbedded C)
    (hnoComm : ∀ g : G, g ∉ Subgroup.normalizer (C : Set G) → ∀ U V : Subgroup G,
      U ≤ rightConjugate C g → V ≤ C → IsKleinFour U → IsKleinFour V →
      ¬ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u))
    {g : G} (hg : g ∉ Subgroup.normalizer (C : Set G))
    (T : Sylow 2 ↥(rightConjugate C g ⊓ Subgroup.normalizer (C : Set G)))
    {U : Subgroup G} (hU : IsKleinFour U)
    (hUT : U ≤ sylowImage (rightConjugate C g ⊓ Subgroup.normalizer (C : Set G)) T) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := sylowImage (rightConjugate C g ⊓ Subgroup.normalizer (C : Set G)) T with hA
  have hA1 : A ≠ ⊥ := by
    intro h1
    have h2 := Subgroup.card_le_of_le (h1 ▸ hUT)
    rw [hU.card_four, card_bot] at h2
    omega
  obtain ⟨S, hAS⟩ := exists_sylow_le_sylowImage (le_sup_right : A ≤ C ⊔ A)
    (sylowImage_isPGroup _ T)
  obtain ⟨-, -, hcomm, -, factor, -, -, -⟩ :=
    theorem_2_part_one C hCtight g hg T S hAS hA1
  set R := relativeNormalizer A (sylowImage (C ⊔ A) S) ⊓ C with hRdef
  set W : Subgroup G := ((U.subgroupOf A).map factor.toMonoidHom).map R.subtype with hWdef
  have hWR : W ≤ R := map_subtype_le _
  have hUA : U ≤ A := hUT
  have hW : IsKleinFour W := by
    refine isKleinFour_of_card_eq_four ?_ ?_
    · rw [hWdef, card_map_of_injective R.subtype_injective,
        card_map_of_injective factor.injective, ← hU.card_four]
      exact Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hu2 : u ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact sq_eq_one_of_isKleinFour hU hu)
      show ((factor u : R) : G) ^ 2 = 1
      rw [← SubgroupClass.coe_pow, ← map_pow, hu2, map_one, OneMemClass.coe_one]
  have hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := fun u hu w hw => hcomm u (hUA hu) w (hWR hw)
  have hUC : U ≤ rightConjugate C g := hUT.trans (overlap_sylow_le_conjugate C g T)
  exact hnoComm g hg U W hUC (hWR.trans inf_le_right) hU hW hUW

theorem false_of_isKleinFour_le_sylow (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) {M : Subgroup G}
    (hM : IsFooteM L M) (hne : FooteNoEscape M) {g : G} (hg : g ∉ normalizer (M : Set G))
    (T : Sylow 2 ↥(rightConjugate (coreActionKernel M) g ⊓
      normalizer (coreActionKernel M : Set G)))
    {U : Subgroup G} (hU : IsKleinFour U) (hUT : U ≤ sylowImage _ T) : False := by
  have hNC := normalizer_coreActionKernel_eq h h47 hST hM
  have htight := tightlyEmbedded_coreActionKernel h h47 hST hM hne
  have hgC : g ∉ Subgroup.normalizer (coreActionKernel M : Set G) := by
    rw [hNC]
    exact hg
  have hnoComm : ∀ g' : G, g' ∉ Subgroup.normalizer (coreActionKernel M : Set G) →
      ∀ U V : Subgroup G,
      U ≤ rightConjugate (coreActionKernel M) g' → V ≤ coreActionKernel M →
      IsKleinFour U → IsKleinFour V →
      ¬ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) := by
    intro g' hg' U V hUC hVC hU hV hUV
    have hgM : g' ∉ normalizer (M : Set G) := by simpa [hNC] using hg'
    refine false_of_commuting_fourgroups (g := g') h h47 hST hA5 hE8 hK hcalc hFI hM hne hgM
      hU ?_ hV hVC hUV
    rw [← GSThmB.conjugate_coreActionKernel]
    exact hUC
  exact false_of_isKleinFour_le_sylow_of_noCommuting htight hnoComm hgC T hU hUT

end CFSG.ComponentClassification.FooteLit
