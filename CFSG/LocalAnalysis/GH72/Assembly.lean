module

public import CFSG.LocalAnalysis.GH72.DDStructure
public import CFSG.LocalAnalysis.Mason73.FinalIdentification
public import CFSG.LocalAnalysis.Mason73.Lemma44

public section

namespace CFSG.GH72

open Subgroup

theorem aStar_of_sections
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h417 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G),
      H.Normal →
        ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h72 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁))
    (h73 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal)) :
    AStarStatement := by
  refine aStar_of_not_minimalCounterexample fun G _ _ hmc => ?_
  obtain ⟨-, h2, S, hS⟩ := hmc.hyp
  obtain ⟨S₁, S₂, hd⟩ := exists_ddDecomp (S : Subgroup G) hS
  obtain ⟨S₁', S₂', hd', hpf⟩ := h32_37 (⟨S, S₁, S₂, hd, h2⟩ : Sec3Setting G)
  obtain ⟨z₁, hz₁⟩ := exists_central_involution S₁' hd'.dih₁
  obtain ⟨z₂, hz₂⟩ := exists_central_involution S₂' (isDih_of_isDihNonab hd'.dih₂)
  let 𝔖 : Sec4Setting G := ⟨⟨S, S₁', S₂', hd', h2⟩, hmc, hpf, z₁, z₂, hz₁, hz₂⟩
  obtain ⟨A, hAS, hA⟩ := exists_e16 𝔖.decomp
  obtain ⟨⟨M₁, hM₁⟩, hN⟩ := h72 𝔖 hAS hA
  obtain ⟨h73a, h73b⟩ := h73 𝔖 hAS hA
  by_cases hsolv : Group.IsSolvable (𝔖.N A)
  · exact (h417 𝔖 M₁ (h73b hsolv M₁ hM₁)).2 hM₁.2.2.2.1
  · obtain ⟨N₁, hN₁⟩ := hN hsolv
    exact (h417 𝔖 N₁ (h73a hsolv N₁ hN₁)).1 hN₁.2.2.2.1

theorem hDD_of_sections
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h417 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G),
      H.Normal →
        ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h72 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁))
    (h73 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal)) :
    HDDStatement :=
  hDD_of_aStar (aStar_of_sections h32_37 h417 h72 h73)

theorem lemma44_of_sections
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h417 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G),
      H.Normal →
        ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h72 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁))
    (h73 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal))
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {n : ℕ} (hn : 3 ≤ n)
    {ι : CFSG.CGT.Stroth77.L4Sylow.L4Model n →* G} (hι : Function.Injective ι)
    (S : Sylow 2 G) (hS : ι.range = (S : Subgroup G)) :
    CFSG.LocalAnalysis.Mason73.Mason44Conclusion G :=
  CFSG.LocalAnalysis.Mason73.lemma44 hn hι S hS (hDD_of_sections h32_37 h417 h72 h73)

theorem hMason_of_sections
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hSC : CFSG.LocalAnalysis.Mason73.L4SylowComparison)
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h417 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G),
      H.Normal →
        ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h72 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁))
    (h73 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal)) :
    ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
        Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n) →
        CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G := by
  intro G _ _ _ hnonab n hn P hP
  obtain ⟨e⟩ := hP
  let ι : CFSG.CGT.Stroth77.L4Sylow.L4Model n →* G :=
    (P : Subgroup G).subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (P : Subgroup G).subtype_injective.comp e.symm.injective
  have hS : ι.range = (P : Subgroup G) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact CFSG.LocalAnalysis.Mason73.masonL4_of_mason44_comparison hCIT hSC hnonab hn P ⟨e⟩
    (lemma44_of_sections h32_37 h417 h72 h73 hn hι P hS)

end CFSG.GH72
