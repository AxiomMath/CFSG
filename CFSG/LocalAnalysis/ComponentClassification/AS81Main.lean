module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Reduce

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

theorem exists_isSylowOf {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ∃ R : Subgroup G, IsSylowOf 2 R K := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  exact ⟨_, P, rfl⟩

theorem oddCoreFreeStep_of (hII : L34HypII) (h14 : Step14)
    (h2 : Sec2SuzXR) (h4 : Sec4HeXR)
    (G : Type) [Group G] [Finite G] (A : Subgroup G) (hbelow : L34GeneralBelow (Nat.card G))
    (hH : RankTwoHypNF G A) (hL : TypeL34 (rankTwoQuot A))
    (hO : standardComponentOddCore G = ⊥) : OddCoreFreeConclusion A := by
  have hB : Base G A := ⟨hH, hO, hII A hH.standard.1.1 hL, Or.inl hL⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf (centralizer (A : Set G))
  by_cases hXR : rankTwoX A ⊔ R = ⊤
  · obtain ⟨g, E, F, hF⟩ := h14 G A hB hL R hR
    rcases Nat.even_or_odd (Nat.card (center A)) with he | ho
    · exact Or.inr (h4 G A R g E F hF hL he hbelow hXR)
    · exact Or.inl (h2 G A R g E F hF hL ho hbelow hXR)
  · exact oddCoreFreeConclusion_of_sup_ne_top hB hL hbelow hR hXR

theorem l34Step_of
    (hSuz : SuzMultiplierSix)
    (hII : L34HypII) (h14 : Step14) (h2 : Sec2SuzXR) (h4 : Sec4HeXR) (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (hbelow : L34GeneralBelow (Nat.card G)) (hH : RankTwoHypNF G A)
    (hL : TypeL34 (rankTwoQuot A)) : L34Conclusion A :=
  l34Step_of_oddCoreFree hSuz (oddCoreFreeStep_of hII h14 h2 h4) G A hbelow hH hL

theorem l34General_of
    (hSuz : SuzMultiplierSix)
    (hII : L34HypII) (h14 : Step14) (h2 : Sec2SuzXR) (h4 : Sec4HeXR) : L34General :=
  l34General_of_step (l34Step_of hSuz hII h14 h2 h4)

end CFSG.ComponentClassification.AS81
