module

public import CFSG.GroupTheory.McBrideGomiStatement
public import CFSG.GroupTheory.SylowIntersectionControl.CharNormalizerFusion
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma49
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Exists
import CFSG.GroupTheory.SylowIntersectionControl.CharPairChoice
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepB
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepC
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepD
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepE
import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem GNPairChoice.hasGomiBlock_of_not_isRegular (c : GNPairChoice Ω)
    (hc : ∀ T : Subgroup Ω, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      IsGomiCharPairGN T (c.fst T) (c.snd T))
    (hin : GomiThm45Inputs) (h49 : GomiLemma49) {G : Subgroup Ω} (hG : GomiHyp43 G)
    (hs : ¬ c.selection.IsRegular G) : HasGomiBlock G := by
  refine hasGomiBlock_of_cex (fun G' h => ?_) G hG hs
  have hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ c.selection.sets P :=
    fun P _ => by simp [GNPairChoice.selection]
  have hmono : ∀ H : Subgroup Ω, H ≤ G' → pCoreOf 2 G' ≤ H → GomiHyp43 H :=
    fun H hHG hQH => h.hyp_self.of_pCoreOf_le hHG hQH
  have hchar := h.hyp_self.charTwo
  have h45 := c.gomiThm45At hc hin G' h.hyp_self h.singular
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf G'
  obtain ⟨X, hX⟩ := h45 S hS
  obtain ⟨B, hB, hQB, hBt⟩ := h.exists_twoComponent hfZ hchar hmono h.hyp_self hin.fact31
    hin.fact33 hin.fact37Two hin.lemma44 hS hX
  have hGB := h.eq_conjClosure_sup hchar hmono h49 hB hBt
  exact h.isRegular hfZ hchar hmono hin.bender hin.benderSL2 hin.fact22 hin.fact23 hin.fact36 h45
    hB hQB hBt hGB (h.centralizer_eq hfZ hchar hmono hB hQB hGB)

theorem isCatalogGroup_of_isSectionOf_of_isKProper {X : Type} [Group X]
    (hK : CFSG.Open.IsKProper X) {H : Subgroup X} (hH : H ≠ ⊤) (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S)
    (hsec : CFSG.SignalizerFunctorTheorem.IsSectionOf S ↥H) : CFSG.Open.IsCatalogGroup S := by
  by_cases hcomm : ∀ a b : S, a * b = b * a
  · exact CFSG.Assembly.abelian_simple S hcomm
  · push Not at hcomm
    obtain ⟨K, f, hf⟩ := hsec
    exact (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hK H hH).surjective_image
      K f hf hcomm

theorem gomiHyp43_of_isPLocal {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    (hK : CFSG.Open.IsKProper X) (hchar : CFSG.Open.IsCharTwoType X)
    (hknown : GomiHyp43OfKnown) {M : Subgroup X}
    (hM : CFSG.IsPLocal 2 M) : GomiHyp43 M := by
  obtain ⟨P, hPne, hP2, rfl⟩ := hM
  apply hknown
  · have htwo : 2 ∣ Nat.card P := by
      rcases hP2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hPne
      · exact h
    exact even_iff_two_dvd.mpr (htwo.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer))
  · exact hchar _ ⟨P, hPne, hP2, rfl⟩
  · intro S _ _ hS hsec
    by_cases hNtop : Subgroup.normalizer (P : Set X) = ⊤
    · have hPnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      have hPtop : P = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
        · exact absurd h hPne
        · exact h
      have htop2 : IsPGroup 2 (⊤ : Subgroup X) := hPtop ▸ hP2
      rw [hNtop] at hsec
      obtain ⟨K, f, hf⟩ := hsec
      have hK2 : IsPGroup 2 K := htop2.to_subgroup K
      have hS2 : IsPGroup 2 S := IsPGroup.of_surjective hK2 f hf
      have hcenter : Subgroup.center S = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
        · have hlt : (⊥ : Subgroup S) < Subgroup.center S := hS2.bot_lt_center
          rw [h] at hlt
          exact absurd hlt (lt_irrefl (⊥ : Subgroup S))
        · exact h
      exact CFSG.Assembly.abelian_simple S fun a b => by
        have hmem : a ∈ Subgroup.center S := by
          rw [hcenter]
          exact Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp hmem b).symm
    · exact isCatalogGroup_of_isSectionOf_of_isKProper hK hNtop S hS hsec

theorem mcBrideGomi_of_inputs (hknown : GomiHyp43OfKnown) (hin : GomiThm45Inputs)
    (h49 : GomiLemma49) : McBrideGomi := by
  intro X _ _ hX hK hchar hblock T hT
  obtain ⟨c, hc⟩ := exists_gnPairChoice_isGomiCharPairGN (G := X)
  refine c.familyControlsFusion_charNormalizers
    (fun T hT hK hne => ⟨(hc T hT hK hne).1.2.1, (hc T hT hK hne).1.2.2.2.1⟩)
    (fun M hM => ?_) hT
  by_contra hs
  obtain ⟨B, hB⟩ := c.hasGomiBlock_of_not_isRegular hc hin h49
    (gomiHyp43_of_isPLocal hX hK hchar hknown hM.1) hs
  exact hblock M ⟨hM.1, fun H hH hMH => le_antisymm (hM.2 hH hMH) hMH⟩ B hB

end CFSG.GroupTheory
