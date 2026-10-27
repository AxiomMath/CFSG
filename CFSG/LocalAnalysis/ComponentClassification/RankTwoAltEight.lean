module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightDW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEIdent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenCent

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

theorem NormPair.exists_hom_eight
    {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} (np : NormPair A R T g 8)
    (hc : Sec3 A R T g) (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h34 : Asc08Lemma34) (h5 : AltChildAt 5) :
    ∃ (ψA : A ≃* alternatingGroup (Fin 8)) (ψB : rightConjugate A g ≃* alternatingGroup (Fin 8))
      (Φ : alternatingGroup (Fin (8 + 4)) →* G), Function.Injective Φ ∧
        Φ.range = A ⊔ rightConjugate A g ∧
        (∀ z, Φ (liftA (by norm_num) z) = ((ψA.symm z : A) : G)) ∧
        ∀ z, Φ (liftB (by norm_num) z) = ((ψB.symm z : rightConjugate A g) : G) := by
  obtain ⟨ψD⟩ := np.nonempty_DW_equiv_eight hc hK h4 h32 h34 h5
  exact np.exists_hom_of_DW le_rfl ψD hc h32

theorem AltGenSetting.rankTwoX_eq_eight
    {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
    {Φ : alternatingGroup (Fin (8 + 4)) →* G} (s : AltGenSetting A R T g 8 Φ)
    (h34 : Asc08Lemma34) (hGA : Asc76X.GoldschmidtTheoremA) :
    rankTwoX A = A ⊔ rightConjugate A g :=
  s.rankTwoX_eq_of_local h34 (s.normalizer_le (by norm_num)) s.rootFusionAt_eight
    (s.typeTwoCentralizerAt_of hGA (s.normalizer_le (by norm_num)) s.rootFusionAt_eight)

end CFSG.ComponentClassification.RankTwoAlt
