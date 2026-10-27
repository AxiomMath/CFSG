module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5End
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSideInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem isPGroup_autI {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Subgroup G} (hK : IsPGroup 2 K) : IsPGroup 2 (autI hV K) := by
  unfold autI
  refine IsPGroup.map ?_ _
  exact hK.comap_of_injective (Subgroup.normalizer (V : Set G)).subtype
    (Subgroup.normalizer (V : Set G)).subtype_injective

theorem isSylowTwoOf_of_le_of_le {Ω : Type*} [Group Ω] [Finite Ω] {P P' Y : Subgroup Ω}
    (hP : IsSylowTwoOf P Y) (hPP' : P ≤ P') (hP'Y : P' ≤ Y) (hP'2 : IsPGroup 2 P') :
    IsSylowTwoOf P' Y := by
  refine ⟨hP'Y, hP'2, fun h => hP.2.2 ?_⟩
  have := Subgroup.relIndex_mul_relIndex P P' Y hPP' hP'Y
  have h' : (P'.subgroupOf Y).index ∣ (P.subgroupOf Y).index := Dvd.intro_left _ this
  exact (Dvd.dvd.trans h h')

@[expose] def FFPairStep : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      ∃ C₁ C₂ : Subgroup G, FFPairData M T hU I C₁ C₂

@[expose] def FFBaumStar : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      autI hU (baum T) ≤ autI hU (thompsonJ M)

theorem ffRankTwoInput_of_pairStep
    (hP : FFPairStep) (hB : FFBaumStar) : FFRankTwoInput := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hcon T hT hNT hC3 hU I hMN hI2 hcard hJM hSyl hperm hfam
  obtain ⟨C₁, C₂, hdat⟩ := hP d G P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl
    hperm hfam
  have hBS := hB d G P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam
  have hSylB : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)) :=
    isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
      (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
  exact false_of_pair_data hc hstr hAll.onlyL34At hT hNT hMN hfam hcard hSylB hJM hC3 hdat

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
