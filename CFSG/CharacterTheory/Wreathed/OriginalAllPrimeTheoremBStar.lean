module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeChapterII
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQD
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFacts
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSec11
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NFacts
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeStationaryCoverage
public import CFSG.LocalAnalysis.ABGTheoremB.V4Assembly
public import CFSG.LocalAnalysis.ABGTheoremB.TheoremBStarQD
public import CFSG.LocalAnalysis.ABGTheoremB.QGroupSignalizer
public import CFSG.LocalAnalysis.ABGTheoremB.II61QBridge

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open SmallerRecognitionOriginalField
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure WreathedBStarInputs (σ : Setting G) : Prop where
  ii42 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII42Input σ J
  ii46 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII46Input σ J
  ii49 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII49Input σ J
  ii49i : ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X → σ.D ≤ Subgroup.normalizer (X : Set G) →
    ∀ y ∈ X, σ.x₂ * y * σ.x₂⁻¹ * y⁻¹ ∈ σ.ON

theorem II61D_of (σ : Setting G) : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.oddCore H →
      IsPStable r H :=
  fun _ _ hW r hr hr2 hOp _ => haveI : Fact r.Prime := ⟨hr⟩; isPStable_of_isDGroup hr2 hW.1 hOp

theorem II61Q_of
    {σ : Setting G} (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H := by
  intro r hr hdiv hrp H hH hO
  have : Fact r.Prime := ⟨hr⟩
  exact isPStable_of_qGroup (σ.prime_ne_two_of_dvd_ON hr hdiv)
    (σ.familyL_qGroupStanding hσ hII hr hdiv hH hO) (σ.not_dvd_q_of_ne_p hσ hr hrp)
    (σ.familyL_pCore_ne_bot hH) (σ.familyL_qGroupStabilityFacts hσ hII hr hdiv hH)

theorem wreathedSetting_theoremBStar_of_inputs
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (hI : WreathedBStarInputs (wreathedSetting n S e p f)) :
    (wreathedSetting n S e p f).TheoremBStar := by
  set σ := wreathedSetting n S e p f with hσdef
  have hσ : σ.IsValid := wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hh : σ.height ≠ 1 := by
    change n ≠ 1
    omega
  have hII : σ.ChapterIIFacts := wreathedSetting_chapterIIFacts hnonab n hn S e hfour p f hp hpodd
    hf hq hlocal hrec hsd
    (wreathedSetting_localQD_charPower hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec)
    (wreathedSetting_not_qd_of_cover hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec)
  have hQC : σ.QCoverFact :=
    wreathedSetting_qCoverFact hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hT : σ.TIFacts := wreathedSetting_tiFacts_of hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hN : σ.IVNFacts :=
    wreathedSetting_ivNFacts hnonab n hn S e hfour p f hp hpodd hf hq hlocal hII
  have h32 := σ.lemmaIV32_of hσ hII
  have h61 := σ.propIV61_of hσ hII
  have h62 := σ.propIV62 hσ hII
  have h71 := σ.propIV71_of_IVNFacts hσ hII hN
  have h81 := σ.lemmaIV81 hσ hII
  have h83 := σ.lemmaIV83 hσ hII
  have h91 : σ.PropIV91 := σ.propIV91_of_height_ne_one' hσ hII hN hh
  have h₁ : ∀ r : ℕ, σ.HypIV7 r → r = σ.p := σ.stage_one hσ hII hN h91 (II61Q_of hσ hII)
  have hV21 := σ.corollaryV21 hσ hII h₁ hN.sylow_quaternion_element
  have h41 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.PropV41 J := fun J hJ =>
    V4.propV41_of hσ hII hJ hN hT (hI.ii42 J hJ) (hI.ii46 J hJ) (hI.ii49 J hJ) h₁
      (σ.qGroupSignalizerInput_of hσ hII.toNStructure hI.ii49i)
      (V4.dGroupSignalizerInput_of_height_ne_one hh)
  have h45 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.LemmaV45 J := fun J hJ =>
    V4.lemmaV45_of hσ hII hJ hN hT (hI.ii42 J hJ) (hI.ii46 J hJ) (hI.ii49 J hJ) h₁
  have h₂ : ¬ σ.HypIV7 σ.p := V56.propV61 hσ hII hV21 h41 h45
    (σ.cStructure_of hσ hN hT) (σ.lemmaV31_of hσ hII hN) (σ.lemmaV33_of hσ hII hN)
    (σ.propR1Input_of hσ hII hN
      (wreathedSetting_r1NFacts hnonab n hn S e hfour p f hp hpodd hf hq hlocal))
    (σ.propR2Input_of hσ h91 (II61D_of σ)
      (wreathedSetting_h_R23 hnonab n hn S e hfour p f hp hpodd hf hq hlocal))
    h32 h61 h62 h71 h81 h83 h91
  have hV61 := σ.corollaryV61 hσ hII (σ.notTotallyInvertedOrdinary_of_stages h₁ h₂)
    hN.propIV51 hN.sylow_quaternion_element
  have h₃ := TotallyInverted.not_totallyInverted_of_height_ne_one hσ hh hII hV61 hT hQC
    (TotallyInverted.Inputs.dGroupFourFusion_of_wreathed G S e hn)
    (fun _ Δ => wreathedSetting_sec11Inputs hnonab n hn S e hfour p f hp hpodd hf hq hlocal Δ)
  exact σ.theoremBStar_of_stages h₁ h₂ h₃

theorem stationaryCoverageStatement_of_bStarInputs
    (hI : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      SmallerWreathedRecognition G →
      CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G →
      ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
        ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
      ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
          .PSL 2 p f →
        WreathedBStarInputs (wreathedSetting n S e p f)) :
    CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement :=
  stationaryCoverageStatement_of_theoremBStar
    fun G _ _ _ hnonab hrec hsd n hn S e hfour p f hp hpodd hf hq hlocal =>
      wreathedSetting_theoremBStar_of_inputs hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec
        hsd (hI G hnonab hrec hsd n hn S e hfour p f hp hpodd hf hq hlocal)

end CFSG.Wreathed.OriginalAllPrime
