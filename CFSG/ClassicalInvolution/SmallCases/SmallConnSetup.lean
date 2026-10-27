module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Exact
public import CFSG.ClassicalInvolution.Generic.TypeCSetup2Assembly
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.SmallConn

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.ConnectedA2 CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

@[expose] def NoDataBootD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
      ExactMembers (𝒞 K) ∧ LocalOddCentral (𝒞 K) {z}

@[expose] def SmallA2Setup (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → ExactMembers (𝒞 K) ∧ LocalOddCentral (𝒞 K) {z}

section A2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem localOddCentral_of_frame {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hD : HasDatum p f K) (hP1 : A2P1 p f) {F : Type} [Field F] (hF : Nat.card F = p ^ f)
    {A : Subgroup G} {S : Set (Subgroup G)} (Fr : RankFrame F (𝒞 K) A S)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S) (hne : K₁ ≠ K₂) (hnc : ¬ Commutes K₁ K₂) :
    LocalOddCentral (𝒞 K) {z} := by
  have hf : 0 < f := pos_of_five_le hb.five
  have hcard8 : Nat.card A = 8 :=
    le_antisymm (card_le_eight_of_not_bootData hb.member Fr rfl ⟨K₁, h₁⟩ hb.noBoot) Fr.card
  have hP1A := hP1 G K z hb hD F hF A S Fr hcard8 ⟨K₁, h₁, K₂, h₂, hne, hnc⟩
  obtain ⟨z', hz'A, hz'⟩ := frame_involutions hb.member Fr K₁ h₁
  exact Balance.localOddCentral_of_classicalMember hb.odd hf
    (inClass_conjugates hb.member) (exists_single_class K) (Fr.subset h₁) hz'
    (hP1A z' hz'A hz'.ne_one) K (mem_conjClass_self K) z hb.member

theorem smallA2Setup_of_inputs (hD : A2Datum p f) (hP1 : A2P1 p f) : SmallA2Setup p f := by
  intro G _ _ _ K z hb
  have hDat := hD G K z hb
  refine ⟨exactMembers_of_inputs hb hDat hP1, ?_⟩
  have hf : 0 < f := pos_of_five_le hb.five
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hb.member
  obtain ⟨L₁, L₂, t, h₁, h₂, hLD⟩ := id hDat
  rcases hLD with hLD | hLD
  · have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, -⟩ := hLD.exists_rankFrame
      (CFSG.ClassicalInvolution.Generic.DeltaClosure.odd_card_galoisField hb.odd hb.five)
      (by rw [hF]; exact hb.five) hΩ.conjInvariant h₁ h₂
    exact localOddCentral_of_frame hb hDat hP1 hF Fr hs₁ hs₂ hne hnc
  · have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), pow_mul']
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, -⟩ :=
      hLD.exists_rankFrame hK hb.odd hb.five hΩ.conjInvariant h₁ h₂
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield hK
    exact localOddCentral_of_frame hb hDat hP1 hF Fr hs₁ hs₂ hne hnc

theorem smallConnectedA2_of_setup (hs : SmallA2Setup p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) : SmallConnectedA2 p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  have hb : Branch p f K z := ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ, hB, hA2⟩
  obtain ⟨hex, hp1⟩ := hs G K z hb
  have S : RouteDSetup p f K z :=
    mk_routeDSetup hp2 hq hz hBelow ((deltaConnected_iff K).mp hΔ) hex hp1
  refine Or.inl (oddLieType_of_lieSystem (f := f) (Ω := 𝒞 K) hp2 hnab ?_)
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hsh⟩ | hm
  · exact hshape a t n G hnab K z S hsh
  · exact hmulti G hnab K z S hm

end A2

theorem noDataD_of_noDataBootD (h : NoDataBootD p f) : NoDataD p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD hB
  obtain ⟨hex, hp1⟩ := h G hnab hp2 hq K z hz hBelow h3 h4 hD hB
  exact (deltaConnected_iff K).mpr
    (routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hp1)

theorem smallA2Setup_of_noDataBootD (h : NoDataBootD p f) : SmallA2Setup p f := by
  intro G _ _ _ K z hb
  exact h G hb.nonabelian hb.odd hb.five K z hb.member hb.below hb.rank hb.notFourGenerated
    (dConnected_of_deltaConnected hb.connected) hb.noBoot

theorem smallTypeCSetup_of_noDataBootD (h : NoDataBootD p f) : SmallTypeCSetup p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB _
  exact h G hnab hp2 hq K z hz hBelow h3 h4 (dConnected_of_deltaConnected hΔ) hB

theorem noDataBootD_of_seeds (hND : NoDataD p f) (hA : SmallA2Setup p f)
    (hC : SmallTypeCSetup p f) : NoDataBootD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hΔ := hND G hnab hp2 hq hBelow K z hz h3 h4 hD hB
  by_cases hA2 : A2Configuration z K
  · exact hA G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ, hB, hA2⟩
  · exact hC G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2

theorem noDataBootD_iff :
    NoDataBootD p f ↔ NoDataD p f ∧ SmallA2Setup p f ∧ SmallTypeCSetup p f :=
  ⟨fun h => ⟨noDataD_of_noDataBootD h, smallA2Setup_of_noDataBootD h,
    smallTypeCSetup_of_noDataBootD h⟩, fun h => noDataBootD_of_seeds h.1 h.2.1 h.2.2⟩

theorem noDataBootD_of_inputs (hND : NoDataD p f) (hD : A2Datum p f) (hP1 : A2P1 p f)
    (hexotic : ExoticLeviBlock p f) (hC : TypeCSetup.TypeCBalancedFrame p f) :
    NoDataBootD p f :=
  noDataBootD_of_seeds hND (smallA2Setup_of_inputs hD hP1)
    (TypeCSetup.smallTypeCSetup_of_frame hexotic hC)

end CFSG.ClassicalInvolution.SmallConn
