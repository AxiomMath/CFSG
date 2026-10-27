module

public import CFSG.CGT.Stroth77.Section223Step
public import CFSG.CGT.Stroth77.Section223IndexFour
public import CFSG.CGT.Stroth77.Extension22Data
public import CFSG.CGT.Stroth77.Extension215
public import CFSG.CGT.Stroth77.Extension24IndexTwo
public import CFSG.CGT.Stroth77.Extension24
public import CFSG.CGT.Stroth77.Extension25
public import CFSG.CGT.Stroth77.Extension27
public import CFSG.CGT.Stroth77.Extension28Basic
public import CFSG.CGT.Stroth77.Extension28
public import CFSG.CGT.Stroth77.Extension29IndexTwo
public import CFSG.CGT.Stroth77.Extension29IndexFour
public import CFSG.CGT.Stroth77.Extension212Two
public import CFSG.CGT.Stroth77.Extension212Four
public import CFSG.CGT.Stroth77.Extension213
public import CFSG.CGT.Stroth77.Extension214
public import CFSG.CGT.Stroth77.Extension216
public import CFSG.CGT.Stroth77.Extension217
public import CFSG.CGT.Stroth77.Extension218
public import CFSG.CGT.Stroth77.Extension218Four
public import CFSG.CGT.Stroth77.Extension219
public import CFSG.CGT.Stroth77.Extension220IndexTwo
public import CFSG.CGT.Stroth77.Extension220
public import CFSG.CGT.Stroth77.Extension221
public import CFSG.CGT.Stroth77.Extension222
public import CFSG.CGT.Stroth77.Extension222Four
public import CFSG.CGT.Stroth77.Extension23Final
public import CFSG.CGT.Stroth77.Extension26Final
public import CFSG.CGT.Stroth77.Extension210Final
public import CFSG.CGT.Stroth77.Extension211Final
public import CFSG.CGT.Stroth77.Extension210Four
public import CFSG.CGT.Stroth77.Section224
public import CFSG.CGT.Stroth77.Stroth31Proof
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.GH74.Defs
public import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem exists_hasStrothTypeOver_of_or {S : Type} [Group S] {B C : Subgroup S}
    {τ τ₁ τ₂ : StrothTypeIndex} {D : StrothTypeData B τ}
    (h : HasStrothTypeOver D C τ₁ ∨ HasStrothTypeOver D C τ₂) :
    ∃ τ' : StrothTypeIndex, HasStrothTypeOver D C τ' :=
  h.elim (fun h => ⟨τ₁, h⟩) (fun h => ⟨τ₂, h⟩)

theorem strothExtStep : StrothExtStep := by
  intro S _ _ B C S' τ D hk hτ hBC hC hrel hexp hL hH hcS
  have hne : C ≠ B := by
    rintro rfl
    have hpos : 0 < Nat.card C := Nat.card_pos
    omega
  suffices key : ∃ τ' : StrothTypeIndex, HasStrothTypeOver D C τ' by
    obtain ⟨τ', D', h1, h2, h3, h4⟩ := key
    exact ⟨τ', D', h1, h2, h3, h4⟩
  rcases hrel with hrel | hrel
  ·
    cases τ with
    | t100 m =>
      obtain ⟨d, -, -, ⟨D', h1, h2, h3, h4, -⟩ | ⟨D', h1, h2, h3, h4, -⟩⟩ :=
        strothTypeData_t300_or_t310_of_data D hBC hC hrel hL hH hcS hne
      · exact ⟨_, D', h1, h2, h3, h4⟩
      · exact ⟨_, D', h1, h2, h3, h4⟩
    | t101 s =>
      exact (false_of_index_two_t101_of_data D hBC hC hrel hL hH hcS).elim
    | t110 t =>
      exact (false_of_index_two_t110_of_data D hBC hC hrel hL hH hcS).elim
    | t111 t =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t321_or_t331_of_noInvolutionsCentralizing_t111 D hBC hC hrel hL hH hcS
          hne)
    | t120 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t320_or_t330_of_data D hBC hC hrel hL hH hcS)
    | t121 m hm =>
      exact (false_of_index_two_t121_of_data D hBC hC hrel hL hH hcS).elim
    | t130 m hm =>
      exact (false_of_index_two_of_data_t130 D hBC hC hrel hL hH hcS).elim
    | t131 m hm =>
      exact (false_of_index_two_t131_of_data D hBC hC hrel hL hH hcS).elim
    | t200 m =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t100_or_t110_of_noInvolutionsCentralizing D hBC hC hrel hL hH hcS hne)
    | t201 m =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t101_or_t111_of_noInvolutionsCentralizing D hBC hC hrel hL hH hcS hne)
    | t210 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t121_or_t131_of_noInvolutionsCentralizing_t210 D hBC hC hrel hL hH hcS
          hne)
    | t211 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t120_or_t130_of_noInvolutionsCentralizing_t211 D hBC hC hrel hL hH hcS
          hne)
    | t220 s hs =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t120_or_t130_of_data D hBC hC hrel hL hH hcS)
    | t221 s hs =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t121_or_t131_of_noInvolutionsCentralizing D hBC hC hrel hL hH hcS)
    | t230 s hs =>
      exact (false_of_index_two_t230_of_data D hBC hC hrel hL hH hcS).elim
    | t231 s hs =>
      exact (false_of_index_two_t231_of_data D hBC hC hrel hL hH hcS).elim
    | t300 n =>
      have hn : 1 ≤ n := hk 0
      exact (false_of_index_two_t300_of_data D hn hBC hC hrel hL hH hcS).elim
    | t310 m hm =>
      exact (false_of_index_two_t310_of_data D hBC hC hrel hL hH hcS).elim
    | t320 m hm =>
      exact (false_of_index_two_t320_of_data D hBC hC hrel hL hH hcS).elim
    | t330 m hm =>
      exact (false_of_index_two_of_data_t330 D hBC hC hrel hL hH hcS).elim
    | t321 =>
      exact (false_of_index_two_t321_of_data D hBC hC hrel hL hH hcS).elim
    | t331 =>
      exact (false_of_index_two_t331_of_data D hBC hC hrel hL hH hcS).elim
  ·
    cases τ with
    | t100 m =>
      obtain ⟨e, f, -, -, ⟨D', h1, h2, h3, h4, -⟩ | ⟨D', h1, h2, h3, h4, -⟩⟩ :=
        strothTypeData_t200_or_t201_of_data D hBC hC hrel hL hH hcS hne
      · exact ⟨_, D', h1, h2, h3, h4⟩
      · exact ⟨_, D', h1, h2, h3, h4⟩
    | t101 s =>
      have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr fun h => hτ (by rw [h])
      exact (false_of_index_four_t101_of_data D hs hBC hC hrel hL hH hcS).elim
    | t110 t =>
      exact (false_of_index_four_t110_of_data D hBC hC hrel hL hH hcS).elim
    | t111 t =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t210_or_t211_of_data_t111 D hBC hC hrel hL hH hcS)
    | t120 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t220_or_t221_of_data D hBC hC hrel hL hH hcS)
    | t121 m hm =>
      exact (false_of_index_four_t121_of_data D hBC hC hrel hL hH hcS).elim
    | t130 m hm =>
      exact (false_of_index_four_of_data_t130 D hBC hC hrel hL hH hcS).elim
    | t131 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t230_or_t231_of_noInvolutionsCentralizing D hBC hC hrel hL hH hcS)
    | t200 m =>
      exact (false_of_index_four_t200_of_data D hk hBC hC hrel hexp hL hH hcS).elim
    | t201 m =>
      exact (false_of_index_four_t201_of_data D hk hBC hC hrel hexp hL hH hcS).elim
    | t210 m hm =>
      exact (false_of_index_four_t210_of_data D hBC hC hrel hexp hL hH hcS).elim
    | t211 m hm =>
      exact (false_of_index_four_t211_of_data D hBC hC hrel hexp hL hH hcS).elim
    | t220 s hs =>
      exact (false_of_index_four_t220_of_data D hk hBC hC hrel hexp hL hH hcS).elim
    | t221 s hs =>
      exact (false_of_index_four_t221_of_data D hBC hC hrel hexp hL hH hcS).elim
    | t230 s hs =>
      exact (false_of_index_four_t230_of_data D hBC hC hrel hL hH hcS).elim
    | t231 s hs =>
      exact (false_of_index_four_t231_of_data D hBC hC hrel hL hH hcS).elim
    | t300 n =>
      have hn : 1 ≤ n := hk 0
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t100_or_t101_of_noInvolutionsCentralizing D hn hBC hC hrel hL hH hcS)
    | t310 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t110_or_t111_of_noInvolutionsCentralizing_t310 D hBC hC hrel hL hH hcS)
    | t320 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t120_or_t121_of_data D hBC hC hrel hL hH hcS)
    | t330 m hm =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t130_or_t131_of_data D hBC hC hrel hL hH hcS)
    | t321 =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t120_or_t121_of_data_t321 D hBC hC hrel hL hH hcS)
    | t331 =>
      exact exists_hasStrothTypeOver_of_or
        (hasStrothTypeOver_t130_or_t131_of_noInvolutionsCentralizing_t331 D hBC hC hrel hL hH hcS)

theorem stroth_2_23_frame :
    ∀ {G : Type} [Group G] [Finite G], StrothFrame G →
      ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
        F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) :=
  stroth_2_23_frame_of_strothExtStep strothExtStep

end CFSG.CGT.Stroth77
