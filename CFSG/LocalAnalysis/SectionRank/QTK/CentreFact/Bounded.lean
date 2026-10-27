module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2236
public import Certificates.Certificate2237
public import Certificates.Certificate2239
public import Certificates.Certificate2281
public import Certificates.Certificate3169
public import Certificates.Certificate8150
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
import CFSG.RankThree.PartTwo.Census.Sporadic.J3
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.Sporadic.J3
import CFSG.Sporadic.Schreier.PairJ3Faithful
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.Section
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (localRank)

theorem oddBound_three_of_g2_three
    {S : Type} [Group S] [Finite S] (h : ChevalleyExceptionalModel S .G2 3 1) : OddBound 3 S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, one_pos⟩
  have hq : q.card = 3 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      exact hq.symm.le
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b₁⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by decide) K (by rw [hq, hK]; rfl)
  obtain ⟨b₂⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by decide) (ZMod 3)
    (by rw [hq, Nat.card_zmod])
  exact small_oddBound_of_mulEquiv (by norm_num) (e.trans (b₁.trans b₂.symm))
    (small_oddBound_of_localRank (by norm_num)
      CFSG.RankThree.PartTwo.Census.Carrier.G2Three.localRank_three_adjointQuotient)

theorem oddBound_three_of_u4_three {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSU 4 3 1) : OddBound 3 S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  exact small_oddBound_of_mulEquiv (by norm_num) e
    (small_oddBound_of_localRank (by norm_num)
      (CFSG.RankThree.PartTwo.Census.localRankThreeU43 K hK9))

open CFSG.Sporadic.Schreier in
theorem localRank_three_j3P_le_two :
    localRank 3 j3P ≤ 2 :=
  CFSG.RankThree.PartTwo.Census.localRank_three_le_two_of_centralizer fun t ht h9 => by
    rw [CFSG.RankThree.PartTwo.Census.card_centralizer_j3P ht] at h9
    exact absurd h9 (by norm_num)

theorem oddBound_three_of_J3
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .J3) : OddBound 3 S :=
  small_oddBound_of_mulEquiv (by norm_num) (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)
    (small_oddBound_of_localRank (by norm_num) localRank_three_j3P_le_two)

theorem oddBound_of_J3_of_ne_three {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .J3) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from
    CFSG.Sporadic.J3.card_J3]
  intro hd
  have h2 : r ^ 2 ∣ 2 ^ 7 * 3 ^ 5 * 1615 := by
    rw [show 2 ^ 7 * 3 ^ 5 * 1615 = 50232960 by norm_num]
    exact (pow_dvd_pow r (by norm_num : 2 ≤ 3)).trans hd
  exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
    (CFSG.SectionRank.not_sq_dvd_of_bound (B := 41) (by norm_num) (by norm_num) (by decide) hr hr2
      hr3) h2

theorem oddBound_of_J3
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .J3) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : OddBound r S := by
  by_cases hr3 : r = 3
  · subst hr3
    exact oddBound_three_of_J3 e
  · exact oddBound_of_J3_of_ne_three e hr hr2 hr3

end CFSG.SectionRank.QTK.CentreFact
