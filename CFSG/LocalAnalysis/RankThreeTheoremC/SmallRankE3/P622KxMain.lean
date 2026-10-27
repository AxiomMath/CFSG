module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxRank1
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxChev2
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxJ1
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxSpor
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFactDihedralTypeAut KFactReeSylowTwo KFactReeL28
  KFactReeBorel KFact2024 KFact2401Three KFact2314 KFact1019 KFact2025 KFact131
  KFactParabolicGen KFact2715 KFactParabolicCover KFactSporThree KFact2401Spor KFactSporLocal
  KFactJ1Sylow KFactJ1L27 IsDihedralTypeIndex IsReeIndex
  exists_not_comm_of_section_bot)

variable {G : Type} [Group G] [Finite G]

namespace P622KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem isCatalogGroup (c : P622KxCfg p P M x z T S L) : IsCatalogGroup ↥L := by
  haveI : IsSimpleGroup ↥L := c.isSimple
  have hKH : CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) :=
    fun K L' _ _ hsimple _ =>
      k631_isKGroup_centralizer c.setting c.conf.failure.point.ne_one K (L'.subgroupOf K) hsimple
  have hKL : CFSG.Open.IsKGroup ↥L := hKH.of_le c.le_C
  exact hKL.isCatalogGroup_of_surjective ⊤ (exists_not_comm_of_section_bot c.simple)
    (Subgroup.topEquiv (G := ↥L)).toMonoidHom (Subgroup.topEquiv (G := ↥L)).surjective

theorem false_of_nonSporadic (hL613 : P622L613) (hp3 : p ≠ 3) (hD : KFactDihedralTypeAut)
    (hE : KFactReeSylowTwo) (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025)
    (h131 : KFact131) (hgen : KFactParabolicGen) (h2715 : KFact2715)
    (hcov : KFactParabolicCover) (c : P622KxCfg p P M x z T S L)
    (hnonspor : ¬ ∃ s : TauCeti.SporadicName,
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : False := by
  by_cases hC2 : IsChevSimple 2 ↥L
  · exact c.false_of_chev2 hL613 hp3 h131 hgen h2715 hcov hC2
  obtain ⟨i, ⟨e⟩⟩ := c.isCatalogGroup
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := exists_not_comm_of_section_bot c.simple
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have h7 : 7 ≤ n := by
      by_contra hlt
      apply hC2
      right
      refine ⟨TauCeti.CFSGIndex.alternating n hn, ?_, ⟨e⟩⟩
      show (n = 5 ∧ (2 = 2 ∨ 2 = 5)) ∨ (n = 6 ∧ (2 = 2 ∨ 2 = 3)) ∨ (n = 8 ∧ 2 = 2)
      have : 5 ≤ n := hn
      omega
    exact c.false_of_alt hL613 hp3 h2024 h2401 h7 ⟨e⟩
  | lie d =>
    have hd2 : d.1.characteristic ≠ 2 := by
      intro h2
      apply hC2
      left
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact h2
    by_cases hdih : IsDihedralTypeIndex d.1
    · refine c.false_of_dihedralType hD hp3 ?_
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact hdih
    by_cases hree : IsReeIndex d.1
    · refine c.false_of_ree hL613 hE h27 hB hp3 ?_
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact hree
    exact c.false_of_lieOdd hL613 hp3 h2314 h1019 h2025 h2401 d hd2 ⟨e⟩ hdih hree
  | sporadic s => exact hnonspor ⟨s, ⟨e⟩⟩

theorem false_of_sporadic (hL613 : P622L613) (hp3 : p ≠ 3) (hS3 : KFactSporThree)
    (h2401 : KFact2401Spor) (hloc : KFactSporLocal) (hE : KFactJ1Sylow) (h27 : KFactJ1L27)
    (hOp : rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥) (c : P622KxCfg p P M x z T S L)
    {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : False := by
  by_cases h3 : CFSG.Open.pRank 3 L ≤ 1
  · have hs : s = .J1 := hS3 G L s c.isSimple.toNontrivial e h3
    subst hs
    exact c.false_of_j1 hE h27 hp3 e
  · have h32 : 2 ≤ CFSG.Open.pRank 3 L := by omega
    exact c.false_of_sporadic_rank3 hL613 hp3 h2401 hloc hOp e h32

end P622KxCfg

theorem p622KxLarge_of_cases (hL613 : P622L613) (hD : KFactDihedralTypeAut)
    (hE : KFactReeSylowTwo) (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025)
    (h131 : KFact131) (hgen : KFactParabolicGen) (h2715 : KFact2715)
    (hcov : KFactParabolicCover) (hS3 : KFactSporThree) (h2401S : KFact2401Spor)
    (hloc : KFactSporLocal) (hJ1 : KFactJ1Sylow) (hJ27 : KFactJ1L27) : P622KxLarge := by
  intro G _ _ hS hD1 hD2 hU0 p hp3 P M x z T S hf h614 hmax hle hbot L hLs hLC hzL hrk hLM hN
  have hc : P622Conf p P M x z T S := ⟨hf, h614, hmax, hle⟩
  have c : P622KxCfg p P M x z T S L := ⟨hS, hD1, hD2, hU0, hc, hLs, hLC, hzL, hrk, hLM, hN⟩
  by_cases hspor : ∃ s : TauCeti.SporadicName,
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
  · obtain ⟨s, e⟩ := hspor
    exact c.false_of_sporadic hL613 hp3 hS3 h2401S hloc hJ1 hJ27 hbot e
  · exact c.false_of_nonSporadic hL613 hp3 hD hE h27 hB h2024 h2401 h2314 h1019 h2025 h131 hgen
      h2715 hcov hspor

theorem p622Kx_of_cases (h3 : P622KxThree) (hL613 : P622L613) (hD : KFactDihedralTypeAut)
    (hE : KFactReeSylowTwo) (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025)
    (h131 : KFact131) (hgen : KFactParabolicGen) (h2715 : KFact2715)
    (hcov : KFactParabolicCover) (hS3 : KFactSporThree) (h2401S : KFact2401Spor)
    (hloc : KFactSporLocal) (hJ1 : KFactJ1Sylow) (hJ27 : KFactJ1L27) : P622Kx :=
  p622Kx_of_three_large h3 (p622KxLarge_of_cases hL613 hD hE h27 hB h2024 h2401 h2314 h1019 h2025
    h131 hgen h2715 hcov hS3 h2401S hloc hJ1 hJ27)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
