module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxChev2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxJ1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSpor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxRank1

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie IsChevSimple)

variable {G : Type} [Group G] [Finite G]

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem isCatalogGroup (c : KxCfg p P M x z T S L) : IsCatalogGroup ↥L := by
  have hS := c.conf.config.situation
  have hx := c.conf.config.point
  haveI : IsSimpleGroup ↥L := c.isSimple
  have hKL : CFSG.Open.IsKGroup ↥L := (s622_isKGroup_centralizer hS hx).of_le c.le_C
  exact hKL.isCatalogGroup_of_surjective ⊤ (exists_not_comm_of_section_bot c.simple)
    (Subgroup.topEquiv (G := ↥L)).toMonoidHom (Subgroup.topEquiv (G := ↥L)).surjective

theorem false_of_nonSporadic (hL613 : L613) (hD : KFactDihedralTypeAut) (hE : KFactReeSylowTwo)
    (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024) (h2401 : KFact2401Three)
    (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025) (h131 : KFact131)
    (hgen : KFactParabolicGen) (h2715 : KFact2715) (hcov : KFactParabolicCover)
    (c : KxCfg p P M x z T S L)
    (hnonspor : ¬ ∃ s : TauCeti.SporadicName,
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : False := by
  by_cases hC2 : IsChevSimple 2 ↥L
  · exact c.false_of_chev2 hL613 h131 hgen h2715 hcov hC2
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
    exact c.false_of_alt hL613 h2024 h2401 h7 ⟨e⟩
  | lie d =>
    have hd2 : d.1.characteristic ≠ 2 := by
      intro h2
      apply hC2
      left
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact h2
    by_cases hdih : IsDihedralTypeIndex d.1
    · refine c.false_of_dihedralType hD ?_
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact hdih
    by_cases hree : IsReeIndex d.1
    · refine c.false_of_ree hL613 hE h27 hB ?_
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact hree
    exact c.false_of_lieOdd hL613 h2314 h1019 h2025 h2401 d hd2 ⟨e⟩ hdih hree
  | sporadic s => exact hnonspor ⟨s, ⟨e⟩⟩

end KxCfg

theorem KxCfg.false_of_sporadic {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
    {T S L : Subgroup G} (h313 : GL83NormalElementaryRankFour) (hS3 : KFactSporThree)
    (h2401 : KFact2401Spor) (hM11 : KFactSporM11) (hE : KFactJ1Sylow) (h27 : KFactJ1L27)
    (hRest : KxSporadicCore) (hOp : rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥)
    (c : KxCfg p P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : False := by
  by_cases h3 : CFSG.Open.pRank 3 L ≤ 1
  · have hs : s = .J1 :=
      hS3 G L s c.isSimple.toNontrivial e h3
    subst hs
    exact c.false_of_j1 hE h27 e
  · have h32 : 2 ≤ CFSG.Open.pRank 3 L := by omega
    obtain ⟨hY1, hY2⟩ := c.pCoreOf_inf_facts
    exact hRest G p P M x z T S L c ⟨s, e⟩ h32
      (fun U hUL hU1 hU2 => c.localRank_three_le h313 h2401 hM11 e h32 hUL hU1 hU2)
      hY1 hY2 c.normalizer_pCoreOf_inf_eq hOp

theorem s622Kx_of_cases (hL613 : L613) (h313 : GL83NormalElementaryRankFour)
    (hD : KFactDihedralTypeAut) (hE : KFactReeSylowTwo)
    (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024) (h2401 : KFact2401Three)
    (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025) (h131 : KFact131)
    (hgen : KFactParabolicGen) (h2715 : KFact2715) (hcov : KFactParabolicCover)
    (hS3 : KFactSporThree) (h2401S : KFact2401Spor) (hM11 : KFactSporM11)
    (hJ1 : KFactJ1Sylow) (hJ27 : KFactJ1L27) (hRest : KxSporadicCore) : S622Kx := by
  intro G _ _ p P M x z hS hx hz h614 T hT hOp L hLs hLC hzL hrk hLM hN
  obtain ⟨S, hS622⟩ := exists_s622Conf (⟨hS, hx, hz, h614, hT⟩ : S62Config p P M x z T)
  have c : KxCfg p P M x z T S L := ⟨hS622, hLs, hLC, hzL, hrk, hLM, hN⟩
  by_cases hspor : ∃ s : TauCeti.SporadicName,
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
  · obtain ⟨s, e⟩ := hspor
    exact c.false_of_sporadic h313 hS3 h2401S hM11 hJ1 hJ27 hRest hOp e
  · exact c.false_of_nonSporadic hL613 hD hE h27 hB h2024 h2401 h2314 h1019 h2025 h131 hgen h2715
      hcov hspor

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
