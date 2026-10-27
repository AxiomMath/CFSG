module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248RankOneHolds
import all CFSG.LocalAnalysis.GLTheoremA.CatA.H248RankOneHolds
import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019AmbAut
import CFSG.RankThree.PartOne.N143.SectionListLie
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.ClassicalInvolution.Orders.Classical
import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
import CFSG.LieType.Simplicity.Classical
import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open

theorem coreSmallVac_of_i713 (hI : GL83.I_7_13_1) : CoreSmallVac := by
  intro p hp hp2 hp3 S _ _ d ⟨e⟩ hshape A hA
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  by_contra hlt
  push Not at hlt
  obtain ⟨d1, hv⟩ := d
  rcases hshape with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  ·
    obtain rfl : d1 = .A 1 Q := hd
    obtain ⟨hpQ, hfQ⟩ := CFSG.LocalAnalysis.GLTheoremA.S2019.primePower_eight Q hQ
    have hm : StatedClassicalModel S .PSL 2 2 3 := by
      simpa [hpQ, hfQ] using CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hv e
    have hS : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_PSL_simplicity S 2 2 3 hm).2
    refine false_of_pRank_le_one hI hp hp2 hS
      (exists_noncomm_of_elemAbelian_cube hp hS hA hlt)
      ⟨.lie ⟨.A 1 Q, hv⟩, ⟨e⟩⟩ ?_ hA hlt
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p S]
    refine CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd ?_
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight hm]
    exact CFSG.Quasithin.H13.NQCore.not_sq_dvd_of_squarefree (α := 3) (β := 2) (u := 7)
      (hn := by norm_num) hp hp5
      ((by norm_num : Nat.Prime 7).squarefree)
  ·
    obtain rfl : d1 = .twistedA 3 Q := hd
    rcases hQ with hQ | hQ
    · obtain ⟨hpQ, hfQ⟩ := CFSG.LocalAnalysis.GLTheoremA.S2019.primePower_two Q hQ
      have hm : StatedClassicalModel S .PSU 4 2 1 := by
        simpa [hpQ, hfQ] using CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
      have hS : IsSimpleGroup S :=
        (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S 4 2 1 hm).2
      refine false_of_pRank_le_one hI hp hp2 hS
        (exists_noncomm_of_elemAbelian_cube hp hS hA hlt)
        ⟨.lie ⟨.twistedA 3 Q, hv⟩, ⟨e⟩⟩ ?_ hA hlt
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p S]
      refine CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd ?_
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hm]
      exact CFSG.Quasithin.H13.NQCore.not_sq_dvd_of_squarefree (α := 6) (β := 4) (u := 5)
        (hn := by norm_num) hp hp5
        ((by norm_num : Nat.Prime 5).squarefree)
    · obtain ⟨hpQ, hfQ⟩ := CFSG.RankThree.PartOne.N143.primePower_eq_three hQ
      have hm : StatedClassicalModel S .PSU 4 3 1 := by
        simpa [hpQ, hfQ] using CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
      have hS : IsSimpleGroup S :=
        (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S 4 3 1 hm).2
      refine false_of_pRank_le_one hI hp hp2 hS
        (exists_noncomm_of_elemAbelian_cube hp hS hA hlt)
        ⟨.lie ⟨.twistedA 3 Q, hv⟩, ⟨e⟩⟩ ?_ hA hlt
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p S]
      refine CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd ?_
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three hm]
      exact CFSG.Quasithin.H13.NQCore.not_sq_dvd_of_squarefree (α := 7) (β := 6) (u := 35)
        (hn := by norm_num) hp hp5
        (by
          rw [show (35:ℕ) = 5 * 7 by norm_num, Nat.squarefree_mul (by norm_num)]
          exact ⟨(by norm_num : Nat.Prime 5).squarefree,
            (by norm_num : Nat.Prime 7).squarefree⟩)
  ·
    obtain rfl : d1 = .B 3 Q := hd
    obtain ⟨hpQ, hfQ⟩ := CFSG.RankThree.PartOne.N143.primePower_eq_three hQ
    have hm : StatedClassicalModel S .POmegaOdd 3 3 1 := by
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 Q hv
        (by omega : Q.p ≠ 2) (by norm_num : 3 ≤ 3) e
      simpa [hpQ, hfQ] using h
    have hS : IsSimpleGroup S :=
      (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd
        S 3 3 1 hm).2
    refine false_of_pRank_le_one hI hp hp2 hS
      (exists_noncomm_of_elemAbelian_cube hp hS hA hlt)
      ⟨.lie ⟨.B 3 Q, hv⟩, ⟨e⟩⟩ ?_ hA hlt
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p S]
    refine CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd ?_
    rw [show Nat.card S = 4585351680 by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
        (p := 3) (f := 1) (by norm_num) hm).2.2.2.1 rfl]
      decide]
    exact CFSG.Quasithin.H13.NQCore.not_sq_dvd_of_squarefree (α := 9) (β := 9) (u := 455)
      (hn := by norm_num) hp hp5
      (by
        rw [show (455:ℕ) = 5 * (7 * 13) by norm_num, Nat.squarefree_mul (by norm_num)]
        refine ⟨(by norm_num : Nat.Prime 5).squarefree, ?_⟩
        rw [show (7 * 13:ℕ) = 7 * 13 by norm_num, Nat.squarefree_mul (by norm_num)]
        exact ⟨(by norm_num : Nat.Prime 7).squarefree,
          (by norm_num : Nat.Prime 13).squarefree⟩)

end CFSG.LocalAnalysis.GLTheoremA.H248
