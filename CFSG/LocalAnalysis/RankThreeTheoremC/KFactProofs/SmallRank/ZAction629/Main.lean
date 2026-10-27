module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Shapes
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
open scoped commutatorElement

theorem kFactZAction629_holds : KFactZAction629 := by
  intro K _ _ p f hp hf hp2 hf2 _ hp35 S F z hS hF hFne hzp hzne hzS hSzF hR3 hR5 hb _ hrk3
    hrk2 hnQ
  have hFD : FData f F :=
    ⟨hf, hf2, fun a ha b hb' => congrArg Subtype.val
      (hF.1.is_comm.comm (⟨a, ha⟩ : F) ⟨b, hb'⟩), fun a ha => hF.2 a ha, hFne⟩
  rcases hp35 with rfl | rfl
  · obtain ⟨e⟩ := hR3 rfl
    obtain ⟨i, j, t, hshape, hi, hj, hi2, hj2, hji⟩ := shape3 e
    have hsetup : Setup 3 2 S z t := ⟨hp, hp2, hS, hzp, hzne, hzS, hshape⟩
    have hnc : ¬ IsCyclic ↥(CC S z) := fun hc =>
      hnQ ⟨rfl, hsetup.rankThreeIsQ8CentralCyclic_of_cyclic e hc⟩
    have hcard := three_card hsetup hFD hSzF hb (hrk2 rfl) hnc hi hj hi2 hj2 hji
    refine ⟨⟨hcard, hsetup.center_inv hFD hSzF hb⟩,
      ⟨fun h => absurd h (by norm_num), fun _ => three_shape hsetup e hFD hSzF hb hnc, ?_⟩, ?_⟩
    · rw [hsetup.center_eq, hsetup.omega_center_eq hFD hSzF hb]
    · exact hsetup.conclusion_C
  · obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hAB, hAsup, hcardAB⟩ := hR5 rfl
    obtain ⟨i, j, r, s, t, hshape, hiA, hjA, hrB, hsB, hi2, hj2, hji, hr2, hs2, hs1, hrs⟩ :=
      shape5 eA eB hAB hAsup hcardAB
    have hsetup : Setup 5 4 S z t := ⟨hp, hp2, hS, hzp, hzne, hzS, hshape⟩
    have hAR : A ≤ RR S z := le_sup_left.trans hAsup.le
    have hBR : B ≤ RR S z := le_sup_right.trans hAsup.le
    have hcard := five_card hsetup hFD hSzF hb hrk3 (hAR hiA) (hAR hjA) (hBR hrB) (hBR hsB) hi2
      hj2 hji hr2 hs2 hs1 hrs (hAB i hiA s hsB) (hAB j hjA s hsB)
    have hcyc := five_cyclic hsetup hFD hSzF hb hrk3 (hAR hiA) (hAR hjA) (hBR hrB) (hBR hsB) hi2
      hj2 hji hr2 hs2 hs1 hrs (hAB i hiA s hsB) (hAB j hjA s hsB)
    refine ⟨⟨hcard, hsetup.center_inv hFD hSzF hb⟩,
      ⟨fun _ => five_shape hsetup eA eB hAB hAsup hcardAB hcyc, fun h => absurd h (by norm_num),
        ?_⟩, ?_⟩
    · rw [hsetup.center_eq, hsetup.omega_center_eq hFD hSzF hb]
    · exact hsetup.conclusion_C

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
