module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporJ4Fi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporCoHe

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem srow_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) (hsHe : s ≠ .He) (hsHN : s ≠ .HN)
    (hsCo : s ≠ .Co1) : SRow s 3 := by
  cases s
  case B => exact absurd rfl hsB
  case M => exact absurd rfl hsM
  case He => exact absurd rfl hsHe
  case HN => exact absurd rfl hsHN
  case Co1 => exact absurd rfl hsCo
  case J1 =>
    exact srow_of_not_sq_dvd (s := .J1) hOut hbr hOrd (by decide) (by decide) Nat.prime_three
      (by norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd])
  case M11 => exact srow_M11_three hOut
  case M12 => exact srow_M12_three hOut
  case M22 => exact srow_M22_three hOut
  case M23 => exact srow_M23_three hOut hbr
  case M24 => exact srow_M24_three hOut hbr hb
  case J2 => exact srow_J2_three hOut hbr hb
  case J3 => exact CFSG.HardMathSupport.Dickson.I271.SporAltJ3.srow_J3_three hOut hbr hb
  case J4 => exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.srow_J4_three hOut hbr
  case HS => exact srow_HS_three hOut hbr
  case McL => exact srow_McL_three hOut hbr
  case Ru => exact srow_Ru_three hOut hbr hb
  case Suz => exact CFSG.HardMathSupport.Dickson.I271.SporAltSuz.srow_Suz_three hOut hbr hb
  case ONan => exact srow_ON_three hOut hbr hb
  case Co2 => exact CFSG.HardMathSupport.Dickson.I271.SporAltCo2.srow_Co2_three hOut hbr hb
  case Co3 => exact CFSG.HardMathSupport.Dickson.I271.SporAltCo3.srow_Co3_three hOut hbr hb
  case Fi22 => exact CFSG.HardMathSupport.Dickson.I271.SporAltFi22.srow_Fi22_three hOut hbr hb
  case Fi23 => exact CFSG.HardMathSupport.Dickson.I271.SporAltFi23.srow_Fi23_three hOut hbr hb
  case Fi24Prime => exact CFSG.HardMathSupport.Dickson.I271.TabFi24.srow_Fi24_three hOut hbr
  case Ly => exact CFSG.HardMathSupport.Dickson.I271.SporAltLy.srow_Ly_three hOut hbr hb
  case Th => exact CFSG.HardMathSupport.Dickson.I271.SporAltTh.srow_Th_three hOut hbr hb

theorem altRow_HN_Co1 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {m : ℕ}
    (hm : m = 7 ∨ m = 8) : AltRow m .HN ∧ AltRow m .Co1 := by
  have hm5 : 5 ≤ m := by omega
  refine ⟨altRow_of_grow hm5 (fun T _ hT => not_equiv_alt_of_card (by omega) (by
      rw [hT]; rcases hm with rfl | rfl <;> decide))
    (CFSG.HardMathSupport.Dickson.I271.SporAltHN3.grow_HN_three hOut hbr), ?_⟩
  refine altRow_of_grow hm5 (fun T _ hT => not_equiv_alt_of_card (by omega) (by
      rcases hT with h | h | h <;> rw [h] <;> rcases hm with rfl | rfl <;> decide))
    (CFSG.HardMathSupport.Dickson.I271.TabCo1.grow_Co1_three hOut hbr)

theorem i1415SevenSporS_of_residual
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : AltRow 7 .B ∧ AltRow 7 .M ∧ AltRow 7 .He) : I1415SevenSporS := by
  refine (sporAltNoComp_iff 7).2 fun s => ?_
  by_cases hsB : s = .B
  · exact hsB ▸ hres.1
  by_cases hsM : s = .M
  · exact hsM ▸ hres.2.1
  by_cases hsHe : s = .He
  · exact hsHe ▸ hres.2.2
  by_cases hsHN : s = .HN
  · exact hsHN ▸ (altRow_HN_Co1 hOut hbr (Or.inl rfl)).1
  by_cases hsCo : s = .Co1
  · exact hsCo ▸ (altRow_HN_Co1 hOut hbr (Or.inl rfl)).2
  exact altRow_of_srow (by norm_num) (srow_three hOut hbr hOrd hb hsB hsM hsHe hsHN hsCo)

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
