module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHe3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder sporFactors_prime
  sporFactors_nodup exists_of_prime_pow_dvd_prod)

@[expose] def I1416SporResidual2 : Prop :=
  (∀ p, I1416SporRow .B p) ∧ (∀ p, I1416SporRow .M p) ∧
    I1416SporRow .Co1 3 ∧ I1416SporRow .Co1 5 ∧ I1416SporRow .Co1 7 ∧
    I1416SporRow .Fi24Prime 3 ∧ I1416SporRow .Fi24Prime 5 ∧ I1416SporRow .Fi24Prime 7 ∧
    I1416SporRow .J4 3 ∧ I1416SporRow .Fi23 5

@[expose] def I1416SporResidual : Prop :=
  I1416SporResidual2 ∧ I1416SporRow .HN 3

theorem sporOrd_eq_sporOrder (s : TauCeti.SporadicName) :
    CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s = sporOrder s := by
  cases s <;> rfl













theorem row_of_factors
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M)
    (h : ∀ x ∈ sporFactors s, x.1 ≠ 2 → 2 ≤ x.2 → I1416SporRow s x.1) (p : ℕ) :
    I1416SporRow s p := by
  intro S _ _ he hp hp2
  by_cases hd : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · rw [sporOrd_eq_sporOrder] at hd
    obtain ⟨x, hx, rfl, h2⟩ := exists_of_prime_pow_dvd_prod hp (by norm_num)
      (sporFactors_prime s) (sporFactors_nodup s) hd
    exact h x hx hp2 h2 S he hp hp2
  · exact row_of_not_sq_dvd hOut hbr hOrd hsB hsM hp hd S he hp hp2

theorem i1416TwoSporS_of_residual
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : I1416SporResidual) : I1416TwoSporS := by
  obtain ⟨⟨hB, hM, hCo13, hCo15, hCo17, hF3, hF5, hF7, hJ43, hFi235⟩, hHN3⟩ := hres
  refine i1416TwoSporS_iff.2 fun s p => ?_
  cases s
  case B => exact hB p
  case M => exact hM p
  all_goals refine row_of_factors hOut hbr hOrd (by decide) (by decide) (fun x hx h2 he => ?_) p
  all_goals simp only [sporFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h2 | (exfalso; omega) | skip
  case M11 => exact row_M11_three hOut
  case M12 => exact row_M12_three hOut
  case M22 => exact row_M22_three hOut
  case M23 => exact row_M23_three hOut hbr
  case M24 => exact row_M24_three hOut hbr hb
  case J2.inr.inl => exact row_J2_three hOut hbr hb
  case J2.inr.inr.inl => exact row_J2_five hOut hbr
  case J3.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416J3.row_J3_three hOut hbr
  case J4.inr.inl => exact hJ43
  case J4.inr.inr.inr.inr.inl => exact row_J4_eleven hbr hOut
  case HS.inr.inl => exact row_HS_three hOut hbr
  case HS.inr.inr.inl => exact row_HS_five hOut hbr
  case McL.inr.inl => exact row_McL_three hOut hbr
  case McL.inr.inr.inl => exact row_McL_five hOut hbr
  case He.inr.inl => exact row_He_three hOut hbr hb
  case He.inr.inr.inl => exact row_He_five hOut hbr
  case He.inr.inr.inr.inl => exact row_He_seven hOut hbr
  case Ru.inr.inl => exact row_Ru_three hOut hbr hb
  case Ru.inr.inr.inl => exact row_Ru_five hOut hbr
  case Suz.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Suz.row_Suz_three hOut hbr hb
  case Suz.inr.inr.inl => exact row_Suz_five hOut hbr hb
  case ONan.inr.inl => exact row_ON_three hOut hbr
  case ONan.inr.inr.inr.inl => exact row_ON_seven hOut
  case Co1.inr.inl => exact hCo13
  case Co1.inr.inr.inl => exact hCo15
  case Co1.inr.inr.inr.inl => exact hCo17
  case Co2.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Co2.row_Co2_three hOut hbr
  case Co2.inr.inr.inl => exact row_Co2_five hOut hbr
  case Co3.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Co3.row_Co3_three hOut hbr
  case Co3.inr.inr.inl => exact row_Co3_five hOut hbr
  case Fi22.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Fi22.row_Fi22_three hOut hbr hb
  case Fi22.inr.inr.inl => exact row_Fi22_five hOut hbr
  case Fi23.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Fi23.row_Fi23_three hOut hbr hb
  case Fi23.inr.inr.inl => exact hFi235
  case Fi24Prime.inr.inl => exact hF3
  case Fi24Prime.inr.inr.inl => exact hF5
  case Fi24Prime.inr.inr.inr.inl => exact hF7
  case HN.inr.inl => exact hHN3
  case HN.inr.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416HN.row_HN_five hOut hbr hb
  case Ly.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Ly.row_Ly_three hOut hbr hb
  case Ly.inr.inr.inl => exact row_Ly_five hOut hbr
  case Th.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1416Th.row_Th_three hOut hbr hb
  case Th.inr.inr.inl => exact row_Th_five hOut hbr
  case Th.inr.inr.inr.inl =>
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven.row_Th_seven hOut hbr

section HN3


theorem i1416TwoSporS_of_residual2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : I1416SporResidual2) : I1416TwoSporS :=
  i1416TwoSporS_of_residual hOut hbr hOrd hb
    ⟨hres, CFSG.HardMathSupport.Dickson.I271.I1416HN3.row_HN_three hOut hbr hb⟩

end HN3

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
