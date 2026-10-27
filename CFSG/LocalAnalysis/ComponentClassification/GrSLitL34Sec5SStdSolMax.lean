module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSol
public import CFSG.LocalAnalysis.ComponentClassification.GSTopExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFieldMirrorReach

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.EvenSporadicStandard.Induction (Sol78Thm46 Sol78Remark11 Sol78Thm11SuzONan)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_field_mirror_solomon_top [IsSimpleGroup G] (hS : SchreierFor Blueprint.Catalog)
    (hna : ∃ x y : G, x * y ≠ y * x) (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ x y : GeneralizedFitting.subgroup G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) (hC5 : L3TwoPowProperFixedCatalog)
    {b : G} {M : Subgroup G} {n : ℕ} (hb : orderOf b = 2)
    (hM : FooteLit.IsTwoComponentIn M (centralizer ({b} : Set G))) (hn : 4 ≤ n) (hev : Even n)
    (hL : Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 3 2 n) :
    ∃ J : Subgroup G, FooteLit.GSMirrorReach M J ∧ FooteLit.GSMirrorMaximal J ∧
      GSWeakMaximalComponent J ∧ FooteLit.IsSolomonMaximal J ∧ ∃ m : ℕ, 4 ≤ m ∧ Even m ∧
        Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 m := by
  obtain ⟨J, hMJ, hJmm, hJsol⟩ :=
    Foote5.SolMax.exists_isSolomonMaximal_reach hS hna hsF hnF hK hb hM
  obtain ⟨m, hm, hmev, hJL⟩ := lieModel_of_gsMirrorReach hS hna hK hC5 hn hev hL hMJ
  obtain ⟨c, hc, hJc⟩ := Foote5.SolMax.isTwoComponentAt_of_gsMirrorReach ⟨b, hb, hM⟩ hMJ
  exact ⟨J, hMJ, hJmm, hJmm.gsWeakMaximalComponent ⟨c, hc, hJc.1, hJc.2⟩, hJsol, m, hm, hmev, hJL⟩

theorem exists_mirror_solomon_suzONanField
    (hS : SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hC5 : L3TwoPowProperFixedCatalog)
    (hG : L34BaseSetting G) {a b : G} {M T : Subgroup G} (hb : orderOf b = 2)
    (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (htype : IsL34Type (T ⧸ Open.fusionZStar T))
    (hM : Blueprint.NativeSporadic.IsSporadic
          ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .Suz ∨
        Blueprint.NativeSporadic.IsSporadic
          ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .ONan ∨
        Blueprint.LieModel ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .PSL 3 2 4) :
    ∃ J : Subgroup G, FooteLit.GSMirrorMaximal J ∧ GSWeakMaximalComponent J ∧
      FooteLit.IsSolomonMaximal J ∧ SuzONanFieldType (J ⧸ Open.fusionZStar J) ∧
        3 ≤ pRank 2 ↥J := by
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, -⟩ := GrS5.fstar_facts hG
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  have hTr := (GrS5.three_le_pRank_of_l34 htype).trans
    (pRank_two_le_of_le (hTM.trans inf_le_left))
  rcases hM with hMS | hMO | hL
  · obtain ⟨f⟩ : Nonempty ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M) ≃*
        Blueprint.NativeSporadic.Carrier .Suz) := hMS
    have hs : Blueprint.NativeSporadic.IsSporadic (M ⧸ Open.fusionZStar M) .Suz :=
      ⟨eS.symm.trans f⟩
    exact ⟨M, Foote5.SolMax.gsMirrorMaximal_of_suzONan hS hC4 hna hK (Or.inl hs),
      gsWeakMaximalComponent_of_suzONan hS hC4 hG hb hMb hMp (Or.inl hs),
      Foote5.SolMax.isSolomonMaximal_of_suzONan hS hC4 hna hsF hnF hK hb ⟨hMb, hMp⟩ (Or.inl hs),
      Or.inl hs, hTr⟩
  · obtain ⟨f⟩ : Nonempty ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M) ≃*
        Blueprint.NativeSporadic.Carrier .ONan) := hMO
    have ho : Blueprint.NativeSporadic.IsSporadic (M ⧸ Open.fusionZStar M) .ONan :=
      ⟨eS.symm.trans f⟩
    exact ⟨M, Foote5.SolMax.gsMirrorMaximal_of_suzONan hS hC4 hna hK (Or.inr ho),
      gsWeakMaximalComponent_of_suzONan hS hC4 hG hb hMb hMp (Or.inr ho),
      Foote5.SolMax.isSolomonMaximal_of_suzONan hS hC4 hna hsF hnF hK hb ⟨hMb, hMp⟩ (Or.inr ho),
      Or.inr (Or.inl ho), hTr⟩
  · obtain ⟨J, -, hJmm, hJw, hJs, m, hm, hmev, hJL⟩ :=
      exists_field_mirror_solomon_top hS hna hsF hnF hK hC5 hb ⟨hMb, hMp⟩ le_rfl (by decide)
        (LieType.CurtisTits.lieModel_of_mulEquiv eS hL)
    exact ⟨J, hJmm, hJw, hJs, Or.inr (Or.inr ⟨m, hm, hmev, hJL⟩),
      three_le_pRank_of_lieModel_fusionZStar (by omega) hJL⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
