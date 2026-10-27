module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Class
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.TwoDHigh
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

section TwoD


theorem ssexc_not_L34_twoD {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup τ L 3)
    (h2 : (2 : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨r, e, hr, hchar, hr5, he, hqe⟩ := ssexc_char_ge_five S h2
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ssTw_finite_rationalComponent S i
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · have hτ5 : 5 ≤ τ.rank := h5.trans (compRank_le_rank _)
    obtain ⟨V, hV, h8⟩ := ssexc_twoD_high_pSubgroup S (simplyLaced_of_five_le_rank hτ5) hT i hk
      h5 hr hr5
    exact not_isLThreeFour_of_pGroup hq.1 hr hr5 hV h8
  · have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, h4']
    obtain ⟨V, hV, h8⟩ := ssTw_pgroup_d4class S Nat.prime_three S.natCast_ne_zero hT hTp h1 i h4'
      hc hnin hr hr5
    exact not_isLThreeFour_of_pGroup hq.1 hr hr5 hV h8

theorem ssExcTwoD_holds (τ : Tag) : SsExcTwoD τ := by
  intro L _ _ S h2 a hT hTp h1 i hk hq
  exact ssexc_not_L34_twoD S h2 hT hTp h1 i hk hq

end TwoD

end CFSG.HardMathSupport.Dickson.Sec6
