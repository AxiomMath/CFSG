module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthLane
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSuN

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Exc


theorem excTLKind_exc {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ExcTLKind .exc τ := by
  have _ := hτ
  intro L _ _ p₀ S a hT ha3 h1 i hk _ q _ hq
  classical
  have hL3 : (3 : L) ≠ 0 := by
    intro h3
    apply h1
    have ha1 : ∀ j, a j = 1 := by
      intro j
      have h' : ((a j : L)) ^ 3 = 1 := by
        have := congrArg Units.val (ha3 j)
        simpa using this
      have h0 : ((a j : L) - 1) ^ 3 = 0 := by
        linear_combination h' + (-(a j : L) ^ 2 + (a j : L)) * h3
      exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0))
    have : a = 1 := funext ha1
    rw [this, rootDiagUnit_one]
  have hTp : rootDiagUnit τ a ^ 3 = 1 := excOth_rootDiagUnit_pow_eq_one ha3
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨hnin, hA | ⟨hr4, hc24, -⟩⟩ := exc_kind hk
  · have hNo := ssOth_e6class S Nat.prime_three hL3 hT hTp h1 i hA.1 hA.2 hnin hr
    obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
    exact (hNo F).false e'
  · have hNo := ssOth_d4class S Nat.prime_three hL3 hT hTp h1 i hr4 hc24 hnin hr
    obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
    exact (hNo F).false e'

end Exc

end CFSG.HardMathSupport.Dickson.Sec6.I1431
