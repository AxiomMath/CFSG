module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem arith107 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  cases htag : lab.tag with
  | A => exact fam_A hlab htag hp hp2 hA hg
  | twA => exact fam_twA hlab htag hp hp2 hA hg
  | B => exact fam_B hlab htag hp hp2 hA hg
  | C => exact fam_C hlab htag hp hp2 hA hg
  | D => exact fam_D hlab htag hp hp2 hA hg
  | twD => exact fam_twD hlab htag hp hp2 hA hg
  | E6 => exact fam_E hlab (Or.inl htag) hp hp2 hA hg
  | E7 => exact fam_E hlab (Or.inr (Or.inl htag)) hp hp2 hA hg
  | E8 => exact fam_E hlab (Or.inr (Or.inr htag)) hp hp2 hA hg
  | F4 => exact fam_F4 hlab htag hp hp2 hA hg
  | twE6 => exact fam_twE6 hlab htag hp hp2 hA hg
  | triD4 => exact fam_triD4 hlab htag hp hp2 hA hg
  | G2 => exact fam_G2 hlab htag hp hp2 hA hg
  | twB2 => exact fam_twB2 hlab htag hp hp2 hA hg
  | twF4 => exact fam_twF4 hlab htag hp hp2 hA hg
  | B2der => exact fam_der hlab (Or.inl htag) hp hp2 hA
  | G2der => exact fam_der hlab (Or.inr (Or.inl htag)) hp hp2 hA
  | twF4der => exact fam_der hlab (Or.inr (Or.inr htag)) hp hp2 hA

end CFSG.LocalAnalysis.GLTheoremA

end
