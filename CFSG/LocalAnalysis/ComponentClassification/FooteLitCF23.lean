module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23J1
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23J2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23J3
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23M12
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23HS
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23He
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23ON
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Suz
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L34
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L216
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Ree
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L4
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Alt

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup


theorem cf23InnerFusion_of_families
    (hL3 : CF23InnerFusionFor fun Y _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .PSL 3 p f)
    (hU3 : CF23InnerFusionFor fun Y _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .PSU 3 p f)
    (hU4 : CF23InnerFusionFor fun Y _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .PSU 4 p f)
    (hSp4 : CF23InnerFusionFor fun Y _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .PSp 2 p f)
    (hO8 : CF23InnerFusionFor fun Y _ =>
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .POmegaMinus 4 p f)
    (hU34 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSU 3 2 2)
    (hSp44 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSp 2 2 2)
    (hL52 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 5 2 1)
    (hU52 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSU 5 2 1)
    (hL316 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 3 2 4)
    (hON : SolMax.ONOuterComponentsInput) (hSuz : SolMax.SuzOuterComponentsInput) :
    CF23InnerFusion := by
  apply cf23InnerFusion_of
  intro G _ _ N hN hC hY
  rcases hY with h | ⟨p, f, hp, hp2, hf, h | h | h | h | h | h | h⟩ | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h
  · exact psl2 G N hN hC h
  · have h9 : 5 ≤ p ^ (2 * f) := by
      have h3 : 3 ≤ p := by
        have := hp.two_le
        omega
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
        _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
    exact psl2 G N hN hC ⟨p, 2 * f, hp, hp2, by omega, h9, h⟩
  · exact hL3 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact hU3 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact psl4 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact hU4 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact hSp4 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact hO8 G N hN hC ⟨p, f, hp, hp2, hf, h⟩
  · exact ree G N hN hC h
  · exact l216 G N hN hC h
  · exact l34 G N hN hC h
  · exact hU34 G N hN hC h
  · exact hSp44 G N hN hC h
  · exact hL52 G N hN hC h
  · exact hU52 G N hN hC h
  · exact hL316 G N hN hC h
  · exact alt G N hN hC h
  · exact j1 G N hN hC h
  · exact j2 G N hN hC h
  · exact j3 G N hN hC h
  · exact m12 G N hN hC h
  · exact hs G N hN hC h
  · exact he G N hN hC h
  · exact on_of hON G N hN hC h
  · exact suz_of hSuz G N hN hC h

end CFSG.ComponentClassification.GSThmB.CF23I
