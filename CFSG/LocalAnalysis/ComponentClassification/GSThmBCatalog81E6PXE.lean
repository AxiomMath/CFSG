module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXG2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXD4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXL5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXU5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem cf81E6P211Exc_of
    (hG2 : P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel G .G2 0 p f)
    (hD4 : P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel G .trialityD4 0 p f)
    (hRee : P211For fun G _ => ∃ f : ℕ, Blueprint.LieModel G .twistedG2 0 3 f)
    (hL5 : P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
      Blueprint.LieModel G .PSL 5 p f)
    (hU5 : P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
      Blueprint.LieModel G .PSU 5 p f) :
    CF81E6P211Exc := by
  intro X _ _ hsimp hcent hX
  rcases hX with ⟨p, f, hp, hp2, hf, h | h⟩ | h | h | h
  · exact hG2 X hsimp hcent ⟨p, f, hp, hp2, hf, h⟩
  · exact hD4 X hsimp hcent ⟨p, f, hp, hp2, hf, h⟩
  · exact hRee X hsimp hcent h
  · exact hL5 X hsimp hcent h
  · exact hU5 X hsimp hcent h

theorem cf81E6P211Exc :
    CF81E6P211Exc :=
  cf81E6P211Exc_of P211X.p211For_G2 P211X.p211For_D4 P211X.p211For_ree P211X.p211For_L5
    P211X.p211For_U5

end CFSG.ComponentClassification.GSThmB
