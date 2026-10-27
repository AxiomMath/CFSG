module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem stmt6_2_20_of_inputs_F4 (h523 : Stmt5_2_3_F4) (h523S : Stmt5_2_3S_F4) (h6219 : Stmt6_2_19_F4) :
    Stmt6_2_20_F4 := by
  intro G _ _ T M L V m hsimp hnab hqtke hT hM hTM hLmax hLf hLM hMN hm hlie hV hred hVL
  by_cases hex : ∃ H : Subgroup G, IsHStar T M H ∧ 1 < E1.nParam H
  · by_cases hall : ∀ H : Subgroup G, IsHStar T M H → 1 < E1.nParam H →
        m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧ CentralizerComponentClause T H
    · obtain ⟨H₀, hH₀, hn₀⟩ := hex
      obtain ⟨hm2, hA5, -⟩ := hall H₀ hH₀ hn₀
      exact Or.inl ⟨hm2, hA5, fun H hH hn => (hall H hH hn).2.2⟩
    · push Not at hall
      obtain ⟨H, hH, hn, hnot⟩ := hall
      rcases h523 G T M L H V m hsimp hnab hqtke hT hM hTM hLmax hLf hLM hMN hm hlie hH hn hV
          hred hVL with h1 | h2 | h3
      · exact absurd h1.2.2 (hnot h1.1 h1.2.1)
      · exact Or.inr (Or.inr (Or.inr h2))
      · exact Or.inr (Or.inl h3)
  · push Not at hex
    by_cases hA : m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆
    · exact Or.inl ⟨hA.1, hA.2, fun H hH hn => absurd hn (not_lt.mpr (hex H hH))⟩
    · by_cases hLie : ∃ H : Subgroup G, IsHStar T M H ∧ ∃ K ∈ cComp H, E2.HasE22LieQuot K
      · obtain ⟨H, hH, hK⟩ := hLie
        rcases h523S G T M L H V m hsimp hnab hqtke hT hM hTM hLmax hLf hLM hMN hm hlie hH hK
            hV hred hVL with h1 | h2 | h3
        · exact absurd ⟨h1.1, h1.2.1⟩ hA
        · exact Or.inr (Or.inr (Or.inr h2))
        · exact Or.inr (Or.inl h3)
      · push Not at hLie
        have hyp : Hyp611 G T M L V m :=
          { simple := hsimp
            nonabelian := hnab
            qtke := hqtke
            sylow := hT
            maxTwoLocal := hM
            T_le := hTM
            maximal := hLmax
            faithful := hLf
            L_le := hLM
            normal := hMN
            two_le := hm
            lie := hlie
            module := ⟨hV, hred, hVL⟩
            not_a5 := hA
            nParam_eq_one := fun H hH =>
              le_antisymm (hex H hH) (one_le_nParam_of_isHStar hH)
            noLie := hLie }
        exact Or.inr (Or.inr (Or.inl (h6219 G T M L V m hyp)))

end CFSG.Quasithin.H13
