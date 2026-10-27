module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTorality
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality


theorem monomialToralAt_exc_of_ne_E8
    (h65 : MonomialToralAt Tag.E6 5) (h75 : MonomialToralAt Tag.E7 5)
    {τ : Tag} (hne : τ ≠ .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : MonomialToralAt τ p := by
  have hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 := by
    cases τ <;> simp_all
  have hG2 : Nat.card (WeylGroup Tag.G2) = 12 := CFSG.RankThree.PartOne.K133H.card_weylGroup_G2
  have hE6 : Nat.card (WeylGroup Tag.E6) = 51840 := CFSG.RankThree.E6.card_weylGroup_E6
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ 7 < p := by
    rcases Nat.lt_or_ge 7 p with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rcases hp' with rfl | rfl | rfl | h7
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · exact monomialToralAt_three_of_block a2BlockToral_G2
    · exact monomialToralAt_three_of_block a2BlockToral_F4
    · exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_E6_three
    · exact monomialToralAt_three_of_block a2BlockToral_E7
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · exact monomialToralAt_of_not_dvd hp (by rw [hG2]; norm_num)
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by norm_num))
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by norm_num))
    · exact h65
    · exact h75
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · exact monomialToralAt_of_not_dvd hp (by rw [hG2]; norm_num)
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by norm_num))
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by norm_num))
    · exact monomialToralAt_of_not_dvd hp (by rw [hE6]; norm_num)
    · exact monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E7 hγ)
        (chainBlockToral_E7_six_of_transitive a6ChainTransitive_E7)
  ·
    have hnd12 : ¬ p ∣ 12 := fun h => by
      have hle := Nat.le_of_dvd (by norm_num) h
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · exact monomialToralAt_of_not_dvd hp (by rw [hG2]; exact hnd12)
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by omega))
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by omega))
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inl rfl))
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inl rfl)))

theorem monomialToralAt_exc (h65 : MonomialToralAt Tag.E6 5) (h75 : MonomialToralAt Tag.E7 5)
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : MonomialToralAt τ p := by
  clear hτ
  by_cases hE8 : τ = .E8
  · subst τ
    have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ 7 < p := by
      rcases Nat.lt_or_ge 7 p with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    rcases hp' with rfl | rfl | rfl | h7
    · exact monomialToralAt_three_of_block a2BlockToral_E8
    · exact monomialToralAt_five_of_chainBlock (fun _ hγ => iform_self_E8 hγ)
        chainBlockToral_E8_four
    · exact monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E8 hγ)
        (chainBlockToral_E8_six_of_transitive a6ChainTransitive_E8)
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inr rfl)))
  · exact monomialToralAt_exc_of_ne_E8 h65 h75 hE8 hp hp2

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
