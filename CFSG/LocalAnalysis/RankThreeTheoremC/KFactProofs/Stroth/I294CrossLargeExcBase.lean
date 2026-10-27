module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossRank
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

namespace I294CrossLargeExc

@[expose] def AbelOrRankFour (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  (∀ S : Sylow p G, IsMulCommutative (S : Subgroup G)) ∨
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)

variable {p : ℕ} {G : Type} [Group G] [Finite G]

theorem AbelOrRankFour.of_sylow_comm (h : ∀ S : Sylow p G, IsMulCommutative (S : Subgroup G)) :
    AbelOrRankFour p G :=
  Or.inl h

theorem AbelOrRankFour.of_elemAbelian (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    {a : ℕ} (hE' : Nat.card E = p ^ a) (ha : 4 ≤ a) : AbelOrRankFour p G :=
  Or.inr (ha.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top hE hE'))

theorem AbelOrRankFour.of_mulEquiv {H : Type} [Group H] [Finite H] (hp : p.Prime) (e : H ≃* G)
    (h : AbelOrRankFour p G) : AbelOrRankFour p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases h with h | h
  · exact Or.inl (CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e h)
  · exact Or.inr (by rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e])

theorem AbelOrRankFour.rank_of_not_comm (h : AbelOrRankFour p G)
    (hS : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  rcases h with h | h
  · obtain ⟨S, hS⟩ := hS
    exact (hS (h S)).elim
  · exact h

theorem AbelOrRankFour.of_sylowTorus {m : ℕ}
    (h : CFSG.LieType.SeitzGeneration.SylowTorus G p m) : AbelOrRankFour p G := by
  refine Or.inl fun S => ?_
  rw [isMulCommutative_iff]
  intro a b
  exact Subtype.ext
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus h S.isPGroup' a.2 b.2)

theorem orderOf_natCast_dvd_pred {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) :
    orderOf ((n : ℕ) : ZMod p) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  exact ZMod.orderOf_dvd_card_sub_one hq0

theorem eq_five_of_lt_seven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p < 7) : p = 5 := by
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)

theorem eq_seven_of_lt_eleven {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h : p < 11) : p = 7 := by
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

theorem cases_dvd_four {e : ℕ} (hd : e ∣ 4) : e = 1 ∨ e = 2 ∨ e = 4 := by
  have h : e ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact absurd hd (by norm_num)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd hd (by norm_num)
  · exact Or.inr (Or.inr rfl)

theorem cases_dvd_six {e : ℕ} (hd : e ∣ 6) : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6 := by
  have h : e ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact absurd hd (by norm_num)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact Or.inr (Or.inr (Or.inr rfl))

end I294CrossLargeExc

theorem i294CrossLargePrimeOn_of_abelOrRankFour {φ : TauCeti.LieTypeIndex → Prop}
    (h : ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ d : TauCeti.ValidLieTypeIndex, φ d.1 →
      d.1.characteristic ≠ p →
      ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
        I294CrossLargeExc.AbelOrRankFour p L) :
    I294CrossLargePrimeOn φ := by
  intro p hp h5 L _ _ _ _ d hφ hd e _ hS
  exact (h p hp h5 d hφ hd L e).rank_of_not_comm hS

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
