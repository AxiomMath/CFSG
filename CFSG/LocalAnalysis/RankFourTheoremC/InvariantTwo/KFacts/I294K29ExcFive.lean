module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcSeven
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE

theorem orderOf_five_eq {q : ℕ} (hq : ¬ 5 ∣ q) :
    orderOf ((q : ℕ) : ZMod 5) = 1 ∨ orderOf ((q : ℕ) : ZMod 5) = 2 ∨
      orderOf ((q : ℕ) : ZMod 5) = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq0 : ((q : ℕ) : ZMod 5) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 5).1 h)
  have hd : orderOf ((q : ℕ) : ZMod 5) ∣ 4 := ZMod.orderOf_dvd_card_sub_one hq0
  have h0 := orderOf_natCast_ne_zero (by norm_num : Nat.Prime 5) hq
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases h : orderOf ((q : ℕ) : ZMod 5) <;> simp_all

theorem dvd_sub_one_of_orderOf_eq_one {p q : ℕ} (hp : p.Prime) (hq1 : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = 1) : p ∣ q - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [orderOf_eq_one_iff] at h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h, Nat.cast_one, sub_self]

theorem dvd_add_one_of_orderOf_eq_two {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 2) : p ∣ q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := h ▸ pow_orderOf_eq_one _
  have hne : ((q : ℕ) : ZMod p) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
  have hm : (((q : ℕ) : ZMod p) + 1) * (((q : ℕ) : ZMod p) - 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 hm with h1 | h1
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
    exact h1
  · exact absurd (sub_eq_zero.1 h1) hne

section Catalog


theorem crossAtPrime_E6_five {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    CrossAtPrime ⟨.E6 q, hv⟩ 5 := by
  intro hp hp5 hdp
  have hpq : (5 : ℕ) ≠ q.p := fun h => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E6]; exact h.symm)
  have hnd : ¬ 5 ∣ q.card := not_dvd_card_of_ne hp hpq
  have hq1 : 1 ≤ q.card := Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero 5)
  rcases orderOf_five_eq hnd with h1 | h2 | h4
  · exact crossAtPrime_E6_five_of_dvd hv (dvd_sub_one_of_orderOf_eq_one hp hq1 h1) hp hp5 hdp
  all_goals
    refine crossAtPrime_of_sylowTorus (fun _ _ _ => ?_) hp hp5 hdp
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    have hpK : ¬ 5 ∣ Nat.card K := by rw [hK]; exact hnd
  · rw [← hK] at h2
    exact ⟨_, (sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp (by norm_num) hpK
      (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2] e6Two_charpoly e6Two_pow h2
      (by decide) (by decide) (by decide)).of_mulEquiv e.symm⟩
  · rw [← hK] at h4
    exact ⟨_, (sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp (by norm_num) hpK
      (IsWeylMatrix.of_word Tag.E6 e6FourWord) [1, 1, 4, 4] e6Four_charpoly e6Four_pow h4
      (by decide) (by decide) (by decide)).of_mulEquiv e.symm⟩

theorem crossAtPrime_E7_five {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    CrossAtPrime ⟨.E7 q, hv⟩ 5 := by
  intro hp hp5 hdp
  have hpq : (5 : ℕ) ≠ q.p := fun h => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E7]; exact h.symm)
  have hnd : ¬ 5 ∣ q.card := not_dvd_card_of_ne hp hpq
  have hq1 : 1 ≤ q.card := Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero 5)
  rcases orderOf_five_eq hnd with h1 | h2 | h4
  · exact crossAtPrime_E7_five_of_dvd hv (dvd_sub_one_of_orderOf_eq_one hp hq1 h1) hp hp5 hdp
  · exact crossAtPrime_E7_five_of_dvd_add_one hv (dvd_add_one_of_orderOf_eq_two hp h2) hp hp5
      hdp
  · refine crossAtPrime_of_sylowTorus (fun _ _ _ => ?_) hp hp5 hdp
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    have hpK : ¬ 5 ∣ Nat.card K := by rw [hK]; exact hnd
    rw [← hK] at h4
    exact ⟨_, (sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
      (by norm_num) hpK (IsWeylMatrix.of_word Tag.E7 e7FourWord) [1, 1, 1, 4, 4] e7Four_charpoly
      e7Four_pow h4 (by decide) (by decide) (by decide)).of_mulEquiv e.symm⟩

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
