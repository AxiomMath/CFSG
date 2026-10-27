module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem crossAtPrime_of_sylowTorus {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (h : p.Prime → 5 ≤ p → d.1.characteristic ≠ p → ∃ m, SylowTorus (CFSG.HardMathSupport.Timmesfeld.CrossChar.Cat d) p m) :
    CrossAtPrime d p :=
  crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ _ ⟨e⟩ P => by
    obtain ⟨m, hm⟩ := h hp hp5 hdp
    exact ⟨⟨fun a b => Subtype.ext
      (mul_comm_of_sylowTorus (hm.of_mulEquiv e.symm) P.isPGroup' a.2 b.2)⟩⟩

theorem dvd_sub_one_or_dvd_add_one_or_three_le {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    p ∣ q - 1 ∨ p ∣ q + 1 ∨ 3 ≤ orderOf ((q : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => hpq (h ▸ dvd_zero p))
  have h0 := orderOf_natCast_ne_zero hp hpq
  by_cases h1 : orderOf ((q : ℕ) : ZMod p) = 1
  · left
    rw [orderOf_eq_one_iff] at h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h1, Nat.cast_one, sub_self]
  by_cases h2 : orderOf ((q : ℕ) : ZMod p) = 2
  · right; left
    have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := h2 ▸ pow_orderOf_eq_one _
    have hne : ((q : ℕ) : ZMod p) ≠ 1 := fun h => h1 (by rw [h, orderOf_one])
    have hm : (((q : ℕ) : ZMod p) + 1) * (((q : ℕ) : ZMod p) - 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.1 hm with h | h
    · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
      exact h
    · exact absurd (sub_eq_zero.1 h) hne
  · right; right
    omega

theorem orderOf_seven_eq {q : ℕ} (hq : ¬ 7 ∣ q) (h3 : 3 ≤ orderOf ((q : ℕ) : ZMod 7)) :
    orderOf ((q : ℕ) : ZMod 7) = 3 ∨ orderOf ((q : ℕ) : ZMod 7) = 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hq0 : ((q : ℕ) : ZMod 7) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 7).1 h)
  have hd : orderOf ((q : ℕ) : ZMod 7) ∣ 6 := ZMod.orderOf_dvd_card_sub_one hq0
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases h : orderOf ((q : ℕ) : ZMod 7) <;> simp_all <;> omega

section Catalog


theorem crossAtPrime_E8_seven {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    CrossAtPrime ⟨.E8 q, hv⟩ 7 := by
  intro hp hp5 hdp
  have hpq : (7 : ℕ) ≠ q.p := fun h => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E8]; exact h.symm)
  have hnd : ¬ 7 ∣ q.card := not_dvd_card_of_ne hp hpq
  rcases dvd_sub_one_or_dvd_add_one_or_three_le hp hnd with h1 | h2 | h3
  · exact crossAtPrime_E8_of_dvd hv le_rfl h1 hp hp5 hdp
  · exact crossAtPrime_E8_of_dvd_add_one hv le_rfl h2 hp hp5 hdp
  · refine crossAtPrime_of_sylowTorus (fun _ _ _ => ?_) hp hp5 hdp
    refine exists_sylowTorus_cat_E8 hv hp le_rfl hpq ?_ (Or.inr h3)
    rcases orderOf_seven_eq hnd h3 with h | h <;> rw [h] <;> decide

theorem crossAtPrime_E7_seven_of_three_le {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (h3 : 3 ≤ orderOf ((q.card : ℕ) : ZMod 7)) :
    CrossAtPrime ⟨.E7 q, hv⟩ 7 := by
  refine crossAtPrime_of_sylowTorus fun hp _ hdp => ?_
  have hpq : (7 : ℕ) ≠ q.p := fun h => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E7]; exact h.symm)
  have hnd : ¬ 7 ∣ q.card := not_dvd_card_of_ne hp hpq
  refine exists_sylowTorus_cat_E7 hv hp le_rfl hpq ?_ (Or.inr h3)
  rcases orderOf_seven_eq hnd h3 with h | h <;> rw [h] <;> decide

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
