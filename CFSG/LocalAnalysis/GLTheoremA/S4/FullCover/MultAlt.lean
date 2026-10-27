module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem listedMultiplierBoundAt_cyclic (p : ℕ) (q : ℕ) (hq : q.Prime) :
    ListedMultiplierBoundAt p (.cyclic q hq) := fun hi => by
  rcases hi with h | h <;> exact h.elim

theorem hatOddMultiplierBoundAt_cyclic (q : ℕ) (hq : q.Prime) :
    HatOddMultiplierBoundAt (.cyclic q hq) := fun hi => by
  rcases hi with h | h <;> exact h.elim

section


theorem listedMultiplierBoundAt_alternating (p n : ℕ) (hn : 5 ≤ n) :
    ListedMultiplierBoundAt p (.alternating n hn) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  have hdvd := card_center_dvd_hopfMultiplier_of_cover hQ π hπ hker
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  rcases hi with ((⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl | rfl⟩)
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2] at hdvd
    exact absurd (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd).1 (by norm_num)
  · rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)] at hdvd
    exact absurd (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd).1 (by norm_num)
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at hdvd
    exact absurd (pGroup_card_of_dvd (by norm_num) hZ inferInstance hdvd).1 (by norm_num)
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at hdvd
    exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd).2 (by norm_num),
      Or.inr ⟨rfl, rfl⟩⟩
  · rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)] at hdvd
    exact absurd (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd).1 (by norm_num)

theorem hatOddMultiplierBoundAt_alternating (n : ℕ) (hn : 5 ≤ n) :
    HatOddMultiplierBoundAt (.alternating n hn) := by
  intro hi Q _ _ hQ π hπ hker hodd
  rcases hi with h | ⟨-, rfl⟩
  · exact h.elim
  have hdvd := card_center_dvd_hopfMultiplier_of_cover hQ π hπ hker
  rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at hdvd
  have h2 : Nat.Coprime (Nat.card (Subgroup.center Q)) 2 := Odd.coprime_two_right hodd
  exact h2.dvd_of_dvd_mul_right (by simpa using hdvd : Nat.card (Subgroup.center Q) ∣ 3 * 2)

end

end CFSG.LocalAnalysis.GLTheoremA
