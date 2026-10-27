module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Subgroup

section Lines

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem zpowers_eq_of_mem_zpowers_of_pow_eq_one {g h : X} (hg : g ^ p = 1) (hg1 : g ≠ 1)
    (hh : h ∈ zpowers g) (hh1 : h ≠ 1) : zpowers h = zpowers g := by
  have hog : orderOf g = p := orderOf_eq_prime hg hg1
  have hhp : h ^ p = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hoh : orderOf h = p := orderOf_eq_prime hhp hh1
  exact eq_of_le_of_card_ge (zpowers_le.2 hh)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hog, hoh])

end Lines

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
