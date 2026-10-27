module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace TwA5Big

section Certs


variable {n q : ℕ} {F : Type} [Field F] [Finite F]

theorem three_not_dvd_center (h : UnitaryFieldData 2 n F) (hn : 2 ≤ n) :
    ¬ 3 ∣ Nat.card (Subgroup.center (unitaryPSU h 6)) := by
  rw [center_unitaryPSU_six h hn, Subgroup.card_bot]
  norm_num

theorem twA5_six (h : UnitaryFieldData 2 n F) (hn : 4 ≤ n) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime) (hqdvd : q ∣ 2 ^ n + 1)
    (hq6 : ¬ q ∣ 6) (hq2 : q ≠ 2) :
    (Subgroup.center ↥(blockSU h suFiveIndex) = ⊥ ∧
        TrivialMultiplierT ↥(blockSU h suFiveIndex)) ∨
      (evenRank (unitaryPSU h 6) = 4 ∧ ∃ labJ : GLALabel,
        HasLabel ↥(blockSU h suFiveIndex) (fun l => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) := by
  have hn2 : 2 ≤ n := by omega
  rcases (blockSU_suFiveIndex_clauses h hn2).1 with ⟨h1, h2⟩ | h3
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨evenRank_unitaryPSU_six h hn hq hqdvd hq6 hq2,
      ⟨⟨.twA, 4, n⟩, hasLabel_blockSU_suFiveIndex h hn2, rfl, rfl, h3⟩⟩

theorem twA5_shape (h : UnitaryFieldData 2 n F) (hn : 4 ≤ n) (he : evenRank (unitaryPSU h 6) = 4)
    (lab : GLALabel) (hlab : HasLabel (unitaryPSU h 6) (fun l => l = lab)) :
    JShape lab (3 ∣ Nat.card (Subgroup.center (unitaryPSU h 6))) ⟨.twA, 4, n⟩ := by
  have hlab5 : lab = ⟨.twA, 5, n⟩ := by
    rcases label_eq_or_BC (le_of_eq he.symm) hlab (hasLabel_unitaryPSU_six h (by omega : 2 ≤ n)) with h | h
    · exact h
    · exfalso
      obtain ⟨-, h2, -⟩ := h
      exact h2.elim (fun hB => by cases hB) (fun hC => by cases hC)
  subst hlab5
  have hz3 : ¬ (3 ∣ Nat.card (Subgroup.center (unitaryPSU h 6))) :=
    three_not_dvd_center h (by omega : 2 ≤ n)
  exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, hz3, rfl, rfl⟩)))))⟩

theorem twA5_su_case (h : UnitaryFieldData 2 n F) (hn : 2 ≤ n) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    3 ∣ Nat.card (Subgroup.center (unitaryPSU h 6)) →
      (∃ lab : GLALabel, HasLabel (unitaryPSU h 6) (fun l => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      (blockSU h suFiveIndex) = ⊤ ∧ q = 3 ∧
        ∀ k : unitaryPSU h 6, k * unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) =
          unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) * k := by
  intro h3 _
  exact absurd h3 (three_not_dvd_center h hn)


end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
