module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def LinUniBoundOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N : ℕ),
    Setup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i) →
    (¬ ∃ n : ℕ, p = 3 ∧ N = 6 ∧ Odd n ∧ 3 ∣ 2 ^ n + 1 ∧
      catalogIs (PSimple p L) (S10.isU6n n)) →
    Nat.card A ≤ p ^ (1 + N / p)

theorem card_le_u6_of_marking (hm : U6Marking) (ht : U6Type9) (hs : U6SizeModel)
    {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {n : ℕ}
    (hsetup : Setup 3 L J A d b)
    (hcat : catalogIs (PSimple 3 L) (S10.isU6n n)) (hn : Odd n) (h3 : 3 ∣ 2 ^ n + 1) :
    Nat.card A ≤ 3 ^ (1 + 6 / 3) := by
  simpa using card_le_three_cube_of_u6 hm ht hs hsetup hcat hn h3

theorem linUniBound_of_u6 (hm : U6Marking) (ht : U6Type9) (hs : U6SizeModel)
    (hother : LinUniBoundOther) : LinUniBound := by
  intro G _ _ p L J A d b N hsetup hcat
  by_cases hyes : ∃ n : ℕ, p = 3 ∧ N = 6 ∧ Odd n ∧ 3 ∣ 2 ^ n + 1 ∧
      catalogIs (PSimple p L) (S10.isU6n n)
  · obtain ⟨n, rfl, rfl, hn, h3, hcat6⟩ := hyes
    exact card_le_u6_of_marking hm ht hs hsetup hcat6 hn h3
  · exact hother G p L J A d b N hsetup hcat hyes

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
