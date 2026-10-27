module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Table
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Row
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Spor
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13CenterTwo

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

theorem catalog_cases_lieModel {X : Type} [Group X] (hX : Catalog X) :
    (∃ q : ℕ, q.Prime ∧ Nonempty (X ≃* Multiplicative (ZMod q))) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      (∃ (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f) ∨
      NativeSporadic.SporadicRep X := by
  rcases hX with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨t, n, p, f, hmodel⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨t, n, p, f, Or.inl ⟨?_, hmodel⟩⟩))
    have h2 := hmodel.2
    cases t <;> first | exact h2.elim | simp [classicalTags]
  · rcases h with ⟨t, p, f, ht, hmodel⟩ | ⟨t, p, f, ht, hmodel⟩ | ⟨p, f, hmodel⟩
    · exact Or.inr (Or.inr (Or.inl ⟨t, 0, p, f, Or.inr (Or.inl ⟨rfl, ht, hmodel⟩)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨t, 0, p, f, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hmodel⟩))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.twistedB2, 0, p, f,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hmodel⟩))⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem isCentralFourRow_of_twistedE6 {X : Type} [Group X] {n p f : ℕ}
    (hL : LieModel X .twistedE6 n p f) (h2 : p ^ f = 2) : IsCentralFourRow .twistedE6 n p f := by
  have hp : p.Prime := (GriessNative.admissible_of_lieModel hL).1
  obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
  obtain ⟨rfl, -⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))))

theorem isCentralFourRow_of_catalog (hrows : NativeRowsExceptTwistedE6Two)
    (hB : EvenSporadicStandard.CentralTwoBound) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hcat : Catalog (Q ⧸ center Q)) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q) (hvZ : v ∈ center Q) :
    ∃ (t : StatedLieTag) (n p f : ℕ), LieModel (Q ⧸ center Q) t n p f ∧
      IsCentralFourRow t n p f := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  rcases catalog_cases_lieModel hcat with ⟨q, -, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨t, n, p, f, hL⟩ | hS
  · obtain ⟨a, b, hab⟩ := hQ.2.2
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hab
  · exact absurd (eq_of_center_involution_of_alternating hQ hm e huZ hvZ hu2 hv2 hu1 hv1) huv
  · refine ⟨t, n, p, f, hL, ?_⟩
    by_contra hF
    have hne : ¬ (t = .twistedE6 ∧ p ^ f = 2) := by
      rintro ⟨rfl, h2⟩
      exact hF (isCentralFourRow_of_twistedE6 hL h2)
    obtain ⟨hb, hd, hac⟩ := table_odd_of_not_row (GriessNative.admissible_of_lieModel hL) hF
    exact huv (eq_of_center_involution_of_griessRow hQ (hrows _ t n p f hL hne) hb hd hac huZ hvZ
      hu2 hv2 hu1 hv1)
  · exact absurd (eq_of_center_involution_of_sporadic hB hQ hS huZ hvZ hu2 hv2 hu1 hv1) huv

@[expose] def CentralFourRowInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q →
    ∀ (t : StatedLieTag) (n p f : ℕ), LieModel (Q ⧸ center Q) t n p f →
      IsCentralFourRow t n p f →
    ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u ≠ v → u ∈ center Q → v ∈ center Q →
      (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2

theorem quasisimpleCentralFourInput_of_rows (hrows : NativeRowsExceptTwistedE6Two)
    (hB : EvenSporadicStandard.CentralTwoBound) (h : CentralFourRowInput) :
    QuasisimpleCentralFourInput := by
  intro Q _ _ hQ hcat u v hu hv huv huZ hvZ
  obtain ⟨t, n, p, f, hL, hrow⟩ := isCentralFourRow_of_catalog hrows hB hQ hcat hu hv huv huZ hvZ
  exact h Q hQ t n p f hL hrow u v hu hv huv huZ hvZ

end CFSG.ComponentClassification.Sol76T13.Hq4
