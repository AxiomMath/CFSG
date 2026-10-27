module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Id
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Sz8
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4TwE6
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

@[expose] def POmegaPlusCentralizerInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p ≠ 2 → Even n → LieModel S .POmegaPlus n p f →
    ∀ s : S, s * s = 1 → s ≠ 1 → 2 ^ 4 ∣ Nat.card (centralizer ({s} : Set S))

@[expose] def POmegaPlusInvolutionInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → ∀ (n p f : ℕ), p ≠ 2 → Even n →
    LieModel (Q ⧸ center Q) .POmegaPlus n p f → ∀ u v : Q, u ∈ center Q → v ∈ center Q →
      u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v → ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q

theorem centralFour_POmegaPlus
    (hC : POmegaPlusCentralizerInput)
    (hI : POmegaPlusInvolutionInput) {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {n p f : ℕ} (hp2 : p ≠ 2) (hn : Even n) (hL : LieModel (Q ⧸ center Q) .POmegaPlus n p f)
    {u v : Q} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q)
    (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  have hcl := GriessNative.classical_of_lieModel hL (by decide)
  have hadm := hcl.1
  have hp : p.Prime := hadm.1
  have hq : 3 ≤ p ^ f := by
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact le_trans h3 (Nat.le_self_pow (by have := hadm.2.1; omega) p)
  have hrow : GriessAll.GriessRow (Q ⧸ center Q) .POmegaPlus n p f :=
    GriessClassical.pomegaPlus_row hcl (Or.inl hq)
  have hodd := table_odd_pair_of_row (t := .POmegaPlus) (n := n) (p := p) (f := f)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hp2, hn⟩)))))
  refine ⟨hI Q hQ n p f hp2 hn hL u v huZ hvZ hu2 hv2 hu1 hv1 huv, fun x hx hxZ => ?_⟩
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  refine clause_two_of_griessRow hQ hrow hodd huZ hvZ hu2 hv2 hu1 hv1 huv hx2 ?_
  have h16 := hC (Q ⧸ center Q) n p f hp2 hn hL (x : Q ⧸ center Q)
    (by rw [← QuotientGroup.mk_mul, hx2]; rfl)
    (fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h))
  exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h16

theorem centralFourRowInput_of_POmegaPlus
    (hC : POmegaPlusCentralizerInput) (hI : POmegaPlusInvolutionInput) :
    CentralFourRowInput := by
  intro Q _ _ hQ t n p f hL hrow u v hu hv huv huZ hvZ
  rcases hrow with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hp2, hn⟩
  · exact centralFour_L34 hQ hL hu hv huv huZ hvZ
  · exact centralFour_U62 hQ hL hu hv huv huZ hvZ
  · exact centralFour_O82 hQ hL hu hv huv huZ hvZ
  · exact centralFour_Sz8 hQ hL hu hv huv huZ hvZ
  · exact centralFour_twistedE6 hQ hL hu hv huv huZ hvZ
  · exact centralFour_POmegaPlus hC hI hQ hp2 hn hL hu hv huv huZ hvZ

theorem quasisimpleCentralFourInput_of_POmegaPlus
    (hC : POmegaPlusCentralizerInput) (hI : POmegaPlusInvolutionInput) :
    QuasisimpleCentralFourInput :=
  quasisimpleCentralFourInput_of_rows nativeRowsExceptTwistedE6Two
    EvenSporadicStandard.centralTwoBound (centralFourRowInput_of_POmegaPlus hC hI)

end CFSG.ComponentClassification.Sol76T13.Hq4
