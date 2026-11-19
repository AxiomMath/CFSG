module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

private theorem dvd_natCard_of_forall_dvd_ncard_orbit {H α : Type*} [Group H] [MulAction H α]
    [Finite α] {n : ℕ} (h : ∀ x : α, n ∣ (MulAction.orbit H x).ncard) : n ∣ Nat.card α := by
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient H α)
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' H α), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  induction ω using Quotient.inductionOn with
  | h x =>
    rw [Nat.card_coe_set_eq]
    change n ∣ (MulAction.orbitRel.Quotient.orbit (Quotient.mk'' x)).ncard
    rw [MulAction.orbitRel.Quotient.orbit_mk (G := H) x]
    exact h x

theorem exists_orbit_card_two {Q X : Type*} [Group Q] [Finite Q] [MulAction Q X] [Finite X]
    (hQ : IsPGroup 2 Q) (hX : Nat.card X % 4 = 2) (hmove : ∀ x : X, ∃ q : Q, q • x ≠ x) :
    ∃ x : X, Nat.card (MulAction.orbit Q x) = 2 := by
  classical
  by_contra h
  push Not at h
  have h4 : 4 ∣ Nat.card X := by
    refine dvd_natCard_of_forall_dvd_ncard_orbit (H := Q) (n := 4) fun x => ?_
    rw [← Nat.card_coe_set_eq]
    obtain ⟨n, hn⟩ := hQ.card_orbit x
    have hne1 : Nat.card (MulAction.orbit Q x) ≠ 1 := by
      intro h1
      obtain ⟨q, hq⟩ := hmove x
      have h1' : (MulAction.orbit Q x).ncard = 1 := by simpa using h1
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1'
      have hxa : x = a := by
        have : x ∈ ({a} : Set X) := ha ▸ MulAction.mem_orbit_self x
        simpa using this
      rw [← hxa] at ha
      have : q • x ∈ ({x} : Set X) := ha ▸ MulAction.mem_orbit x q
      exact hq (by simpa using this)
    have hne2 : Nat.card (MulAction.orbit Q x) ≠ 2 := h x
    rw [hn] at hne1 hne2 ⊢
    have hn2 : 2 ≤ n := by
      rcases n with _ | _ | n
      · exact absurd (pow_zero 2) hne1
      · exact absurd (pow_one 2) hne2
      · omega
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hn2
  have : Nat.card X % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  omega

end CFSG.EvenSporadicStandard.HNRecog.Harada
