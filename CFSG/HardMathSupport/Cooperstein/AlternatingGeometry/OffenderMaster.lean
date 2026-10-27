module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderFix
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderArith
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem card_eq_sum_orbits (E : Subgroup (Perm Ω)) :
    Nat.card Ω = ∑ ω : Orb E, Nat.card (orbit E ω.out) := by
  classical
  have := Nat.card_congr (MulAction.selfEquivSigmaOrbits E Ω)
  rw [this, Nat.card_sigma]

theorem card_Orb_pos [Nonempty Ω] : 0 < Nat.card (Orb E) := by
  have : Nonempty (Orb E) := ⟨Quotient.mk'' (Classical.arbitrary Ω)⟩
  exact Nat.card_pos

theorem chain (hoff : offIdx E ≤ Nat.card E) (i0 : Ω) :
    2 ^ Nat.card Ω ≤
      2 * (Nat.card E * (Nat.card (FixEven E) * Nat.card (twistFix E i0).range)) := by
  have h1 := pow_le_two_mul_card_evenVec (Ω := Ω)
  have h2 := offIdx_mul_card (E := E)
  have h3 := card_FixUp_eq (E := E) (i0 := i0)
  have h4 := card_ker_twistFix_le (E := E) (i0 := i0)
  calc 2 ^ Nat.card Ω ≤ 2 * Nat.card (evenVec Ω) := h1
    _ = 2 * (offIdx E * Nat.card (FixUp E)) := by rw [h2]
    _ ≤ 2 * (Nat.card E * Nat.card (FixUp E)) := by
        apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_right _ hoff
    _ = 2 * (Nat.card E * (Nat.card (twistFix E i0).ker * Nat.card (twistFix E i0).range)) := by
        rw [h3]
    _ ≤ 2 * (Nat.card E * (Nat.card (FixEven E) * Nat.card (twistFix E i0).range)) := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right _ h4

theorem card_E_le (hE : IsExp2 E) :
    Nat.card E ≤ ∏ ω : Orb E, Nat.card (orbit E ω.out) := by
  have := card_mul_index_pow_le hE (⊤ : Subgroup E) (fun p => le_top)
  simpa [Subgroup.card_top, Subgroup.index_top] using this

theorem pow_two_le_iff {a b : ℕ} : 2 ^ a ≤ 2 ^ b ↔ a ≤ b := Nat.pow_le_pow_iff_right (by norm_num)

theorem numerics [Nonempty Ω] (hE : IsExp2 E) (hoff : offIdx E ≤ Nat.card E)
    (hn : Nat.card Ω = 7 ∨ 9 ≤ Nat.card Ω) :
    ∃ m : Orb E → ℕ, (∀ ω, Nat.card (orbit E ω.out) = 2 ^ m ω) ∧
      Nat.card E ≤ 2 ^ ∑ ω, m ω ∧
      Nat.card Ω = ∑ ω, gx (m ω) + ∑ ω, m ω + Nat.card (Orb E) ∧
      (∀ ω, m ω ≤ 2) ∧ (∀ ω ω', m ω = 2 → m ω' = 2 → ω = ω') ∧
      ((∃ p, ∀ g ∈ E, g p = p) → (∀ ω, m ω ≤ 1) ∧
          2 ^ Nat.card Ω ≤ 2 ^ Nat.card (Orb E) * Nat.card E) ∧
      ((¬ ∃ p, ∀ g ∈ E, g p = p) →
          2 ^ Nat.card Ω ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card E) := by
  classical
  let i0 : Ω := Classical.arbitrary Ω
  choose m hm using fun ω : Orb E => hE.card_orbit ω.out
  have hr : 0 < Nat.card (Orb E) := card_Orb_pos
  have hrF : Fintype.card (Orb E) = Nat.card (Orb E) := (Nat.card_eq_fintype_card).symm
  have hsum : Nat.card Ω = ∑ ω, 2 ^ m ω := by
    rw [card_eq_sum_orbits E]; exact Finset.sum_congr rfl fun ω _ => hm ω
  have hprod : ∏ ω : Orb E, Nat.card (orbit E ω.out) = 2 ^ ∑ ω, m ω := by
    rw [Finset.prod_congr rfl fun ω _ => hm ω, Finset.prod_pow_eq_pow_sum]
  have hE' : Nat.card E ≤ 2 ^ ∑ ω, m ω := by rw [← hprod]; exact card_E_le hE
  have hid : Nat.card Ω = ∑ ω, gx (m ω) + ∑ ω, m ω + Nat.card (Orb E) := by
    rw [hsum]
    have h1 : ∀ ω, 2 ^ m ω = gx (m ω) + m ω + 1 := fun ω => by have := gx_add (m ω); omega
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      hrF]
  have hfp : Nat.card (FixP E) ≤ 2 ^ Nat.card (Orb E) := card_FixP_le E
  have hch := chain hoff i0
  refine ⟨m, hm, hE', hid, ?_⟩
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · obtain ⟨p, hp⟩ := hf
    have ha1 : Nat.card (twistFix E i0).range = 1 := range_twistFix_trivial hp
    have hfe := card_FixEven_mul_two_le hp
    have hfe2 : Nat.card (FixEven E) * 2 ≤ 2 ^ Nat.card (Orb E) := le_trans hfe hfp
    have h2 : 2 ^ Nat.card Ω ≤ 2 ^ Nat.card (Orb E) * Nat.card E := by
      calc 2 ^ Nat.card Ω ≤ 2 * (Nat.card E * (Nat.card (FixEven E) * 1)) := by
            rw [ha1] at hch; exact hch
        _ = Nat.card E * (Nat.card (FixEven E) * 2) := by ring
        _ ≤ Nat.card E * 2 ^ Nat.card (Orb E) := Nat.mul_le_mul_left _ hfe2
        _ = 2 ^ Nat.card (Orb E) * Nat.card E := by ring
    have h3 : 2 ^ Nat.card Ω ≤ 2 ^ (Nat.card (Orb E) + ∑ ω, m ω) := by
      calc 2 ^ Nat.card Ω ≤ 2 ^ Nat.card (Orb E) * Nat.card E := h2
        _ ≤ 2 ^ Nat.card (Orb E) * 2 ^ ∑ ω, m ω := Nat.mul_le_mul_left _ hE'
        _ = 2 ^ (Nat.card (Orb E) + ∑ ω, m ω) := by rw [pow_add]
    have h4 := pow_two_le_iff.1 h3
    have hg0 : ∑ ω, gx (m ω) = 0 := by omega
    have hm1 := arith_fixed m hg0
    refine ⟨fun ω => by have := hm1 ω; omega, fun ω ω' h _ => ?_, fun _ => ⟨hm1, h2⟩,
      fun h => absurd ⟨p, hp⟩ h⟩
    have := hm1 ω; omega
  · have hnf : ¬ ∃ p, ∀ g ∈ E, g p = p := hf
    have hdvd : Nat.card (twistFix E i0).range ∣ 2 ^ Nat.card E := by
      have := AddSubgroup.card_addSubgroup_dvd_card (twistFix E i0).range
      rwa [Nat.card_fun, Nat.card_zmod] at this
    obtain ⟨u, -, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hfe : Nat.card (FixEven E) ≤ 2 ^ Nat.card (Orb E) := le_trans card_FixEven_le hfp
    by_cases hu0 : u = 0
    ·
      rw [hu0, pow_zero] at hu
      have h2 : 2 ^ Nat.card Ω ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card E := by
        calc 2 ^ Nat.card Ω ≤ 2 * (Nat.card E * (Nat.card (FixEven E) * 1)) := by
              rw [hu] at hch; exact hch
          _ ≤ 2 * (Nat.card E * 2 ^ Nat.card (Orb E)) := by
              apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
          _ = 2 * 2 ^ Nat.card (Orb E) * Nat.card E := by ring
      have h3 : 2 ^ Nat.card Ω ≤ 2 ^ (1 + Nat.card (Orb E) + ∑ ω, m ω) := by
        calc 2 ^ Nat.card Ω ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card E := h2
          _ ≤ 2 * 2 ^ Nat.card (Orb E) * 2 ^ ∑ ω, m ω := Nat.mul_le_mul_left _ hE'
          _ = 2 ^ (1 + Nat.card (Orb E) + ∑ ω, m ω) := by rw [pow_add, pow_add]; ring
      have h4 := pow_two_le_iff.1 h3
      have hg1 : ∑ ω, gx (m ω) ≤ 1 := by omega
      obtain ⟨hm2, hm3⟩ := arith_nofixed m hg1
      exact ⟨hm2, hm3, fun h => (hnf h).elim, fun _ => h2⟩
    · exfalso
      have hu1 : 1 ≤ u := Nat.pos_of_ne_zero hu0
      have hY := card_mul_index_pow_le hE (FixTriv E) (fun p => stabilizer_le_FixTriv p)
      have hte : (FixTriv E).index * Nat.card (FixTriv E) = Nat.card E :=
        Subgroup.index_mul_card (FixTriv E)
      have hat : Nat.card (twistFix E i0).range ≤ (FixTriv E).index := card_range_twistFix_le hE
      have hts : ∀ ω : Orb E, (FixTriv E).index ≤ 2 ^ m ω := fun ω => by
        rw [← hm ω, card_orbit_eq_index]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le (stabilizer_le_FixTriv _))
      have hum : ∀ ω, u ≤ m ω := fun ω => by
        have : 2 ^ u ≤ 2 ^ m ω := by rw [← hu]; exact le_trans hat (hts ω)
        exact pow_two_le_iff.1 this
      obtain ⟨r', hr'⟩ : ∃ r', Nat.card (Orb E) = r' + 1 := ⟨Nat.card (Orb E) - 1, by omega⟩
      have key1 : Nat.card E * (Nat.card (twistFix E i0).range) ^ r' ≤ 2 ^ ∑ ω, m ω := by
        calc Nat.card E * (Nat.card (twistFix E i0).range) ^ r'
            ≤ Nat.card E * (FixTriv E).index ^ r' :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hat r')
          _ = Nat.card (FixTriv E) * (FixTriv E).index ^ (r' + 1) := by rw [← hte]; ring
          _ ≤ ∏ ω : Orb E, Nat.card (orbit E ω.out) := by rw [← hr']; exact hY
          _ = 2 ^ ∑ ω, m ω := hprod
      have key2 : 2 ^ Nat.card Ω * (Nat.card (twistFix E i0).range) ^ r' ≤
          2 * 2 ^ Nat.card (Orb E) * Nat.card (twistFix E i0).range * 2 ^ ∑ ω, m ω := by
        calc 2 ^ Nat.card Ω * (Nat.card (twistFix E i0).range) ^ r'
            ≤ 2 * (Nat.card E * (Nat.card (FixEven E) * Nat.card (twistFix E i0).range)) *
                (Nat.card (twistFix E i0).range) ^ r' := Nat.mul_le_mul_right _ hch
          _ = 2 * Nat.card (FixEven E) * Nat.card (twistFix E i0).range *
                (Nat.card E * (Nat.card (twistFix E i0).range) ^ r') := by ring
          _ ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card (twistFix E i0).range * 2 ^ ∑ ω, m ω := by
              apply Nat.mul_le_mul _ key1
              apply Nat.mul_le_mul_right
              exact Nat.mul_le_mul_left 2 hfe
      rw [hu] at key2
      have key3 : 2 ^ (Nat.card Ω + u * r') ≤ 2 ^ (1 + Nat.card (Orb E) + u + ∑ ω, m ω) := by
        calc 2 ^ (Nat.card Ω + u * r') = 2 ^ Nat.card Ω * (2 ^ u) ^ r' := by
              rw [pow_add, pow_mul]
          _ ≤ 2 * 2 ^ Nat.card (Orb E) * 2 ^ u * 2 ^ ∑ ω, m ω := key2
          _ = 2 ^ (1 + Nat.card (Orb E) + u + ∑ ω, m ω) := by
              rw [pow_add, pow_add, pow_add]; ring
      have key4 := pow_two_le_iff.1 key3
      have hfin : ∑ ω, gx (m ω) + u * Fintype.card (Orb E) ≤ 1 + 2 * u := by
        rw [hrF]
        have h5 : u * Nat.card (Orb E) = u * r' + u := by rw [hr']; ring
        linarith
      have hmain := arith_pos m u hu1 hum (by rw [hrF]; exact hr) hfin
      rw [← hsum] at hmain
      rcases hn with hn | hn <;> omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
