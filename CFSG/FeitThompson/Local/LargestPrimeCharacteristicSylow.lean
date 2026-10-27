module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.LowRankSmallestPrimeHallReduction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

universe u

variable {q : ℕ} {G : Type u} [Group G] [Finite G]

private theorem exists_characteristic_natCard_eq_pow_factorization_aux :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [Nontrivial G] [Group.IsSolvable G],
      Nat.card G ≤ n → Odd (Nat.card G) →
      (∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2) →
      ∀ q : ℕ, q.Prime → q ∣ Nat.card G → (∀ r : ℕ, r.Prime → r ∣ Nat.card G → r ≤ q) →
      ∃ Q : Subgroup G, Q.Characteristic ∧
        Nat.card ↥Q = q ^ (Nat.card G).factorization q := by
  intro n
  induction n with
  | zero =>
      intro G _ _ _ _ hle
      have := Nat.card_pos (α := G)
      omega
  | succ n ih =>
      intro G _ _ _ _ hle hodd hrank q hq hqG hmax
      have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
      have hone : Nat.card G ≠ 1 := by
        have := Finite.one_lt_card (α := G); omega
      set p := (Nat.card G).minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime hone
      have hpG : p ∣ Nat.card G := Nat.minFac_dvd _
      have hmin : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → p ≤ r := fun r hr hrG =>
        Nat.minFac_le_of_dvd hr.two_le hrG
      by_cases hpq : p = q
      ·
        obtain ⟨m, hm⟩ : ∃ m, Nat.card G = q ^ m :=
          ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne fun {d} hd hdvd =>
            le_antisymm (hmax d hd hdvd) (hpq ▸ hmin d hd hdvd)⟩
        have hfac : (Nat.card G).factorization q = m := by
          rw [hm, hq.factorization_pow]; simp
        exact ⟨⊤, inferInstance, by rw [Subgroup.card_top, hfac]; exact hm⟩
      ·
        set K := charHallPCompl p G with hKdef
        have hKchar : K.Characteristic := charHallPCompl_characteristic p G
        have hKnd : ¬ p ∣ Nat.card ↥K := not_dvd_natCard_charHallPCompl hp G
        obtain ⟨a, ha⟩ := exists_index_charHallPCompl_eq_pow hp hmin hodd hrank
        have hcard : p ^ a * Nat.card ↥K = Nat.card G := by
          rw [← ha]; exact K.index_mul_card
        have hKtop : K ≠ ⊤ := fun h => hKnd (by rw [h, Subgroup.card_top]; exact hpG)
        have hlt : Nat.card ↥K < Nat.card G := natCard_lt_natCard_of_ne_top hKtop
        have hqK : q ∣ Nat.card ↥K := by
          rcases (Nat.Prime.dvd_mul hq).1 (hcard ▸ hqG) with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm hpq
          · exact h
        have : Nontrivial ↥K :=
          Finite.one_lt_card_iff_nontrivial.1
            (lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd Nat.card_pos hqK))
        obtain ⟨Q, hQchar, hQcard⟩ :=
          ih ↥K (by omega) (odd_natCard_subgroup hodd K)
            (fun r hr => elementaryAbelianPRank_fittingRaw_charHallPCompl_le hr p G hrank)
            q hq hqK
            (fun r hr hrK => hmax r hr (hrK.trans K.card_subgroup_dvd_card))
        refine ⟨Q.map K.subtype, inferInstance, ?_⟩
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
        congr 1
        have hfac : (Nat.card G).factorization q
            = (p ^ a).factorization q + (Nat.card ↥K).factorization q := by
          rw [← hcard, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') Nat.card_pos.ne']
          simp
        rw [hfac, hp.factorization_pow]
        simp [hpq]

theorem exists_characteristic_natCard_eq_pow_factorization [Nontrivial G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2)
    (hq : q.Prime) (hqG : q ∣ Nat.card G)
    (hmax : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r ≤ q) :
    ∃ Q : Subgroup G, Q.Characteristic ∧
      Nat.card ↥Q = q ^ (Nat.card G).factorization q :=
  exists_characteristic_natCard_eq_pow_factorization_aux (Nat.card G) G le_rfl hodd hrank q hq
    hqG hmax

theorem exists_characteristic_sylow [Nontrivial G] [Group.IsSolvable G] [Fact q.Prime]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2)
    (hqG : q ∣ Nat.card G) (hmax : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r ≤ q) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Characteristic := by
  obtain ⟨Q, hQchar, hQcard⟩ :=
    exists_characteristic_natCard_eq_pow_factorization hodd hrank Fact.out hqG hmax
  exact ⟨Sylow.ofCard Q hQcard, by rwa [Sylow.coe_ofCard]⟩

theorem primeFactors_natCard_nonempty (G : Type*) [Finite G] [Nontrivial G] :
    (Nat.card G).primeFactors.Nonempty :=
  Nat.nonempty_primeFactors.2 Finite.one_lt_card

theorem max'_primeFactors_natCard_spec (G : Type*) [Finite G] [Nontrivial G] :
    ((Nat.card G).primeFactors.max' (primeFactors_natCard_nonempty G)).Prime ∧
      (Nat.card G).primeFactors.max' (primeFactors_natCard_nonempty G) ∣ Nat.card G ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card G →
        r ≤ (Nat.card G).primeFactors.max' (primeFactors_natCard_nonempty G) := by
  have hmem := Finset.max'_mem _ (primeFactors_natCard_nonempty G)
  exact ⟨Nat.prime_of_mem_primeFactors hmem, Nat.dvd_of_mem_primeFactors hmem,
    fun r hr hrG => Finset.le_max' _ _ (Nat.mem_primeFactors.2 ⟨hr, hrG, Nat.card_pos.ne'⟩)⟩

theorem exists_characteristic_sylow_max'_primeFactors [Nontrivial G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ p : ℕ, p.Prime → elementaryAbelianPRank p ↥(fittingRaw G) ≤ 2) :
    ∃ Q : Subgroup G, Q.Characteristic ∧
      Nat.card ↥Q = (Nat.card G).primeFactors.max' (primeFactors_natCard_nonempty G) ^
        (Nat.card G).factorization
          ((Nat.card G).primeFactors.max' (primeFactors_natCard_nonempty G)) :=
  have h := max'_primeFactors_natCard_spec G
  exists_characteristic_natCard_eq_pow_factorization hodd hrank h.1 h.2.1 h.2.2

end

end CFSG.FeitThompson
