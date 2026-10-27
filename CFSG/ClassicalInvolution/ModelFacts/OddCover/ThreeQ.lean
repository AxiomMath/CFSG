module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPrime
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SU3

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits

universe u

section SL

variable {K : Type} [Field K] [Finite K]

theorem statedSL_three_noCover_odd {p f : ℕ} [hp : Fact p.Prime] (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ Nat.card K) : NoCover.{u} Odd (StatedSL 3 K) := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hK
      omega
    · exact h
  have hpart : NoCover.{u} (fun n => ∃ k, n = p ^ k) (StatedSL 3 K) := by
    refine NoCover.of_mulEquiv (specialLinearGroupEquivStatedSL 3 K) ?_
    intro E _ _ _ π hπ hcen ⟨k, hk⟩
    exact sl3_ker_eq_bot_of_isPGroup hπ hcen hK hf h5 (IsPGroup.of_card hk)
  intro E _ _ _ π hπ hC hodd
  have hnd := not_dvd_card_ker hpart π hπ hC
  have hrq : ∀ r : ℕ, r.Prime → r ≠ p → ¬ r ∣ Nat.card K := fun r hr hrp h => by
    rw [hK] at h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp.out).1 (hr.dvd_of_dvd_pow h))
  refine ker_eq_bot_of_sylow_conditions π hπ hC hodd (p := p) (e := Nat.card K - 1)
    (fun Cp => sylow_eq_bot_of_not_dvd Cp hnd) ?_ ?_
  · intro r hr _ hrp hre
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r (StatedSL 3 K)))
    exact ⟨Q, isCyclic_of_isPGroup_of_le_GL_three (hrq r hr.out hrp) hre Q.isPGroup'⟩
  · intro r hr hr2 hrp hre
    obtain ⟨N, hNmap, hNinj, hNcard⟩ :=
      lifted_monomial_subgroup monomialData_statedSL π hπ hC hodd
    refine ⟨N, inf_ker_eq_bot_of_injective hNinj, ?_⟩
    have hN : Nat.card N = 6 * (Nat.card K - 1) ^ 2 := by
      rw [← card_map_eq_of_injective hNinj, hNmap, hNcard, Subgroup.card_top, card_units_eq]
    rw [card_statedSL_three_eq_mul (p := Nat.card K) rfl, hN,
      factorization_order_eq hr.out hr2 (by omega) (by omega) (by omega) (by positivity)
        (hrq r hr.out hrp) (not_dvd_add_one_of_dvd_sub_one hq1 hr.out hr2 hre)
        (factorization_sq_add_add_one hr.out hq1 hre)]

end SL


section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem statedSU_three_isCyclic_sylow (hK : Nat.card K = (p ^ f) ^ 2) {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hre : ¬ r ∣ p ^ f + 1)
    (P : Sylow r (StatedSU 3 (p ^ f) K)) : IsCyclic (P : Subgroup (StatedSU 3 (p ^ f) K)) := by
  have hrq : ¬ r ∣ p ^ f := fun h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp.out).1 (hr.out.dvd_of_dvd_pow h))
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.out.pos
  by_cases hrm : r ∣ p ^ f - 1
  ·
    let e : SU (unitaryInvolution K p f) 3 ≃* StatedSU 3 (p ^ f) K := equivStatedSU hK 3
    set T := levelTorus (unitaryInvolution K p f) (0 : Fin (3 / 2))
    have : IsCyclic T := isCyclic_levelTorus_three
    set Z : Subgroup (StatedSU 3 (p ^ f) K) := T.map e.toMonoidHom
    have : IsCyclic Z := isCyclic_of_surjective (e.toMonoidHom.subgroupMap T)
      (MonoidHom.subgroupMap_surjective _ _)
    have hZ : Nat.card Z = (p ^ f) ^ 2 - 1 := by
      rw [Subgroup.card_map_of_injective e.injective, card_levelTorus_three hK]
    have hm : ¬ r ∣ (p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1) := by
      refine hr.out.not_dvd_mul (fun h => hrq (hr.out.dvd_of_dvd_pow h)) ?_
      intro h
      have h3 : r ∣ (p ^ f) ^ 3 - 1 := by
        have : (p ^ f) ^ 3 - 1 = (p ^ f - 1) * ((p ^ f) ^ 2 + p ^ f + 1) := by
          zify [hq1, Nat.one_le_pow 3 (p ^ f) hq1]
          ring
        rw [this]
        exact Dvd.dvd.mul_right hrm _
      have h2 : r ∣ 2 := by
        have := Nat.dvd_sub h h3
        rwa [show (p ^ f) ^ 3 + 1 - ((p ^ f) ^ 3 - 1) = 2 by
          have := Nat.one_le_pow 3 (p ^ f) hq1
          omega] at this
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 h2)
    refine isCyclic_of_isPGroup_of_card_eq_mul (Z := Z) (m := (p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1)) ?_
      hm P.isPGroup'
    rw [hZ, card_statedSU_three hK]
    ring
  · refine isCyclic_of_isPGroup_of_le_GL_three ?_ ?_ P.isPGroup'
    · rw [hK]
      exact fun h => hrq (hr.out.dvd_of_dvd_pow h)
    · rw [hK]
      intro h
      have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
        zify [hq1, Nat.one_le_pow 2 (p ^ f) hq1]
        ring
      rw [this] at h
      rcases (Nat.Prime.dvd_mul hr.out).1 h with h' | h'
      · exact hrm h'
      · exact hre h'

theorem statedSU_three_noCover_odd (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (h5 : 5 ≤ p ^ f) : NoCover.{u} Odd (StatedSU 3 (p ^ f) K) := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.out.pos
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h5
      omega
    · exact h
  have hpart : NoCover.{u} (fun n => ∃ k, n = p ^ k) (StatedSU 3 (p ^ f) K) := by
    refine NoCover.of_mulEquiv (equivStatedSU hK 3) ?_
    intro E _ _ _ π hπ hcen ⟨k, hk⟩
    exact su3_ker_eq_bot_of_isPGroup hK hp2 hf h5 hπ hcen (IsPGroup.of_card hk)
  intro E _ _ _ π hπ hC hodd
  have hnd := not_dvd_card_ker hpart π hπ hC
  have hrq : ∀ r : ℕ, r.Prime → r ≠ p → ¬ r ∣ p ^ f := fun r hr hrp h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp.out).1 (hr.dvd_of_dvd_pow h))
  refine ker_eq_bot_of_sylow_conditions π hπ hC hodd (p := p) (e := p ^ f + 1)
    (fun Cp => sylow_eq_bot_of_not_dvd Cp hnd) ?_ ?_
  · intro r hr hr2 hrp hre
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r (StatedSU 3 (p ^ f) K)))
    exact ⟨Q, statedSU_three_isCyclic_sylow hK hr2 hrp hre Q⟩
  · intro r hr hr2 hrp hre
    obtain ⟨N, hNmap, hNinj, hNcard⟩ :=
      lifted_monomial_subgroup (monomialData_statedSU (K := K) (p := p) (f := f)) π hπ hC hodd
    refine ⟨N, inf_ker_eq_bot_of_injective hNinj, ?_⟩
    have hN : Nat.card N = 6 * (p ^ f + 1) ^ 2 := by
      rw [← card_map_eq_of_injective hNinj, hNmap, hNcard, card_normOne hK]
    have hre' : ¬ r ∣ p ^ f - 1 := fun h =>
      not_dvd_add_one_of_dvd_sub_one hq1 hr.out hr2 h hre
    have key : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) =
        (p ^ f) ^ 3 * ((p ^ f + 1) * (p ^ f - 1)) * ((p ^ f + 1) * ((p ^ f) ^ 2 - p ^ f + 1)) := by
      have hqq : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
      zify [hq1, Nat.one_le_pow 2 (p ^ f) hq1, hqq]
      ring
    rw [card_statedSU_three hK, key, hN,
      factorization_order_eq hr.out hr2 (by omega) (by omega) (by omega) (by
        have := Nat.le_self_pow (by norm_num : 2 ≠ 0) (p ^ f)
        omega) (hrq r hr.out hrp) hre' (factorization_sq_sub_add_one hr.out hre)]

end SU

end CFSG.ClassicalInvolution.ModelFacts.OddCover
