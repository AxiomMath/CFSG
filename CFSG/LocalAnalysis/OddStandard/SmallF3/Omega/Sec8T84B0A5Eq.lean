module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable

@[expose] def a5a : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def a5b : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 0 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem a5a_sq : a5a * a5a = 1 :=
  Subtype.ext (by change (Equiv.swap 1 2 * Equiv.swap 3 4) * (Equiv.swap 1 2 * Equiv.swap 3 4) = 1;
                  decide +kernel)

theorem a5b_cube : a5b ^ 3 = 1 :=
  Subtype.ext (by change (Equiv.swap 1 0 * Equiv.swap 1 3) ^ 3 = 1; decide +kernel)

theorem a5ab_pow : (a5a * a5b) ^ 5 = 1 :=
  Subtype.ext (by
    change ((Equiv.swap 1 2 * Equiv.swap 3 4) * (Equiv.swap 1 0 * Equiv.swap 1 3)) ^ 5 = 1
    decide +kernel)

theorem a5a_ne : a5a ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  exact absurd h' (by change Equiv.swap 1 2 * Equiv.swap 3 4 ≠ 1; decide +kernel)

theorem a5b_ne : a5b ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  exact absurd h' (by change Equiv.swap 1 0 * Equiv.swap 1 3 ≠ 1; decide +kernel)

theorem a5ab_ne : a5a * a5b ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  exact absurd h' (by
    change (Equiv.swap 1 2 * Equiv.swap 3 4) * (Equiv.swap 1 0 * Equiv.swap 1 3) ≠ 1
    decide +kernel)

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem closure_a5ab : Subgroup.closure ({a5a, a5b} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have hordA : orderOf a5a = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime a5a_sq a5a_ne
  have hordB : orderOf a5b = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime a5b_cube a5b_ne
  have hordAB : orderOf (a5a * a5b) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime a5ab_pow a5ab_ne
  set H := Subgroup.closure ({a5a, a5b} : Set (alternatingGroup (Fin 5))) with hH
  have hmemA : a5a ∈ H := Subgroup.subset_closure (by simp)
  have hmemB : a5b ∈ H := Subgroup.subset_closure (by simp)
  have h2 : 2 ∣ Nat.card H := by
    simpa [hordA] using Subgroup.orderOf_dvd_natCard H hmemA
  have h3 : 3 ∣ Nat.card H := by
    simpa [hordB] using Subgroup.orderOf_dvd_natCard H hmemB
  have h5 : 5 ∣ Nat.card H := by
    simpa [hordAB] using Subgroup.orderOf_dvd_natCard H (H.mul_mem hmemA hmemB)
  have hdvd : Nat.card H ∣ 60 := by
    have h := Subgroup.card_dvd_of_le (H := H) (K := ⊤) le_top
    rwa [Subgroup.card_top, card_alt5] at h
  have h30 : 30 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 5)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3) h5
  have hne30 : Nat.card H ≠ 30 := by
    intro hcard30
    have hindex : H.index = 2 := by
      have hmul := Subgroup.card_mul_index H
      rw [hcard30, card_alt5] at hmul
      omega
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hindex
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    rcases Subgroup.Normal.eq_bot_or_eq_top H with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hcard30
      omega
    · rw [htop, Subgroup.card_top, card_alt5] at hcard30
      omega
  have hcard60 : Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h30
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk
        exact absurd hk (Nat.card_pos (α := ↥H)).ne'
      · exact h0
    have hle : 30 * k ≤ 60 := Nat.le_of_dvd (by norm_num) (hk ▸ hdvd)
    have hk2 : k ≤ 2 := by omega
    interval_cases k
    · exact absurd hk hne30
    · simpa using hk
  exact Subgroup.eq_top_of_card_eq H (by rw [hcard60, card_alt5])

@[expose] noncomputable def a5RelsEquivAlt5 :
    PG 2 a5Rels ≃* alternatingGroup (Fin 5) :=
  (a5Equiv (C := ⊤) a5a_sq a5b_cube a5ab_pow closure_a5ab
    (by rw [Subgroup.card_top, card_alt5])).trans Subgroup.topEquiv

end T84Co

end CFSG.OddStandard.SmallF3.Omega
