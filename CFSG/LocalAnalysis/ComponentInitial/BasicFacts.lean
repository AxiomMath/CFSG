module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem p_group_normalizer_step {S : Type*} [Group S] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (hS : IsPGroup p S) {U : Subgroup S} (hU : U < ⊤) :
    ∃ V : Subgroup S, U ≤ V ∧ (U.subgroupOf V).Normal ∧ U.relIndex V = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hS.to_subgroup U)
  have hlt : Nat.card U < Nat.card S := by
    have := card_lt_of_lt hU
    simpa using this
  have hkn : k < n := by
    rw [hk, hn] at hlt
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hlt
  have hdvd : p ^ (k + 1) ∣ Nat.card S := hn ▸ pow_dvd_pow p hkn
  obtain ⟨V, hV, hUV⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hk
  have hrel : U.relIndex V = p := by
    have h := Subgroup.relIndex_mul_index hUV
    have h2 := (V.card_mul_index : Nat.card V * V.index = Nat.card S)
    have h3 := (U.card_mul_index : Nat.card U * U.index = Nat.card S)
    rw [hk, ← h] at h3
    rw [hV] at h2
    have hVi : 0 < V.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h4 : p ^ k * (U.relIndex V * V.index) = p ^ k * (p * V.index) := by
      rw [h3, ← h2, pow_succ, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right hVi (Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos k) h4)
  refine ⟨V, hUV, ?_, hrel⟩
  apply normal_of_index_eq_minFac_card
  rw [show (U.subgroupOf V).index = p from hrel, hV,
    Nat.Prime.pow_minFac hp.out (Nat.succ_ne_zero k)]

theorem finite_field_prime_power_characteristic {K : Type*} [Field K] {p k : ℕ} (hp : p.Prime)
    (_hk : 1 ≤ k) (hK : Nat.card K = p ^ k) : CharP K p := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos k).ne')
  have := Fintype.ofFinite K
  obtain ⟨q, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn.2] at hK
  have hdvd : ringChar K ∣ p ^ k := hK ▸ dvd_pow_self _ q.ne_zero
  have hq : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hn.1 hp).1 (hn.1.dvd_of_dvd_pow hdvd)
  rw [← hq]
  exact ringChar.charP K

theorem p_group_normalizer_condition {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {U : Subgroup P} (hU : U < ⊤) : U < normalizer (U : Set P) := by
  have := hP.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent U hU

theorem frattini_generator_lifting {G : Type*} [Group G] [Finite G] (S : Set G)
    (hS : closure (QuotientGroup.mk' (frattini G) '' S) = ⊤) : closure S = ⊤ := by
  have h1 : (closure S).map (QuotientGroup.mk' (frattini G)) = ⊤ := by
    rw [MonoidHom.map_closure, hS]
  have h2 : closure S ⊔ frattini G = ⊤ := by
    have := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini G))) h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
  exact frattini_nongenerating h2

end CFSG.LocalAnalysis.ComponentInitial
