module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Case11

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem centralizer_inf_eq_S {P : Subgroup G} (hP : IsPGroup 2 P) (hSP : H.S ≤ P) :
    centralizer ({H.t} : Set G) ⊓ P = H.S := by
  have hQ : IsPGroup 2 (centralizer ({H.t} : Set G) ⊓ P : Subgroup G) := hP.to_le inf_le_right
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card (centralizer ({H.t} : Set G) ⊓ P : Subgroup G) ∣
      Nat.card (centralizer ({H.t} : Set G)) := Subgroup.card_dvd_of_le inf_le_left
  rw [hk, H.card_centralizer] at hdvd
  have hcop : Nat.Coprime (2 ^ k) 495 := by
    apply Nat.Coprime.pow_left
    norm_num
  have h32 : 2 ^ k ∣ 32 := by
    have : 2 ^ k ∣ 32 * 495 := by simpa using hdvd
    exact hcop.dvd_of_dvd_mul_right this
  have hle : Nat.card (centralizer ({H.t} : Set G) ⊓ P : Subgroup G) ≤ 32 := by
    rw [hk]; exact Nat.le_of_dvd (by norm_num) h32
  have hSQ : H.S ≤ centralizer ({H.t} : Set G) ⊓ P := le_inf H.S_le_centralizer hSP
  exact (Subgroup.eq_of_le_of_card_ge hSQ (by rw [H.card_S]; exact hle)).symm

theorem exists_P (hn : Nat.card {x : G // IsConj H.t x} % 4 = 2) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ H.S ≤ P ∧ Nat.card P = 64 ∧ ¬ 2 ∣ P.index := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := H.isPGroup_S.exists_le_sylow
  refine ⟨P, P.isPGroup', hSP, ?_, P.not_dvd_index⟩
  have hcard := P.card_eq_multiplicity
  obtain ⟨q, hq⟩ : ∃ q, Nat.card {x : G // IsConj H.t x} = 4 * q + 2 :=
    ⟨Nat.card {x : G // IsConj H.t x} / 4, by omega⟩
  have hG : Nat.card G = 2 ^ 6 * (495 * (2 * q + 1)) := by
    rw [← H.card_A_mul, hq]; ring
  have hodd : ¬ 2 ∣ 495 * (2 * q + 1) := by omega
  have hfac : (Nat.card G).factorization 2 = 6 := by
    rw [hG, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    simp
  rw [hfac] at hcard
  exact hcard

theorem normal_S_in_P {P : Subgroup G} (hcard : Nat.card P = 64) (hSP : H.S ≤ P) :
    (H.S.subgroupOf P).Normal := by
  have hc : Nat.card (H.S.subgroupOf P) = 32 := by
    rw [← H.card_S]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv)
  have hidx : (H.S.subgroupOf P).index = 2 := by
    have := Subgroup.card_mul_index (H.S.subgroupOf P)
    rw [hc, hcard] at this
    omega
  exact Subgroup.normal_of_index_eq_two hidx

theorem conj_mem_S {P : Subgroup G} (hcard : Nat.card P = 64) (hSP : H.S ≤ P) {x s : G}
    (hx : x ∈ P) (hs : s ∈ H.S) : x * s * x⁻¹ ∈ H.S := by
  have hN := H.normal_S_in_P hcard hSP
  have := hN.conj_mem ⟨s, hSP hs⟩ (by simpa [Subgroup.mem_subgroupOf] using hs) ⟨x, hx⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem mem_normalizer_of_mem_P {P : Subgroup G} (hcard : Nat.card P = 64) (hSP : H.S ≤ P)
    {x : G} (hx : x ∈ P) : x ∈ Subgroup.normalizer (H.S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact H.conj_mem_S hcard hSP hx
  · intro hs
    have := H.conj_mem_S hcard hSP (P.inv_mem hx) hs
    rwa [show x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s by group] at this

theorem conj_eq_tz {P : Subgroup G} (hP : IsPGroup 2 P) (hcard : Nat.card P = 64)
    (hSP : H.S ≤ P) {x : G} (hxP : x ∈ P) (hxS : x ∉ H.S) :
    x * H.t * x⁻¹ = H.t * H.a ^ 4 := by
  have hxN := H.mem_normalizer_of_mem_P hcard hSP hxP
  rcases H.conj_t_cases hxN with h | h | h
  · exfalso
    apply hxS
    rw [← H.centralizer_inf_eq_S hP hSP]
    refine ⟨mem_centralizer_singleton_iff.2 ?_, hxP⟩
    calc x * H.t = (x * H.t * x⁻¹) * x := by group
      _ = H.t * x := by rw [h]
  · exact absurd h (H.conj_t_ne_z hxN)
  · exact h

theorem exists_mem_P_not_mem_S {P : Subgroup G} (hcard : Nat.card P = 64) (hSP : H.S ≤ P) :
    ∃ x ∈ P, x ∉ H.S := by
  by_contra h
  push Not at h
  have hle : P ≤ H.S := h
  have := le_antisymm hle hSP
  rw [this, H.card_S] at hcard
  omega

theorem false_case10 (h2 : ¬ IsConj H.t (H.t * H.a ^ 4))
    (hn : Nat.card {x : G // IsConj H.t x} % 4 = 2) : False := by
  obtain ⟨P, hP, hSP, hcard, -⟩ := H.exists_P hn
  obtain ⟨x, hxP, hxS⟩ := H.exists_mem_P_not_mem_S hcard hSP
  have := H.conj_eq_tz hP hcard hSP hxP hxS
  exact h2 (isConj_iff.2 ⟨x, this⟩)

end Setting

end CFSG.EvenSporadicStandard.M11Std
