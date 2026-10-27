module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bL
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bUSD
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK

namespace Lemma44b

theorem sylow_iso_of_quotient {K : Type} [Group K] [Finite K] {G₂ : Type} [Group G₂]
    {C : Subgroup K} {N : Subgroup G₂} [N.Normal] (hN : Odd (Nat.card N))
    (φ : ↥C ≃* G₂ ⧸ N) {M : Subgroup G₂} {Model : Type} [Group Model] (e : ↥M ≃* Model)
    (hM : Nat.card M = 2 ^ (Nat.card K).factorization 2) (S : Sylow 2 K) :
    Nonempty (↥S ≃* Model) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Φ : G₂ →* K := C.subtype.comp (φ.symm.toMonoidHom.comp (QuotientGroup.mk' N))
  let Ψ : ↥M →* K := Φ.comp M.subtype
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : φ.symm (QuotientGroup.mk (m : G₂)) = 1 :=
      Subtype.ext (hm.trans (Subgroup.coe_one C).symm)
    have h2 : (QuotientGroup.mk (m : G₂) : G₂ ⧸ N) = 1 :=
      φ.symm.injective (h1.trans (map_one φ.symm).symm)
    have hmN : (m : G₂) ∈ N := (QuotientGroup.eq_one_iff _).mp h2
    have hpow : (m : G₂) ^ 2 ^ ((Nat.card K).factorization 2) = 1 := by
      have h3 : m ^ Nat.card M = 1 := pow_card_eq_one'
      rw [hM] at h3
      have h4 := congrArg (fun x : M => (x : G₂)) h3
      simpa using h4
    exact Subtype.ext (CFSG.BrauerLinearThree.eq_one_of_mem_odd_of_pow_two_pow hN hmN hpow)
  have hcard : Nat.card Ψ.range = 2 ^ (Nat.card K).factorization 2 := by
    rw [← hM]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv).symm
  let P : Sylow 2 K := Sylow.ofCard Ψ.range hcard
  exact ⟨(Sylow.equiv S P).trans ((MonoidHom.ofInjective hΨ).symm.trans e)⟩

theorem card_K_L3 {K : Type} [Group K] {p n : ℕ} (hKL : IsLnEps 3 K 1 (p ^ n)) :
    ∃ c, Odd c ∧ Nat.card K * c = (p ^ n) ^ 3 * ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 - 1) := by
  rcases hKL with ⟨-, F, hF, hfin, hcard, ⟨e⟩⟩ | ⟨h1, -⟩
  · refine ⟨Nat.gcd 3 (Nat.card F - 1), Lemma44bOrd.odd_gcd_three _, ?_⟩
    rw [Nat.card_congr e.toEquiv, Lemma44bOrd.card_statedProj_statedSL_three_mul, hcard]
  · exact absurd h1 (by norm_num)

theorem one_le_of_isLnEps {K : Type} [Group K] {ε : ℤ} {p n : ℕ}
    (hK : IsLnEps 3 K ε (p ^ n)) : 1 ≤ n := by
  by_contra hn0
  have hn0' : n = 0 := by omega
  subst hn0'
  rcases hK with ⟨-, F, hF, hFin, hcardF, -⟩ | ⟨-, F, hF, hFin, hcardF, -⟩
  · have h1 := Finite.one_lt_card (α := F)
    rw [hcardF] at h1
    simp at h1
  · have h1 := Finite.one_lt_card (α := F)
    rw [hcardF] at h1
    simp at h1

theorem card_K_U3 {K : Type} [Group K] {p n : ℕ} (hp : p.Prime) (hKU : IsLnEps 3 K (-1) (p ^ n)) :
    ∃ c, Odd c ∧ Nat.card K * c = (p ^ n) ^ 3 * ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 + 1) := by
  have hn : 1 ≤ n := one_le_of_isLnEps hKU
  rcases hKU with ⟨h1, -⟩ | ⟨-, F, hF, hfin, hcard, ⟨e⟩⟩
  · exact absurd h1 (by norm_num)
  · have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F :=
      ⟨hp, hn, by rw [hcard, ← pow_mul, mul_comm]⟩
    refine ⟨Nat.gcd 3 (p ^ n + 1), Lemma44bOrd.odd_gcd_three _, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    exact Lemma44bOrd.card_statedProj_statedSU_three_mul hdata

theorem exists_involution {K : Type} [Group K] [Finite K] (h : 2 ∣ Nat.card K) :
    ∃ z : K, orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 h

theorem odd_card_N {m : ℕ} (h : m = 1 ∨ m = 3) : Odd m := by
  rcases h with rfl | rfl <;> decide

theorem sylow_L3_sd {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKL : IsLnEps 3 K 1 (p ^ n)) (hq : p ^ n % 4 = 3) (S : Sylow 2 K) :
    ∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup m) := by
  obtain ⟨c, hc, hcard⟩ := card_K_L3 hKL
  have hv := Lemma44bOrd.factorization_L3_sd hq hc hcard
  have h2 : 2 ∣ Nat.card K := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨z, hz⟩ := exists_involution h2
  obtain ⟨F, hF, hfin, N, hNn, hFcard, hNcard, ⟨φ⟩⟩ := ivk_4_1a_L3 K p n hp hp2 hKL z hz
  have hq' : Nat.card F % 4 = 3 := by rw [hFcard]; exact hq
  obtain ⟨hm2, M, hMcard, ⟨eM⟩⟩ := Lemma44bL.exists_GL2_semidihedral (F := F) hq'
    (m := (p ^ n + 1).factorization 2) (by rw [hFcard])
  have hMc : Nat.card M = 2 ^ (Nat.card K).factorization 2 := by rw [hMcard, hv]
  obtain ⟨e⟩ := sylow_iso_of_quotient (odd_card_N hNcard) φ eM hMc S
  exact ⟨(p ^ n + 1).factorization 2 + 2, by omega, ⟨e⟩⟩

theorem sylow_L3_wr {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKL : IsLnEps 3 K 1 (p ^ n)) (hq : p ^ n % 4 = 1) (hq1 : 1 < p ^ n) (S : Sylow 2 K) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup m) := by
  obtain ⟨c, hc, hcard⟩ := card_K_L3 hKL
  have hv := Lemma44bOrd.factorization_L3_wr hq hq1 hc hcard
  have h2 : 2 ∣ Nat.card K := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨z, hz⟩ := exists_involution h2
  obtain ⟨F, hF, hfin, N, hNn, hFcard, hNcard, ⟨φ⟩⟩ := ivk_4_1a_L3 K p n hp hp2 hKL z hz
  have hq' : Nat.card F % 4 = 1 := by rw [hFcard]; exact hq
  obtain ⟨hk2, M, hMcard, ⟨eM⟩⟩ := Lemma44bL.exists_GL2_wreathed (F := F) hq'
    (k := (p ^ n - 1).factorization 2) (by rw [hFcard])
  have hMc : Nat.card M = 2 ^ (Nat.card K).factorization 2 := by rw [hMcard, hv]
  obtain ⟨e⟩ := sylow_iso_of_quotient (odd_card_N hNcard) φ eM hMc S
  exact ⟨(p ^ n - 1).factorization 2, hk2, ⟨e⟩⟩

theorem sylow_U3_wr {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKU : IsLnEps 3 K (-1) (p ^ n)) (hq : p ^ n % 4 = 3) (S : Sylow 2 K) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup m) := by
  have hn : 1 ≤ n := one_le_of_isLnEps hKU
  obtain ⟨c, hc, hcard⟩ := card_K_U3 hp hKU
  have hv := Lemma44bOrd.factorization_U3_wr hq hc hcard
  have h2 : 2 ∣ Nat.card K := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨z, hz⟩ := exists_involution h2
  obtain ⟨F, hF, hfin, N, hNn, hFcard, hNcard, ⟨φ⟩⟩ := ivk_4_1a_U3 K p n hp hp2 hKU z hz
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F :=
    ⟨hp, hn, by rw [hFcard, ← pow_mul, mul_comm]⟩
  obtain ⟨hk2, M, hMcard, ⟨eM⟩⟩ := Lemma44bUW.exists_GU2_wreathed hdata hq
    (k := (p ^ n + 1).factorization 2) rfl
  have hMc : Nat.card M = 2 ^ (Nat.card K).factorization 2 := by rw [hMcard, hv]
  obtain ⟨e⟩ := sylow_iso_of_quotient (odd_card_N hNcard) φ eM hMc S
  exact ⟨(p ^ n + 1).factorization 2, hk2, ⟨e⟩⟩

theorem sylow_U3_sd {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKU : IsLnEps 3 K (-1) (p ^ n)) (hq : p ^ n % 4 = 1) (hq1 : 1 < p ^ n) (S : Sylow 2 K) :
    ∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup m) := by
  have hn : 1 ≤ n := one_le_of_isLnEps hKU
  obtain ⟨c, hc, hcard⟩ := card_K_U3 hp hKU
  have hv := Lemma44bOrd.factorization_U3_sd hq hq1 hc hcard
  have h2 : 2 ∣ Nat.card K := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨z, hz⟩ := exists_involution h2
  obtain ⟨F, hF, hfin, N, hNn, hFcard, hNcard, ⟨φ⟩⟩ := ivk_4_1a_U3 K p n hp hp2 hKU z hz
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F :=
    ⟨hp, hn, by rw [hFcard, ← pow_mul, mul_comm]⟩
  obtain ⟨hk2, M, hMcard, ⟨eM⟩⟩ := Lemma44bUSD.exists_GU2_semidihedral hdata hq
    (k := (p ^ n - 1).factorization 2) rfl
  have hMc : Nat.card M = 2 ^ (Nat.card K).factorization 2 := by rw [hMcard, hv]
  obtain ⟨e⟩ := sylow_iso_of_quotient (odd_card_N hNcard) φ eM hMc S
  exact ⟨(p ^ n - 1).factorization 2 + 2, by omega, ⟨e⟩⟩

end Lemma44b

open Lemma44b in
theorem ivk_4_4b : IVK_4_4b := by
  intro K _ _ ε p n hp hp2 hK S
  have hn : 1 ≤ n := one_le_of_isLnEps hK
  have hodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hq1 : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
  have hmod : p ^ n % 4 = 1 ∨ p ^ n % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hK with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hε with rfl | rfl
  · refine ⟨fun hnot => ?_, fun hcong => ?_⟩
    · have h3 : p ^ n % 4 = 3 := by
        rcases hmod with h | h
        · exfalso
          apply hnot
          unfold Int.ModEq
          omega
        · exact h
      obtain ⟨m, hm, hS⟩ := sylow_L3_sd hp hp2 hK h3 S
      exact ⟨m, hm, hS⟩
    · have h1 : p ^ n % 4 = 1 := by
        unfold Int.ModEq at hcong
        omega
      exact sylow_L3_wr hp hp2 hK h1 hq1 S
  · refine ⟨fun hnot => ?_, fun hcong => ?_⟩
    · have h1 : p ^ n % 4 = 1 := by
        rcases hmod with h | h
        · exact h
        · exfalso
          apply hnot
          unfold Int.ModEq
          omega
      obtain ⟨m, hm, hS⟩ := sylow_U3_sd hp hp2 hK h1 hq1 S
      exact ⟨m, hm, hS⟩
    · have h3 : p ^ n % 4 = 3 := by
        unfold Int.ModEq at hcong
        omega
      exact sylow_U3_wr hp hp2 hK h3 S

end CFSG.GH74.GLS.IVK.Proofs2
