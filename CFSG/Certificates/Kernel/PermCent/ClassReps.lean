module

public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.KC.ClassReps

open Subgroup CFSG.Sporadic.SmallOddCore

variable {M : Type*} [Group M]

theorem ncard_conjClass_of_reps [Finite M] {ng N : ℕ} (g : ℕ → M) {t : M} (c : ℕ → M)
    (hreach : ∀ i < N, ∃ h ∈ closure (g '' {k | k < ng}), c i = h * t * h⁻¹)
    (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, g k * c i * (g k)⁻¹ = c j)
    (hroot : ∃ i < N, c i = t) (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    (conjClass (closure (g '' {k | k < ng})) t).ncard = N := by
  classical
  let Tset : Set M := {y | ∃ i < N, c i = y}
  have hmaps : ∀ k < ng, ∀ y ∈ Tset, g k * y * (g k)⁻¹ ∈ Tset := by
    rintro k hk y ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := hcl i hi k hk
    exact ⟨j, hj, e.symm⟩
  have hall : ∀ p ∈ closure (g '' {k | k < ng}), ∀ y ∈ Tset, p * y * p⁻¹ ∈ Tset := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hmaps k hk
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  have hset : conjClass (closure (g '' {k | k < ng})) t = Tset := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, hi, e⟩ := hroot
      exact hall p hp t ⟨i, hi, e⟩
    · rintro ⟨i, hi, rfl⟩
      exact hreach i hi
  have himg : Tset = c '' (Finset.range N : Set ℕ) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simpa using hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simpa using hi, rfl⟩
  have hio : Set.InjOn c (Finset.range N : Set ℕ) :=
    fun i hi j hj e => hinj i (by simpa using hi) j (by simpa using hj) e
  rw [hset, himg, hio.ncard_image, Set.ncard_coe_finset, Finset.card_range]

theorem oddCore_eq_bot_of_three (K : Subgroup M) [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a * 3) {x h : M} (hx : x ∈ K) (hh : h ∈ K) (hx3 : orderOf x = 3)
    (hw : 2 ∣ orderOf (x * (h * x * h⁻¹))) : CFSG.oddCore ↥K = ⊥ := by
  set O := CFSG.oddCore ↥K
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.SmallLocal.odd_card_oddCore
  have hOdvd : Nat.card O ∣ 2 ^ a * 3 := hK ▸ Subgroup.card_subgroup_dvd_card O
  have hO3 : Nat.card O ∣ 3 :=
    (Nat.Coprime.pow_right a hOodd.coprime_two_right).dvd_of_dvd_mul_left hOdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hO3 with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    let x' : K := ⟨x, hx⟩
    let h' : K := ⟨h, hh⟩
    have hq : Nat.card (↥K ⧸ O) = 2 ^ a := by
      have e := Subgroup.card_eq_card_quotient_mul_card_subgroup O
      rw [hK, h3] at e
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num) e).symm
    have hxO : x' ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      have d1 : orderOf ((x' : ↥K ⧸ O)) ∣ 3 := by
        have e := orderOf_map_dvd (QuotientGroup.mk' O) x'
        rwa [Subgroup.orderOf_mk, hx3] at e
      have d2 : orderOf ((x' : ↥K ⧸ O)) ∣ 2 ^ a := hq ▸ orderOf_dvd_natCard _
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right a (by norm_num)) d1 d2)
    have hyO : x' * (h' * x' * h'⁻¹) ∈ O :=
      O.mul_mem hxO ((CFSG.oddCore_normal ↥K).conj_mem _ hxO h')
    have hdvd : orderOf (⟨_, hyO⟩ : O) ∣ 3 := h3 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at hdvd
    have e : ((x' * (h' * x' * h'⁻¹) : K) : M) = x * (h * x * h⁻¹) := rfl
    rw [e] at hdvd
    have := hw.trans hdvd
    omega

end CFSG.KC.ClassReps

end
