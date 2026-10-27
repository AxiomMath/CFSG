module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_conj_agree_closure {N : Subgroup G} {S : Set G} {u v : G}
    (hu : u ∈ normalizer (N : Set G)) (hS : ∀ s ∈ S, s ∈ normalizer (N : Set G))
    (hgen : ∀ s ∈ S, u * s * u⁻¹ * (v * s * v⁻¹)⁻¹ ∈ N) :
    ∀ y ∈ Subgroup.closure S, u * y * u⁻¹ * (v * y * v⁻¹)⁻¹ ∈ N := by
  have hNrm : Subgroup.closure S ≤ normalizer (N : Set G) :=
    (Subgroup.closure_le (K := normalizer (N : Set G))).mpr hS
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
      have ha : u * x * u⁻¹ ∈ normalizer (N : Set G) :=
        mul_mem (mul_mem hu (hNrm hx)) (inv_mem hu)
      have hconj : (u * x * u⁻¹) * (u * y * u⁻¹ * (v * y * v⁻¹)⁻¹) * (u * x * u⁻¹)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp ha (u * y * u⁻¹ * (v * y * v⁻¹)⁻¹)).mp ihy
      have hkey : u * (x * y) * u⁻¹ * (v * (x * y) * v⁻¹)⁻¹
          = ((u * x * u⁻¹) * (u * y * u⁻¹ * (v * y * v⁻¹)⁻¹) * (u * x * u⁻¹)⁻¹)
            * ((u * x * u⁻¹) * (v * x * v⁻¹)⁻¹) := by group
      rw [hkey]
      exact mul_mem hconj ihx
  | inv x hx ih =>
      have ha : u * x * u⁻¹ ∈ normalizer (N : Set G) :=
        mul_mem (mul_mem hu (hNrm hx)) (inv_mem hu)
      have hb : (v * x * v⁻¹) * (u * x * u⁻¹)⁻¹ ∈ N := by
        simpa only [mul_inv_rev, inv_inv] using inv_mem ih
      have hkey : u * x⁻¹ * u⁻¹ * (v * x⁻¹ * v⁻¹)⁻¹
          = (u * x * u⁻¹)⁻¹ * ((v * x * v⁻¹) * (u * x * u⁻¹)⁻¹) * ((u * x * u⁻¹)⁻¹)⁻¹ := by
        group
      rw [hkey]
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem ha) _).mp hb

theorem sec11_exists_order_three [Finite G] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : Nat.card Q = 8) (hK : Nat.card K = 24) :
    ∃ ρ ∈ K, ρ * ρ * ρ = 1 ∧ K = Q ⊔ zpowers ρ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card K := by rw [hK]; norm_num
  obtain ⟨ρ0, hρ0⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3dvd
  have hord : orderOf (ρ0 : G) = 3 := (Subgroup.orderOf_coe ρ0).trans hρ0
  refine ⟨(ρ0 : G), ρ0.2, ?_, ?_⟩
  · have h3 : (ρ0 : G) ^ 3 = 1 := by simpa [hord] using pow_orderOf_eq_one (ρ0 : G)
    simpa [pow_succ, pow_two] using h3
  · have hTK : Q ⊔ zpowers (ρ0 : G) ≤ K :=
      sup_le hQK (Subgroup.zpowers_le.mpr ρ0.2)
    have hTcard : Nat.card ↥(Q ⊔ zpowers (ρ0 : G)) = 24 := by
      have h8 : 8 ∣ Nat.card ↥(Q ⊔ zpowers (ρ0 : G)) := by
        have h := Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ zpowers (ρ0 : G))
        rwa [hQ] at h
      have h3 : 3 ∣ Nat.card ↥(Q ⊔ zpowers (ρ0 : G)) := by
        have h := Subgroup.card_dvd_of_le (le_sup_right : zpowers (ρ0 : G) ≤ Q ⊔ zpowers (ρ0 : G))
        rwa [Nat.card_zpowers, hord] at h
      have h24 : 24 ∣ Nat.card ↥(Q ⊔ zpowers (ρ0 : G)) := by
        have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
        simpa using this
      have hdvd : Nat.card ↥(Q ⊔ zpowers (ρ0 : G)) ∣ Nat.card K := Subgroup.card_dvd_of_le hTK
      rw [hK] at hdvd
      exact Nat.dvd_antisymm hdvd h24
    exact (Subgroup.eq_of_le_of_card_ge hTK (by simp [hTcard, hK])).symm

theorem sec11_cube_mem {N : Subgroup G} {ρ s n : G} (hρ : ρ ∈ normalizer (N : Set G))
    (hρ3 : ρ * ρ * ρ = 1) (hs : s * s = 1) (hsρ : s * ρ = ρ * s)
    (hsN : ∀ m ∈ N, s * m = m * s) (hn : n ∈ N)
    (h3 : (ρ * s * n) * (ρ * s * n) * (ρ * s * n) = 1) : s ∈ N := by
  have hρ2 : ρ * ρ ∈ normalizer (N : Set G) := mul_mem hρ hρ
  have hM1 : (ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hρ2) n).mp hn
  have hM2 : ρ⁻¹ * n * (ρ⁻¹)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hρ) n).mp hn
  have hM : (ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n ∈ N :=
    mul_mem (mul_mem hM1 hM2) hn
  have hcomm : Commute s (ρ * n) :=
    (show Commute s ρ from hsρ).mul_right (show Commute s n from hsN n hn)
  have hs3 : s ^ 3 = s := by rw [pow_succ, pow_two, hs, one_mul]
  have hpow : (ρ * n) ^ 3
      = ρ * ρ * ρ * ((ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n) := by
    rw [pow_succ, pow_two]
    group
  have hρn3 : (ρ * n) ^ 3 = (ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n := by
    rw [hpow, hρ3, one_mul]
  have hfac : ρ * s * n = s * (ρ * n) := by rw [← hsρ, mul_assoc]
  have hstep : (ρ * s * n) * (ρ * s * n) * (ρ * s * n)
      = s * ((ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n) := by
    calc (ρ * s * n) * (ρ * s * n) * (ρ * s * n)
        = (s * (ρ * n)) * (s * (ρ * n)) * (s * (ρ * n)) := by rw [hfac]
      _ = (s * (ρ * n)) ^ 3 := by rw [pow_succ, pow_two]
      _ = s ^ 3 * (ρ * n) ^ 3 := hcomm.mul_pow 3
      _ = s * ((ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n) := by rw [hs3, hρn3]
  have hsm : s * ((ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n) = 1 := by
    rw [← hstep]; exact h3
  have hs_eq : s = ((ρ * ρ)⁻¹ * n * ((ρ * ρ)⁻¹)⁻¹ * (ρ⁻¹ * n * (ρ⁻¹)⁻¹) * n)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hsm
  rw [hs_eq]
  exact inv_mem hM

end CFSG.OddStandard.SmallF3.Omega
