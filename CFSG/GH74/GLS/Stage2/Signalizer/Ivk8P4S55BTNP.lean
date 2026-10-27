module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4QuadOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrNP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

section Comm

variable {Γ : Type*} [Group Γ]

theorem closure_comm_two {s : Set Γ} (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (h2 : ∀ x ∈ s, ∃ n : ℕ, x ^ 2 ^ n = 1) :
    (∀ x ∈ closure s, ∀ y ∈ closure s, x * y = y * x) ∧ IsPGroup 2 ↥(closure s) := by
  have hcs : closure s ≤ centralizer s := by
    rw [closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    exact hc y hy x hx
  have hcomm : ∀ x ∈ closure s, ∀ y ∈ closure s, x * y = y * x := by
    intro x hx y hy
    have hle : closure s ≤ centralizer ({x} : Set Γ) := by
      rw [closure_le]
      intro w hw
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hcs hx)) w hw
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  refine ⟨hcomm, ?_⟩
  have key : ∀ y ∈ closure s, ∃ n : ℕ, y ^ 2 ^ n = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h2 y hy
    | one => exact ⟨0, by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨m, hm⟩ := iha
      obtain ⟨n, hn⟩ := ihb
      have hab : Commute a b := hcomm a ha b hb
      have e : 2 ^ (m + n) = 2 ^ m * 2 ^ n := pow_add 2 m n
      refine ⟨m + n, ?_⟩
      rw [hab.mul_pow, e, pow_mul, hm, one_pow, one_mul, Nat.mul_comm, pow_mul, hn, one_pow]
    | inv a ha iha =>
      obtain ⟨m, hm⟩ := iha
      exact ⟨m, by rw [inv_pow, hm, inv_one]⟩
  rintro ⟨x, hx⟩
  obtain ⟨n, hn⟩ := key x hx
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem mem_normalizer_of_map_conj_eq {K : Subgroup Γ} {b : Γ}
    (h : K.map (MulAut.conj b).toMonoidHom = K) : b ∈ normalizer (K : Set Γ) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : b * y * b⁻¹ = b * x * b⁻¹ := hyx
      simpa using h2
    rw [← this]
    exact hy

end Comm

variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V]

theorem quad_mem_normalizer_component (hp2 : p ≠ 2) (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ)
    (hρ : Function.Injective ρ) {a : Γ}
    (hquad : (((ρ a : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) {K : Subgroup Γ}
    (hK : IsComponent K) : a ∈ normalizer (K : Set Γ) := by
  by_contra hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hn (Subgroup.one_mem _)
  have hap : a ^ p = 1 :=
    hρ (by rw [map_pow, map_one]; exact quadratic_pow_prime_eq_one (F := ZMod p) (V := V) hquad)
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  have hm : ∀ m : ℕ, 0 < m → m < p → a ^ m ∉ normalizer (K : Set Γ) := by
    intro m hm0 hmp hmem
    have hcop : m.Coprime (orderOf a) := by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun h => absurd (Nat.le_of_dvd hm0 h) (by omega))).symm
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    exact hn (hc ▸ Subgroup.pow_mem _ hmem c)
  have hcm : ∀ m : ℕ, 0 < m → m < p → ∀ u ∈ K, ∀ w ∈ K,
      u * (a ^ m * w * (a ^ m)⁻¹) = (a ^ m * w * (a ^ m)⁻¹) * u := by
    intro m hm0 hmp u hu w hw
    set K' : Subgroup Γ := K.map (MulAut.conj (a ^ m)).toMonoidHom with hK'
    have hK'c : IsComponent K' := LocalCores.isComponent_map_mulEquiv (MulAut.conj (a ^ m)) hK
    have hne : K ≠ K' := fun h => hm m hm0 hmp (mem_normalizer_of_map_conj_eq h.symm)
    rcases LocalCores.distinct_components_commute hK hK'c with h | h
    · exact absurd h hne
    · have hw' : a ^ m * w * (a ^ m)⁻¹ ∈ K' := ⟨w, hw, rfl⟩
      have : ⁅u, a ^ m * w * (a ^ m)⁻¹⁆ ∈ (⊥ : Subgroup Γ) :=
        h ▸ Subgroup.commutator_mem_commutator hu hw'
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
  obtain ⟨x, hxK, ⟨n₀, hn₀⟩, k₀, hk₀K, hxk₀⟩ :
      ∃ x ∈ K, (∃ n : ℕ, x ^ 2 ^ n = 1) ∧ ∃ k ∈ K, x * k ≠ k * x := by
    let S₀ : Sylow 2 ↥K := default
    have hS : IsSylowOf 2 (S₀ : Subgroup ↥K) ⊤ := by
      rw [isSylowOf_iff]
      exact ⟨le_top, S₀.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S₀.not_dvd_index⟩
    by_contra hall
    push Not at hall
    refine not_sylow_two_le_center hK.1 hS fun y hy => ?_
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨n, hn⟩ := S₀.isPGroup' ⟨y, hy⟩
    have hyn : (y : Γ) ^ 2 ^ n = 1 := by
      have := congrArg (fun v : ↥(S₀ : Subgroup ↥K) => ((v : ↥K) : Γ)) hn
      simpa using this
    exact Subtype.ext (hall y y.2 ⟨n, hyn⟩ w w.2).symm
  set s : Set Γ := {y | ∃ i : ℕ, i < p ∧ y = a ^ i * x * (a ^ i)⁻¹} with hs
  have hxs : x ∈ s := ⟨0, hp.pos, by simp⟩
  have hsc : ∀ y ∈ s, ∀ y' ∈ s, y * y' = y' * y := by
    have key : ∀ i j : ℕ, i < j → j < p →
        (a ^ i * x * (a ^ i)⁻¹) * (a ^ j * x * (a ^ j)⁻¹) =
          (a ^ j * x * (a ^ j)⁻¹) * (a ^ i * x * (a ^ i)⁻¹) := by
      intro i j hij hjp
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
      have hc := hcm (d + 1) (by omega) (by omega) x hxK x hxK
      have e : a ^ (i + d + 1) = a ^ i * a ^ (d + 1) := by rw [← pow_add]; ring_nf
      rw [e]
      calc (a ^ i * x * (a ^ i)⁻¹) * (a ^ i * a ^ (d + 1) * x * (a ^ i * a ^ (d + 1))⁻¹)
          = a ^ i * (x * (a ^ (d + 1) * x * (a ^ (d + 1))⁻¹)) * (a ^ i)⁻¹ := by group
        _ = a ^ i * ((a ^ (d + 1) * x * (a ^ (d + 1))⁻¹) * x) * (a ^ i)⁻¹ := by rw [hc]
        _ = (a ^ i * a ^ (d + 1) * x * (a ^ i * a ^ (d + 1))⁻¹) * (a ^ i * x * (a ^ i)⁻¹) := by
          group
    rintro y ⟨i, hi, rfl⟩ y' ⟨j, hj, rfl⟩
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact key i j hij hj
    · rfl
    · exact (key j i hij hi).symm
  have hs2 : ∀ y ∈ s, ∃ n : ℕ, y ^ 2 ^ n = 1 := by
    rintro y ⟨i, -, rfl⟩
    exact ⟨n₀, by rw [conj_pow, hn₀]; group⟩
  obtain ⟨hAc, hA2⟩ := closure_comm_two hsc hs2
  have hconj : ∀ b : Γ, (∀ y ∈ s, b * y * b⁻¹ ∈ s) → ∀ w ∈ closure s, b * w * b⁻¹ ∈ closure s := by
    intro b hb w hw
    have hle : (closure s).map (MulAut.conj b).toMonoidHom ≤ closure s := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact subset_closure (hb y hy)
    exact hle ⟨w, hw, rfl⟩
  have hfwd : ∀ y ∈ s, a * y * a⁻¹ ∈ s := by
    rintro y ⟨i, hi, rfl⟩
    by_cases hip : i + 1 < p
    · exact ⟨i + 1, hip, by rw [pow_succ']; group⟩
    · have hi' : i + 1 = p := by omega
      refine ⟨0, hp.pos, ?_⟩
      have e : a * a ^ i = 1 := by rw [← pow_succ', hi', hap]
      calc a * (a ^ i * x * (a ^ i)⁻¹) * a⁻¹ = (a * a ^ i) * x * (a * a ^ i)⁻¹ := by group
        _ = a ^ 0 * x * (a ^ 0)⁻¹ := by rw [e]; simp
  have hbwd : ∀ y ∈ s, a⁻¹ * y * a⁻¹⁻¹ ∈ s := by
    rintro y ⟨i, hi, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine ⟨p - 1, by omega, ?_⟩
      have e : a⁻¹ = a ^ (p - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hap]
      rw [e]
      group
    · refine ⟨i - 1, by omega, ?_⟩
      have e : a ^ i = a * a ^ (i - 1) := by rw [← pow_succ', Nat.sub_add_cancel hi0]
      rw [e]
      group
  have hnorm : a ∈ normalizer ((closure s : Subgroup Γ) : Set Γ) := by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hconj a hfwd w hw, fun hw => ?_⟩
    have := hconj a⁻¹ hbwd _ hw
    simpa [mul_assoc] using this
  have hcent := quadratic_centralizes_abelian (F := ZMod p) (V := V) hp2 (Ne.symm hp2) ρ hρ hquad
    hA2 hAc hnorm
  have hax : a * x * a⁻¹ = x := by rw [hcent x (subset_closure hxs)]; group
  apply hxk₀
  have h1 := hcm 1 (by omega) hp.one_lt k₀ hk₀K x hxK
  rw [pow_one, hax] at h1
  exact h1.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
