module

public import CFSG.GH74.GLS.C3.Layer1.Back114W
public import CFSG.GH74.GLS.C3.Layer1.Back114Fin

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfigW

theorem inv_conj_x (h : IsAConfigW n x K T Q S a) : a⁻¹ * x * a = a * x * a⁻¹ := by
  have h1 : a ^ 2 * x = x * a ^ 2 := mem_centralizer_singleton_iff.1 (h.T_le_C h.a_mem.2.2.2)
  have h2 : a ^ 2 * x * (a ^ 2)⁻¹ = x := by rw [h1]; group
  calc a⁻¹ * x * a = a⁻¹ * (a ^ 2 * x * (a ^ 2)⁻¹) * a := by rw [h2]
    _ = a * x * a⁻¹ := by group

theorem conj_conj_x (h : IsAConfigW n x K T Q S a) : a * (a * x * a⁻¹) * a⁻¹ = x := by
  have := h.inv_conj_x
  calc a * (a * x * a⁻¹) * a⁻¹ = a * (a⁻¹ * x * a) * a⁻¹ := by rw [this]
    _ = x := by group

theorem K_inf_CxK_odd (h : IsAConfigW n x K T Q S a) (hn : 4 ≤ n) {k : G} (hk : k ∈ K)
    (hkX : k ∈ CxK x K) : Odd (orderOf k) := by
  obtain ⟨e⟩ := h.kbar
  let q : ↥K →* (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.mk' (pPrimeCore 2 ↥K)
  let κ : ↥K := ⟨k, hk⟩
  have hcard4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
  have hcent : e (q κ) ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective g'
    rw [← map_mul, ← map_mul]
    congr 1
    have hcomm : ⁅k', κ⁆ ∈ pPrimeCore 2 ↥K := by
      have h1 := hkX.2.2.2 k'.1 k'.2
      obtain ⟨y, hy, hyeq⟩ := h1
      have : y = ⁅k', κ⁆ := Subtype.ext hyeq
      rwa [this] at hy
    have h1 : q ⁅k', κ⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hcomm
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  rw [alternatingGroup.center_eq_bot hcard4, Subgroup.mem_bot] at hcent
  have h1 : q κ = 1 := e.injective (by rw [hcent, map_one])
  have h2 : κ ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
  exact odd_orderOf_of_mem_pPrimeCoreOf (H := K) ⟨κ, h2, rfl⟩

theorem sign_psi_of_mem_K (h : IsAConfigW n x K T Q S a)
    (ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin n)) {k : G} (hk : k ∈ K) :
    Equiv.Perm.sign (ψ ⟨k, h.K_le_C hk⟩) = 1 := by
  have hcomp : CFSG.IsComponent (K.subgroupOf (centralizer ({x} : Set G))) :=
    h.terminal.2.1.2
  have hperf : Group.IsPerfect ↥(K.subgroupOf (centralizer ({x} : Set G))) := hcomp.1.1
  let φ : ↥(K.subgroupOf (centralizer ({x} : Set G))) →* ℤˣ :=
    Equiv.Perm.sign.comp (ψ.comp (K.subgroupOf (centralizer ({x} : Set G))).subtype)
  have hker : commutator ↥(K.subgroupOf (centralizer ({x} : Set G))) ≤ φ.ker := by
    show ⁅(⊤ : Subgroup ↥(K.subgroupOf (centralizer ({x} : Set G)))), ⊤⁆ ≤ φ.ker
    refine Subgroup.commutator_le.2 ?_
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hmem : (⟨⟨k, h.K_le_C hk⟩, hk⟩ : ↥(K.subgroupOf (centralizer ({x} : Set G)))) ∈ φ.ker := by
    apply hker
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top _
  exact hmem

theorem U_le_CxK_of_five_six (h : IsAConfigW n x K T Q S a) (hn : n = 5 ∨ n = 6)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) :
    ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G),
      Odd (orderOf u) → u ∈ CxK x K := by
  intro u hu hodd
  obtain ⟨ψ, hker⟩ := h.quotientType
  set z : G := a * x * a⁻¹ with hzdef
  have hzT : z ∈ T := hz.1
  have hzK : z ∈ K := hz.2
  have hzC : z ∈ centralizer ({x} : Set G) := h.T_le_C hzT
  have hz2 : z ^ 2 = 1 := by
    have hx2 := h.x_sq
    calc z ^ 2 = a * x ^ 2 * a⁻¹ := by rw [hzdef]; exact conj_pow
      _ = 1 := by rw [hx2]; group
  have hz1 : z ≠ 1 := by
    intro h1
    apply h.x_ne_one
    have := h.conj_conj_x
    rw [← hzdef, h1] at this
    simpa using this.symm
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hxY : x ∈ (Ysub x K T a : Subgroup G) := by
    unfold Ysub
    refine Subgroup.mem_sup_left ⟨z, hz, ?_⟩
    show a * z * a⁻¹ = x
    rw [hzdef]
    exact h.conj_conj_x
  have hzY : z ∈ (Ysub x K T a : Subgroup G) := by
    unfold Ysub
    exact Subgroup.mem_sup_right (mem_zpowers _)
  have hux : x * u = u * x := (mem_centralizer_iff.1 hu) x hxY
  have huz : z * u = u * z := (mem_centralizer_iff.1 hu) z hzY
  have huC : u ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hux.symm
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  let σ := ψ ⟨z, hzC⟩
  let π := ψ ⟨u, huC⟩
  have hσ2 : σ ^ 2 = 1 := by
    show ψ ⟨z, hzC⟩ ^ 2 = 1
    rw [← map_pow]
    have : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ^ 2 = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have hodd' := h.K_inf_CxK_odd hn4 hzK hmem
    rw [hzord] at hodd'
    exact (Nat.not_even_iff_odd.2 hodd') even_two
  have hσs : Equiv.Perm.sign σ = 1 := h.sign_psi_of_mem_K ψ hzK
  have hcomm : π * σ = σ * π := by
    show ψ ⟨u, huC⟩ * ψ ⟨z, hzC⟩ = ψ ⟨z, hzC⟩ * ψ ⟨u, huC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext huz.symm
  have hπodd : Odd (orderOf π) := by
    have h1 : orderOf π ∣ orderOf (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) :=
      orderOf_map_dvd ψ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hπ1 : π = 1 := by
    rcases hn with rfl | rfl
    · refine no_odd_commuting_five σ π hσ2 hσ1 hσs hcomm ?_
      have hd : orderOf π ∣ 15 * 2 ^ 3 := by
        have h1 := orderOf_dvd_natCard π
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
        have h2 : (5 : ℕ).factorial = 15 * 2 ^ 3 := by decide
        rwa [h2] at h1
      exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_odd_of_dvd_mul_two_pow hπodd hd)
    · refine no_odd_commuting_six σ π hσ2 hσ1 hσs hcomm ?_
      have hd : orderOf π ∣ 45 * 2 ^ 4 := by
        have h1 := orderOf_dvd_natCard π
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
        have h2 : (6 : ℕ).factorial = 45 * 2 ^ 4 := by decide
        rwa [h2] at h1
      exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_odd_of_dvd_mul_two_pow hπodd hd)
  have hmem : (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := hπ1
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  exact hmem

end IsAConfigW

end Config

end CFSG.GH74.GLS
