module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AA4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

namespace S4A

theorem perm4_no_six : ∀ π : Equiv.Perm (Fin 4), π ^ 3 = 1 → π ≠ 1 →
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 4 = 1 → σ * π = π * σ → σ = 1 := by
  decide +kernel

section Quot

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_ker_iff {N W : Subgroup G} {K : Type} [Group K] {φ : ↥N →* K}
    (hker : φ.ker = W.subgroupOf N) (n : ↥N) : φ n = 1 ↔ (n : G) ∈ W := by
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem n4_rho_not_mem_W (h : L41GPh3 t L S x₁ x₂ lam rho) : rho ∉ ctxW t x₁ x₂ := by
  intro hρ
  have hWp : IsPGroup 2 ↥(ctxW t x₁ x₂) := h.isPGroup.to_le h.basic.normal_W.1
  obtain ⟨k, hk⟩ := hWp ⟨rho, hρ⟩
  have h1 : rho ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf rho ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  rw [h.ord_rho] at h2
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem n4_W_le_O (h : L41GPh3 t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ l41O2 t x₁ x₂ := by
  rw [n4_O2_eq h]
  refine le_inf (n4_W_le_N h.toL41GPh1) ?_
  intro w hw
  rw [← h.basic.cent_A] at hw
  exact Subgroup.centralizer_le (n4_four_le_A t x₁ x₂) hw

theorem n4_O_comm_rho (h : L41GPh3 t L S x₁ x₂ lam rho) {q : G} (hq : q ∈ l41O2 t x₁ x₂)
    (hc : q * rho * q⁻¹ * rho⁻¹ ∈ ctxW t x₁ x₂) : q ∈ ctxW t x₁ x₂ := by
  obtain ⟨φ, -, hker⟩ := n4_quot_N h
  have hqN : q ∈ l41N t x₁ x₂ := pCoreOf_two_le _ hq
  have hρN : rho ∈ l41N t x₁ x₂ := n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  have hρ3 : φ ⟨rho, hρN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨rho, hρN⟩ : ↥(l41N t x₁ x₂)) ^ 3 = 1 := Subtype.ext (n4_rho_cube h.toCtx0)
    rw [this, map_one]
  have hρ1 : φ ⟨rho, hρN⟩ ≠ 1 := fun h1 => n4_rho_not_mem_W h ((n4_ker_iff hker _).mp h1)
  have hq4 : φ ⟨q, hqN⟩ ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := pCoreOf_two_isPGroup (l41N t x₁ x₂) ⟨q, hq⟩
    have h1 : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (⟨q, hqN⟩ : ↥(l41N t x₁ x₂)) ^ 2 ^ k = 1 := Subtype.ext h1
    exact perm_pow_four_of_two_pow (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]) _
      (by rw [← map_pow, h2, map_one])
  have hcomm : φ ⟨q, hqN⟩ * φ ⟨rho, hρN⟩ = φ ⟨rho, hρN⟩ * φ ⟨q, hqN⟩ := by
    have h1 : φ (⟨q, hqN⟩ * ⟨rho, hρN⟩ * (⟨rho, hρN⟩ * ⟨q, hqN⟩)⁻¹) = 1 := by
      rw [n4_ker_iff hker]
      show q * rho * (rho * q)⁻¹ ∈ ctxW t x₁ x₂
      have e : q * rho * (rho * q)⁻¹ = q * rho * q⁻¹ * rho⁻¹ := by group
      rw [e]
      exact hc
    simp only [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  exact (n4_ker_iff hker _).mp (perm4_no_six _ hρ3 hρ1 _ hq4 hcomm)

theorem n4_center_W (h : L41GPh3 t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂)
    (hc : ∀ m ∈ l41N t x₁ x₂, ⁅n, m⁆ ∈ ctxW t x₁ x₂) : n ∈ ctxW t x₁ x₂ := by
  obtain ⟨φ, hsurj, hker⟩ := n4_quot_N h
  have hcen : ∀ τ : Equiv.Perm (Fin 4), φ ⟨n, hn⟩ * τ = τ * φ ⟨n, hn⟩ := by
    intro τ
    obtain ⟨m, rfl⟩ := hsurj τ
    have h1 : φ (⟨n, hn⟩ * m * (m * ⟨n, hn⟩)⁻¹) = 1 := by
      rw [n4_ker_iff hker]
      show n * (m : G) * ((m : G) * n)⁻¹ ∈ ctxW t x₁ x₂
      have e : n * (m : G) * ((m : G) * n)⁻¹ = ⁅n, (m : G)⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hc m m.2
    simp only [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  exact (n4_ker_iff hker _).mp (CFSG.perm_eq_one_of_forall_commute (by simp) hcen)

end Quot

section QuotCert

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_base_mem_four (h : L41GPh3 t L S x₁ x₂ lam rho) {b : G} (hb : b ∈ baseGrp x₁ x₂)
    (hc : b * rho * b⁻¹ * rho⁻¹ ∈ fourGrp x₁ x₂) : b ∈ fourGrp x₁ x₂ := by
  have hw := h.wreath
  have hFB : ∀ f ∈ fourGrp x₁ x₂, f ∈ baseGrp x₁ x₂ := fun f hf => pt_four_le_base x₁ x₂ hf
  have hF2 : ∀ f ∈ fourGrp x₁ x₂, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hw.fourGrp_eq_omega.2.1.2 f hf
  have hcF : rho * b * rho⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
    have h1 := (fourGrp x₁ x₂).inv_mem hc
    have e : (b * rho * b⁻¹ * rho⁻¹)⁻¹ = rho * b * rho⁻¹ * b⁻¹ := by group
    rwa [e] at h1
  have hcb : rho * b * rho⁻¹ = (rho * b * rho⁻¹ * b⁻¹) * b := by group
  have hcc : (rho * b * rho⁻¹ * b⁻¹) * (rho * b * rho⁻¹ * b⁻¹) = 1 := hF2 _ hcF
  have hbc : b * (rho * b * rho⁻¹ * b⁻¹) = (rho * b * rho⁻¹ * b⁻¹) * b :=
    baseGrp_comm hw hb (hFB _ hcF)
  have hb2F : b ^ 2 ∈ fourGrp x₁ x₂ := by
    rw [hw.fourGrp_eq_mho]
    exact Subgroup.subset_closure ⟨b, hb, rfl⟩
  have hfix : rho * b ^ 2 = b ^ 2 * rho := by
    generalize rho * b * rho⁻¹ * b⁻¹ = c at hcb hcc hbc
    have e1 : rho * b ^ 2 * rho⁻¹ = (rho * b * rho⁻¹) ^ 2 := by rw [conj_pow]
    have e2 : (c * b) ^ 2 = b ^ 2 := by
      calc (c * b) ^ 2 = c * b * (c * b) := by rw [pow_two]
        _ = c * (b * c) * b := by group
        _ = c * (c * b) * b := by rw [hbc]
        _ = (c * c) * (b * b) := by group
        _ = b ^ 2 := by rw [hcc, one_mul, pow_two]
    have e3 : rho * b ^ 2 * rho⁻¹ = b ^ 2 := by rw [e1, hcb, e2]
    calc rho * b ^ 2 = (rho * b ^ 2 * rho⁻¹) * rho := by group
      _ = b ^ 2 * rho := by rw [e3]
  have hb21 : b ^ 2 = 1 := eq_one_of_commute_rho_of_mem_fourGrp h.toCtx0 hb2F hfix
  rw [(hw.fourGrp_eq_omega).1]
  exact Subgroup.subset_closure ⟨hb, hb21⟩

end QuotCert

section Generic

variable {G : Type} [Group G]

theorem n4_comm_mul_of_comm {p b r : G} (hp : p * r = r * p) (hu : p * ⁅b, r⁆ = ⁅b, r⁆ * p) :
    ⁅p * b, r⁆ = ⁅b, r⁆ := by
  have hpr : r * p⁻¹ * r⁻¹ = p⁻¹ := by
    have e : r * p * r⁻¹ = p := by
      calc r * p * r⁻¹ = (p * r) * r⁻¹ := by rw [hp]
        _ = p := by group
    calc r * p⁻¹ * r⁻¹ = (r * p * r⁻¹)⁻¹ := by group
      _ = p⁻¹ := by rw [e]
  have h1 : ⁅p * b, r⁆ = p * ⁅b, r⁆ * p⁻¹ := by
    calc ⁅p * b, r⁆ = p * (b * r * b⁻¹ * r⁻¹) * (r * p⁻¹ * r⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = p * ⁅b, r⁆ * p⁻¹ := by rw [hpr, commutatorElement_def]
  rw [h1]
  calc p * ⁅b, r⁆ * p⁻¹ = (⁅b, r⁆ * p) * p⁻¹ := by rw [hu]
    _ = ⁅b, r⁆ := by group

end Generic

end S4A

end CFSG.OddStandard.SmallF3.HarrisU33
