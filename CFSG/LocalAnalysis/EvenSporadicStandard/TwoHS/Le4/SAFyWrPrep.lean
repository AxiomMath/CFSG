module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem sylow_smul_mem_of_mem {G : Type*} [Group G] (p : ℕ) (P : Sylow p G) (g x : G)
    (hx : x ∈ (P : Subgroup G)) : g * x * g⁻¹ ∈ (↑(g • P) : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨x, hx, by simp [MulAut.smul_def]⟩

theorem sylow_inv_mem_of_smul_mem {G : Type*} [Group G] (p : ℕ) (P : Sylow p G) (g y : G)
    (hy : y ∈ (↑(g • P) : Subgroup G)) : g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  have : g⁻¹ * (MulAut.conj g • s) * g = s := by simp [MulAut.smul_def]; group
  rw [this]; exact hs

variable {X : Type*} [Group X] [Finite X]

theorem exists_swap_normalizing (Q : Subgroup X) {τ v x₀ : X}
    (hQτ : ∀ q ∈ Q, q * τ = τ * q) (hQv : ∀ q ∈ Q, q * v = v * q)
    (hcard : Nat.card Q = 64) (hC : Nat.card (centralizer ({τ} : Set X)) = 960)
    (hx₀ : x₀ * τ * x₀⁻¹ = v) :
    ∃ x : X, (∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, x⁻¹ * q * x ∈ Q) ∧ x * τ * x⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({τ} : Set X) with hH
  have hmemH : ∀ g : X, g * τ = τ * g → g ∈ H := by
    intro g hg
    rw [hH, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact hg.symm
  have hQH : Q ≤ H := fun q hq => hmemH q (hQτ q hq)
  set R : Subgroup X := Q.map (MulAut.conj x₀⁻¹).toMonoidHom with hR
  have hmemR : ∀ r : X, r ∈ R ↔ x₀ * r * x₀⁻¹ ∈ Q := by
    intro r
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : x₀ * ((MulAut.conj x₀⁻¹).toMonoidHom q) * x₀⁻¹ = q := by
        simp; group
      rw [this]; exact hq
    · intro h
      refine ⟨x₀ * r * x₀⁻¹, h, ?_⟩
      simp; group
  have hRH : R ≤ H := by
    intro r hr
    have hq : x₀ * r * x₀⁻¹ ∈ Q := (hmemR r).1 hr
    apply hmemH
    have h1 := hQv _ hq
    have hτ' : τ = x₀⁻¹ * v * x₀ := by rw [← hx₀]; group
    calc r * τ = x₀⁻¹ * ((x₀ * r * x₀⁻¹) * v) * x₀ := by rw [hτ']; group
      _ = x₀⁻¹ * (v * (x₀ * r * x₀⁻¹)) * x₀ := by rw [h1]
      _ = τ * r := by rw [hτ']; group
  have hcardR : Nat.card R = 64 := by
    rw [hR, Subgroup.card_map_of_injective (MulAut.conj x₀⁻¹).injective, hcard]
  set Q' : Subgroup ↥H := Q.subgroupOf H with hQ'
  set R' : Subgroup ↥H := R.subgroupOf H with hR'
  have hcardQ' : Nat.card Q' = 64 := by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hcardR' : Nat.card R' = 64 := by
    rw [← hcardR]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hidx : ∀ S : Subgroup ↥H, Nat.card S = 64 → ¬ 2 ∣ S.index := by
    intro S hS
    have h1 := Subgroup.card_mul_index S
    have hC' : Nat.card ↥H = 960 := hC
    rw [hS, hC'] at h1
    have : S.index = 15 := by omega
    rw [this]; norm_num
  have hQp : IsPGroup 2 Q' := IsPGroup.of_card (n := 6) (by rw [hcardQ']; norm_num)
  have hRp : IsPGroup 2 R' := IsPGroup.of_card (n := 6) (by rw [hcardR']; norm_num)
  let SQ : Sylow 2 ↥H := hQp.toSylow (hidx Q' hcardQ')
  let SR : Sylow 2 ↥H := hRp.toSylow (hidx R' hcardR')
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥H SR SQ
  have hSQ : ∀ q : ↥H, q ∈ (SQ : Subgroup ↥H) ↔ (q : X) ∈ Q := fun q => Iff.rfl
  have hSR : ∀ r : ↥H, r ∈ (SR : Subgroup ↥H) ↔ (r : X) ∈ R := fun r => Iff.rfl
  have hforward : ∀ r ∈ R, (c : X) * r * (c : X)⁻¹ ∈ Q := by
    intro r hr
    have h1 : (⟨r, hRH hr⟩ : ↥H) ∈ (SR : Subgroup ↥H) := (hSR _).2 hr
    have h2 := sylow_smul_mem_of_mem 2 SR c ⟨r, hRH hr⟩ h1
    rw [hc] at h2
    exact (hSQ _).1 h2
  have hbackward : ∀ q ∈ Q, (c : X)⁻¹ * q * (c : X) ∈ R := by
    intro q hq
    have h1 : (⟨q, hQH hq⟩ : ↥H) ∈ (SQ : Subgroup ↥H) := (hSQ _).2 hq
    rw [← hc] at h1
    have h2 := sylow_inv_mem_of_smul_mem 2 SR c _ h1
    exact (hSR _).1 h2
  have hcτ : (c : X) * τ = τ * (c : X) := by
    have := (mem_centralizer_iff.1 c.2) τ (Set.mem_singleton _)
    exact this.symm
  refine ⟨x₀ * (c : X)⁻¹, ?_, ?_, ?_⟩
  · intro q hq
    have h1 := (hmemR _).1 (hbackward q hq)
    have : x₀ * (c : X)⁻¹ * q * (x₀ * (c : X)⁻¹)⁻¹ = x₀ * ((c : X)⁻¹ * q * (c : X)) * x₀⁻¹ := by
      group
    rw [this]; exact h1
  · intro q hq
    have hr : x₀⁻¹ * q * x₀ ∈ R := by
      rw [hmemR]
      have : x₀ * (x₀⁻¹ * q * x₀) * x₀⁻¹ = q := by group
      rw [this]; exact hq
    have h1 := hforward _ hr
    have : (x₀ * (c : X)⁻¹)⁻¹ * q * (x₀ * (c : X)⁻¹) = (c : X) * (x₀⁻¹ * q * x₀) * (c : X)⁻¹ := by
      group
    rw [this]; exact h1
  · have : (c : X)⁻¹ * τ * (c : X) = τ := by
      calc (c : X)⁻¹ * τ * (c : X) = (c : X)⁻¹ * (τ * (c : X)) := by group
        _ = (c : X)⁻¹ * ((c : X) * τ) := by rw [hcτ]
        _ = τ := by group
    calc x₀ * (c : X)⁻¹ * τ * (x₀ * (c : X)⁻¹)⁻¹ = x₀ * ((c : X)⁻¹ * τ * (c : X)) * x₀⁻¹ := by
          group
      _ = v := by rw [this, hx₀]

end CFSG.EvenSporadicStandard.TwoHS
